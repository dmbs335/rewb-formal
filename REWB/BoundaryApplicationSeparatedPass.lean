import REWB.BoundaryApplicationSeparatedCoverage

/-! One top-down execution produces the separated target endpoint
bitset. The mutable-sized vector is threaded linearly through the two
children; only target terminals update it. Every DFA row is a finite
materialized vector and every edge map comes from the shared index. -/
namespace REWB.BoundaryApplication.Separated.Pass
open REWB.BoundaryTrie
open REWB.BoundaryIndex
variable {σ n m : Nat}

def mark (bits : Vector Bool m) (p : Fin m) (value : Bool) : Vector Bool m :=
  bits.set p.val (bits.get p || value) p.isLt

theorem mark_get (bits : Vector Bool m) (p q : Fin m) (value : Bool) :
    (mark bits p value).get q=true ↔ bits.get q=true ∨ (q=p ∧ value=true) := by
  by_cases h : q=p
  · subst q
    change (bits.set p.val (bits.get p || value) p.isLt)[p.val]=true ↔ _
    simp only [Vector.getElem_set_self,Bool.or_eq_true,true_and]
  · have hv : p.val≠q.val := by intro he; exact h (Fin.ext he.symm)
    change (bits.set p.val (bits.get p || value) p.isLt)[q.val]=true ↔ _
    simp only [Vector.getElem_set_ne p.isLt q.isLt hv,h,false_and,or_false]
    rfl

def go (A B D : DFA (Fin σ)) (cuts : RTable.Shared A B D) (dranges : Range.Index D) :
    StartSummary.Saved A.stateCount n (Endpoint m)→Nat→Vector Bool D.stateCount→
      Vector Bool (m+1)→Vector Bool (m+1)×Nat
  | .empty,_,_,bits => (bits,1)
  | .leaf key source,parent,incoming,bits =>
    match key.record with
    | .source _ => (bits,2)
    | .target target =>
      let bottom:=Cuts.advance A B D cuts dranges key.start key.length parent source incoming
      (mark bits target (bottom.row.get D.initial),bottom.work+4)
  | .node key d source l r,parent,incoming,bits =>
    let bottom:=Cuts.advance A B D cuts dranges key.start d parent source incoming
    -- Unpack the cost before the next call so the left result pair does
    -- not retain the vector while its single-owner traversal continues.
    let (leftBits,leftWork):=go A B D cuts dranges l d bottom.row bits
    let (rightBits,rightWork):=go A B D cuts dranges r d bottom.row leftBits
    (rightBits,bottom.work+leftWork+rightWork+6)

def budget (A D : DFA (Fin σ)) (n : Nat) : Nat := Cuts.budget A D n+6

theorem go_work (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (s : StartSummary.Saved A.stateCount (reversed w).size (Endpoint w.length))
    (hg : (StartSummary.shape s).Good (reverseText w fallback)) (hn : (StartSummary.shape s).leaves≠[])
    (parent : Nat) (hp : parent≤(StartSummary.shape s).depth)
    (incoming : Vector Bool D.stateCount) (bits : Vector Bool (w.length+1)) :
    (go A B D (RTable.prepare A B D w) (Range.build D w) s parent incoming bits).2≤
      (StartSummary.shape s).nodes*budget A D w.length := by
  induction s generalizing parent incoming bits with
  | empty => exact False.elim (hn rfl)
  | leaf key row =>
    have hw:=Cuts.advance_work A B D w fallback parent (StartSummary.shape (.leaf key row)) hg hn hp row incoming
    cases ht : key.record with
    | source target => simp only [go,ht,StartSummary.shape,BoundaryTrie.Tree.nodes,Nat.one_mul,budget]; omega
    | target target =>
      simp only [go,ht,StartSummary.shape,BoundaryTrie.Tree.nodes,Nat.one_mul,budget]
      exact Nat.le_trans (Nat.add_le_add_right hw 4) (by omega)
  | node key d row l r ihl ihr =>
    have hd:=BoundaryTrie.Tree.edge_depths (reverseText w fallback) key d (StartSummary.shape l) (StartSummary.shape r) hg
    let bottom:=Cuts.advance A B D (RTable.prepare A B D w) (Range.build D w) key.start d parent row incoming
    let left:=go A B D (RTable.prepare A B D w) (Range.build D w) l d bottom.row bits
    have hl:=ihl hg.1 hg.2.2.1 d hd.1 bottom.row bits
    change left.2≤_ at hl
    have hr:=ihr hg.2.1 hg.2.2.2.1 d hd.2 bottom.row left.1
    have hw:=Cuts.advance_work A B D w fallback parent (StartSummary.shape (.node key d row l r)) hg hn hp row incoming
    change bottom.work≤_ at hw
    change bottom.work+left.2+(go A B D (RTable.prepare A B D w) (Range.build D w)
      r d bottom.row left.1).2+6≤_
    simp only [StartSummary.shape,BoundaryTrie.Tree.nodes,Nat.add_mul,Nat.one_mul]
    unfold budget at *
    omega

def Target (w : Word (Fin σ)) (t : TrieFor w) (target : Fin (w.length+1)) : Prop :=
  ∃b,b∈t.leaves ∧ b.record=.target target

theorem go_correct (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h0 : g0≤w.length) (whole t : TrieFor w)
    (hv : ∀a,a∈whole.leaves→ValidKey g1 (originalKey w a))
    (hs : ∀a,a∈whole.leaves→∀p,a.record=.source p→p.val≤g0)
    (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (parent : Nat) (hp : parent≤t.depth) (hc : Coverage.Covered w fallback whole t parent)
    (incoming : Vector Bool D.stateCount) (hprev : Coverage.Previous A B C D w g0 g1 whole t parent incoming)
    (bits : Vector Bool (w.length+1)) (target : Fin (w.length+1)) :
    (go A B D (RTable.prepare A B D w) (Range.build D w)
      (Summary.build A C w g0 (Range.build A w) (Range.build C w) t).1 parent incoming bits).1.get target=true ↔
      bits.get target=true ∨ (Target w t target ∧ Coverage.Full A B C D w g0 g1 whole target) := by
  induction t generalizing parent incoming bits with
  | empty => exact False.elim (hn rfl)
  | leaf key =>
    have hmem : key∈(BoundaryTrie.Tree.leaf key).leaves := by simp only [BoundaryTrie.Tree.leaves,List.mem_singleton]
    have hrow:=Summary.build_root A C w fallback g0 g1 h0 (.leaf key) hg hn
      (fun a ha=>hv a (hc.1 a ha)) (fun a ha=>hs a (hc.1 a ha))
    cases ht : key.record with
    | source p =>
      simp only [Summary.build,ht,go,Target,BoundaryTrie.Tree.leaves,List.mem_singleton,exists_eq_left,
        reduceCtorEq,false_and,or_false]
    | target p =>
      have hstep:=Coverage.advance_hits A B C D w fallback g0 g1 whole (.leaf key) hg hv parent hp hc
        key hmem p ht _ hrow incoming hprev
      simp only [BoundaryTrie.Tree.depth] at hstep
      rw [leaf_color D w g1 key p (hv key (hc.1 key hmem)) ht,
        Coverage.leaf_full A B C D w g0 g1 whole key p (hv key (hc.1 key hmem)) ht] at hstep
      simp only [Summary.build,ht,StartSummary.root,representative,BoundaryTrie.Tree.depth] at hstep
      simp only [Summary.build,ht,go,mark_get,Target,BoundaryTrie.Tree.leaves,List.mem_singleton,
        exists_eq_left,Endpoint.target.injEq]
      constructor
      · rintro (hbits | ⟨he,hvalue⟩)
        · exact Or.inl hbits
        · subst target; exact Or.inr ⟨rfl,hstep.mp hvalue⟩
      · rintro (hbits | ⟨he,hfull⟩)
        · exact Or.inl hbits
        · subst target; exact Or.inr ⟨rfl,hstep.mpr hfull⟩
  | node key d l r ihl ihr =>
    let saved:=Summary.build A C w g0 (Range.build A w) (Range.build C w) (.node key d l r)
    let bottom:=Cuts.advance A B D (RTable.prepare A B D w) (Range.build D w)
      key.start d parent (StartSummary.root saved.1) incoming
    have hrow:=Summary.build_root A C w fallback g0 g1 h0 (.node key d l r) hg hn
      (fun a ha=>hv a (hc.1 a ha)) (fun a ha=>hs a (hc.1 a ha))
    have hstep (b : KeyFor w) (hb : b∈(BoundaryTrie.Tree.node key d l r).leaves)
        (p : Fin (w.length+1)) (ht : b.record=.target p) :
        bottom.row.get (color D w g1 p d)=true ↔ Cuts.Hits A B C D w g0 g1 whole p d :=
      Coverage.advance_hits A B C D w fallback g0 g1 whole (.node key d l r) hg hv parent hp hc
        b hb p ht _ hrow incoming hprev
    have hd:=BoundaryTrie.Tree.edge_depths (reverseText w fallback) key d l r hg
    have hcl:=Coverage.covered_left w fallback whole key d l r parent hg hp hc
    have hcr:=Coverage.covered_right w fallback whole key d l r parent hg hp hc
    have hpl : Coverage.Previous A B C D w g0 g1 whole l d bottom.row :=
      Or.inr (fun b hb p ht=>hstep b (List.mem_append_left _ hb) p ht)
    have hpr : Coverage.Previous A B C D w g0 g1 whole r d bottom.row :=
      Or.inr (fun b hb p ht=>hstep b (List.mem_append_right _ hb) p ht)
    let left:=go A B D (RTable.prepare A B D w) (Range.build D w)
      (Summary.build A C w g0 (Range.build A w) (Range.build C w) l).1 d bottom.row bits
    have hl:=ihl hg.1 hg.2.2.1 d hd.1 hcl bottom.row hpl bits
    have hr:=ihr hg.2.1 hg.2.2.2.1 d hd.2 hcr bottom.row hpr left.1
    change (go A B D (RTable.prepare A B D w) (Range.build D w)
      (Summary.build A C w g0 (Range.build A w) (Range.build C w) r).1 d bottom.row left.1).1.get target=true ↔ _
    rw [hr]
    change ((go A B D (RTable.prepare A B D w) (Range.build D w)
      (Summary.build A C w g0 (Range.build A w) (Range.build C w) l).1 d bottom.row bits).1.get target=true ∨ _) ↔ _
    rw [hl]
    simp only [Target,BoundaryTrie.Tree.leaves,List.mem_append,or_and_right,exists_or,or_and_right,or_assoc]

end REWB.BoundaryApplication.Separated.Pass
