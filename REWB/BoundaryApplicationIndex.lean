import REWB.BoundaryApplicationVersions

/-! The fixed-end color index entry point constructs its descriptors,
compressed trie, shared D range maps, static E text cells, mixed program,
and all persistent local versions. No tree or merge program is supplied
by the caller. The counters combine the stated primitive conventions of
those executable components. -/
namespace REWB.BoundaryApplication.FixedEnd
open REWB.BoundaryTrie
variable {σ : Nat}

def trie (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :=
  BoundaryTrie.Build.run (reversed w) fallback (reverseKeys w g hg)

theorem trie_good (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    (trie w fallback g hg).tree.Good (reverseText w fallback) :=
  (BoundaryTrie.Build.run_correct (reversed w) fallback (reverseKeys w g hg)).2.1

theorem trie_length (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    (trie w fallback g hg).tree.leaves.length=w.length+2 := by
  have hh:=(BoundaryTrie.Build.run_correct (reversed w) fallback (reverseKeys w g hg)).1.length_eq
  exact hh.trans (reverseKeys_length w g hg)

theorem trie_nonempty (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    (trie w fallback g hg).tree.leaves≠[] := by
  intro he
  have hh:=trie_length w fallback g hg
  rw [he,List.length_nil] at hh
  omega

theorem trie_valid (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length)
    (a : KeyFor w) (ha : a∈(trie w fallback g hg).tree.leaves) : ValidKey g (originalKey w a) :=
  reverseKeys_valid w g hg a
    ((BoundaryTrie.Build.run_correct (reversed w) fallback (reverseKeys w g hg)).1.mem_iff.mp ha)

theorem trie_nodes (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    (trie w fallback g hg).tree.nodes≤2*(w.length+2) := by
  have hh:=(BoundaryTrie.Build.run_correct (reversed w) fallback (reverseKeys w g hg)).2.2.1
  simpa only [reverseKeys_length] using hh

theorem trie_record (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length)
    (a : Key w.length (Endpoint w.length)) (ha : a∈keys w.length g hg) :
    ∃b,b∈(trie w fallback g hg).tree.leaves ∧ b.record=a.record ∧ b.length=a.length := by
  let b : KeyFor w:=⟨a.start,a.length,by have hh:=a.bounded; have hn:=reversed_size w; omega,a.record⟩
  refine ⟨b,?_,rfl,rfl⟩
  apply (BoundaryTrie.Build.run_correct (reversed w) fallback (reverseKeys w g hg)).1.mem_iff.mpr
  exact List.mem_map.mpr ⟨a,ha,rfl⟩

theorem trie_target (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length)
    (t : Fin (w.length+1)) (ht : g≤t.val) :
    ∃a,a∈(trie w fallback g hg).tree.leaves ∧ a.record=.target t := by
  obtain ⟨a,ha,hr⟩:=target_mem w.length g hg t ht
  obtain ⟨b,hb,hbr,_⟩:=trie_record w fallback g hg a ha
  exact ⟨b,hb,hbr.trans hr⟩

theorem trie_source (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length)
    (s : Fin (w.length+1)) (hs : s.val≤g) :
    ∃a,a∈(trie w fallback g hg).tree.leaves ∧ a.record=.source s := by
  obtain ⟨a,ha,hr⟩:=source_mem w.length g hg s hs
  obtain ⟨b,hb,hbr,_⟩:=trie_record w fallback g hg a ha
  exact ⟨b,hb,hbr.trans hr⟩

theorem trie_depth_zero (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    (trie w fallback g hg).tree.depth=0 := by
  obtain ⟨a,ha,hr⟩:=trie_source w fallback g hg 0 (Nat.zero_le _)
  have hv:=trie_valid w fallback g hg a ha
  simp only [ValidKey,originalKey] at hv
  rw [hr] at hv
  have hc:=BoundaryTrie.Tree.depth_common (reverseText w fallback) _ (trie_good w fallback g hg) a a ha ha
  have hh:=hc.1
  rw [hv.2.2] at hh
  exact Nat.eq_zero_of_le_zero hh

/-- Cell 0 is the boundary before the first letter. Cell t+1 contains
the transition for w[t], so a seed at cell t is after the preceding
letter. Querying through cell r reads the suffix w[t:r]. -/
def rows (E : DFA (Fin σ)) (w : Word (Fin σ)) : Array (Range.Map E.stateCount) :=
  (Range.one E.stateCount::Range.letters E w).toArray

theorem rows_size (E : DFA (Fin σ)) (w : Word (Fin σ)) : (rows E w).size=w.length+1 := by
  simp only [rows,List.size_toArray,List.length_cons,Range.letters,List.length_map]

theorem rows_zero (E : DFA (Fin σ)) (w : Word (Fin σ)) :
    (rows E w)[0]?=some (Range.one E.stateCount) := by
  simp only [rows,List.getElem?_toArray,List.getElem?_cons_zero]

theorem rows_succ (E : DFA (Fin σ)) (w : Word (Fin σ)) (i : Nat) (hi : i<w.length) :
    (rows E w)[i+1]?=some (Range.letter E w[i]) := by
  simp only [rows,List.getElem?_toArray,List.getElem?_cons_succ,Range.letters,List.getElem?_map,
    List.getElem?_eq_getElem hi,Option.map]

structure Index (D E : DFA (Fin σ)) (w : Word (Fin σ)) where
  trie : BoundaryTrie.Build.Index (reversed w).size (Endpoint w.length)
  ranges : Range.Index D
  program : BoundaryIndex.Mixed.Program D.stateCount E.stateCount (height w.length)
  versions : Versions.Snapshot D.stateCount E.stateCount (height w.length)
  work : Nat

/-- Input materialization and the source/target record/vector cells.
The full rank/trie, map-product, and persistent operations are accumulated
from the measured results separately below. -/
def inputWork (n m : Nat) : Nat := 3*n+8*(n+2)+(n+1)*m+4

def build (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) : Index D E w :=
  let t:=trie w fallback g hg
  let r:=Range.build D w
  let c:=compile D E w r t.tree
  let base:=BoundaryIndex.MergeBuild.prepare (k:=D.stateCount) (rows E w) (height w.length)
  let versions:=Versions.execute base.1 c.1
  ⟨t,r,c.1,versions,t.work+r.products*D.stateCount+r.letterCells+c.2+base.2+
    Versions.work versions+inputWork w.length E.stateCount⟩

theorem build_mass (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) :
    (Versions.root (build D E w fallback g hg).versions).totalMass=w.length+2 := by
  simp only [build,Versions.execute_root,BoundaryIndex.Mixed.execute_mass]
  rw [compile_mass D E w fallback _ _ (trie_good w fallback g hg) (trie_nonempty w fallback g hg),
    trie_length]

theorem build_active (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length)
    (i : BoundaryIndex.Merge.Position (height w.length)) (c : Fin D.stateCount) (q : Fin E.stateCount) :
    (BoundaryIndex.Merge.point (Versions.root (build D E w fallback g hg).versions).state.tree i).active c q=true ↔
      Target D E w g (trie w fallback g hg).tree i c q := by
  simp only [build,Versions.execute_root]
  rw [BoundaryIndex.Mixed.execute_active _ (BoundaryIndex.MergeBuild.prepare_good _ _)
    (BoundaryIndex.MergeBuild.prepare_blank _ _)]
  exact compile_active D E w fallback g _ (trie_good w fallback g hg) (trie_nonempty w fallback g hg)
    (trie_valid w fallback g hg) i c q

theorem build_version_active (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (u : TrieFor w) (path : List Bool)
    (hs : subtree (trie w fallback g hg).tree path=some u)
    (i : BoundaryIndex.Merge.Position (height w.length)) (c : Fin D.stateCount) (q : Fin E.stateCount) :
    ∃s,Versions.get (build D E w fallback g hg).versions path=some s ∧
      ((BoundaryIndex.Merge.point (Versions.root s).state.tree i).active c q=true ↔ Target D E w g u i c q) :=
  version_active D E w fallback g _ u path _ (BoundaryIndex.MergeBuild.prepare_good _ _)
    (BoundaryIndex.MergeBuild.prepare_blank _ _) (trie_good w fallback g hg) (trie_nonempty w fallback g hg)
    (trie_valid w fallback g hg) hs i c q

theorem build_trans (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (i : BoundaryIndex.Merge.Position (height w.length)) :
    (BoundaryIndex.Merge.point (Versions.root (build D E w fallback g hg).versions).state.tree i).trans=
      ((rows E w)[i.val]?.getD (Vector.ofFn id)).get := by
  simp only [build,Versions.execute_root]
  rw [BoundaryIndex.Mixed.execute_trans,BoundaryIndex.MergeBuild.prepare_trans]

theorem build_transfers (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) :
    (Versions.root (build D E w fallback g hg).versions).transfers≤
      (w.length+2)*(w.length+2).log2 := by
  simp only [build,Versions.execute_root]
  have hh:=BoundaryIndex.Mixed.transfers_bound
    (BoundaryIndex.MergeBuild.prepare (k:=D.stateCount) (rows E w) (height w.length)).1
    (compile D E w (Range.build D w) (trie w fallback g hg).tree).1
  rw [compile_mass D E w fallback _ _ (trie_good w fallback g hg) (trie_nonempty w fallback g hg),
    trie_length] at hh
  exact hh

def trieBound (σ n : Nat) : Nat :=
  (n+1)*((n.log2+1)*(16*RankIndex.width σ n+4)+1)+
  (13*(n.log2+1)+12)*(8*(n+2)*((n+2).log2+1))+(n+2)+2+
    2*(n+2)*BoundaryTrie.Build.budget n (n+2)

def executionBound (k m n : Nat) : Nat :=
  (n+2)*(BoundaryIndex.Mixed.seedBudget k m (height n)+BoundaryIndex.Mixed.nodeBudget k m)+
    ((n+2)*(n+2).log2)*BoundaryIndex.Merge.importBudget k m (height n)+8*(n+2)

def bound (σ k m n : Nat) : Nat :=
  trieBound σ n+((n.log2+1)*n)*k+n*k+
    2*(n+2)*(2*(k+8*(n.log2+2)+1)+5)+
    ((n+1)*(k*m+1)+2*(n+2)*(BoundaryIndex.Tree.joinBudget k m+BoundaryIndex.Tree.leafBudget k m))+
    executionBound k m n+inputWork n m

theorem build_work (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) :
    (build D E w fallback g hg).work≤bound σ D.stateCount E.stateCount w.length := by
  let t:=trie w fallback g hg
  let c:=compile D E w (Range.build D w) t.tree
  let base:=BoundaryIndex.MergeBuild.prepare (k:=D.stateCount) (rows E w) (height w.length)
  have ht : t.work≤trieBound σ w.length := by
    have hh:=BoundaryTrie.Build.run_work (reversed w) fallback (reverseKeys w g hg)
    simpa only [reversed_size,reverseKeys_length,trieBound] using hh
  have hc:=compile_work D E w fallback t.tree (trie_good w fallback g hg) (trie_nonempty w fallback g hg)
  have hcn:=Nat.mul_le_mul_right (2*(D.stateCount+8*(w.length.log2+2)+1)+5)
    (trie_nodes w fallback g hg)
  have hcomp : c.2≤2*(w.length+2)*(2*(D.stateCount+8*(w.length.log2+2)+1)+5) := Nat.le_trans hc hcn
  have hb:=BoundaryIndex.MergeBuild.prepare_steps (k:=D.stateCount) (rows E w) (height w.length)
  have hcap:=Nat.mul_le_mul_right
    (BoundaryIndex.Tree.joinBudget D.stateCount E.stateCount+BoundaryIndex.Tree.leafBudget D.stateCount E.stateCount)
    (BoundaryIndex.Tree.capacity_upper (w.length+1))
  rw [show w.length+1+1=w.length+2 by omega] at hcap
  rw [rows_size] at hb
  have hbase : base.2≤(w.length+1)*(D.stateCount*E.stateCount+1)+2*(w.length+2)*
      (BoundaryIndex.Tree.joinBudget D.stateCount E.stateCount+BoundaryIndex.Tree.leafBudget D.stateCount E.stateCount) := by
    change base.2+_=_ at hb
    change 2^(height w.length)*_≤_ at hcap
    omega
  have hm : MaskedEventBudget.size (BoundaryIndex.Mixed.shape c.1)=w.length+2 := by
    rw [compile_mass D E w fallback _ _ (trie_good w fallback g hg) (trie_nonempty w fallback g hg),trie_length]
  have hs:=BoundaryIndex.Mixed.execute_bound base.1 c.1
  have ha:=Versions.execute_allocated base.1 c.1
  rw [hm] at hs ha
  have hv : Versions.work (Versions.execute base.1 c.1)≤executionBound D.stateCount E.stateCount w.length := by
    simp only [Versions.work,Versions.execute_root,executionBound]
    omega
  change t.work+(Range.build D w).products*D.stateCount+(Range.build D w).letterCells+c.2+base.2+
    Versions.work (Versions.execute base.1 c.1)+inputWork w.length E.stateCount≤_
  rw [Range.build_products]
  change t.work+((w.length.log2+1)*w.length)*D.stateCount+w.length*D.stateCount+c.2+base.2+
    Versions.work (Versions.execute base.1 c.1)+inputWork w.length E.stateCount≤_
  unfold bound
  omega

end REWB.BoundaryApplication.FixedEnd
