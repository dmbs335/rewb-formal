import REWB.BoundaryApplicationStartIndex

/-! Complete fixed-start queries from a target start j to a right
boundary r. A cached ancestor search selects one compressed edge; one
joint-cut query evaluates its closed cutoff. Correctness is the actual
two-factor equality with A/B/C/E acceptance, including empty factors. -/
namespace REWB.BoundaryApplication.StartIndex
open REWB.BoundaryTrie
open REWB.BoundaryIndex
open REWB.Spec (slice)
open StartCoverage StartSound
variable {α : Type} {σ n m : Nat}

theorem go_targetDepth (B C E : DFA α) (cuts : StartCuts.Index B C E) (branges : Range.Index B)
    (cranges : Range.Index C) (eranges : Range.Index E)
    (s : StartSummary.Saved C.stateCount n (Endpoint m)) (p : Nat) (beta : Fin B.stateCount)
    (incoming : StartCuts.Row E) (j : Fin (m+1)) (limit : Nat)
    (h : ∀a,a∈(StartSummary.shape s).leaves→a.record=.target j→limit≤a.length) :
    StartLocate.TargetDepth j limit (StartPass.go B C E cuts branges cranges eranges s p beta incoming).1 := by
  induction s generalizing p beta incoming with
  | empty => intro he; cases he
  | leaf key row =>
    intro he
    have ht : key.record=.target j := by
      cases hk : key.record with
      | source i => simp only [StartPass.go,StartPass.terminal,hk] at he; cases he
      | target i =>
        have he' : some i=some j := by simpa only [hk,StartPass.terminal] using he
        have hij : i=j := Option.some.inj he'
        subst i
        rfl
    exact h key (by simp only [StartSummary.shape,BoundaryTrie.Tree.leaves,List.mem_singleton]) ht
  | node key d row l r ihl ihr =>
    exact ⟨ihl _ _ _ (fun a ha ht=>h a (List.mem_append_left _ ha) ht),
      ihr _ _ _ (fun a ha ht=>h a (List.mem_append_right _ ha) ht)⟩

theorem build_targetDepth (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (hg : g≤w.length) (j : Fin (w.length+1)) (right : Nat) (hr : right≤w.length) :
    StartLocate.TargetDepth j (right-j.val) (build A B C E w fallback g hg).paths := by
  apply go_targetDepth B C E
  intro a ha ht
  rw [StartSummary.build_shape] at ha
  have hv:=trie_valid w fallback g hg a ha
  simp only [StartKeys.ValidKey,StartKeys.originalKey,ht] at hv
  rw [hv.2.2]
  omega

theorem cut_sound (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat) (whole : StartKeys.TrieFor w)
    (t u : StartLocate.Tree (StartStep.Entry B C E) (w.length+1)) (j : Fin (w.length+1)) (limit p : Nat)
    (hc : StartLocate.CutPath j limit t u) (hs : Sound A B C E w g whole t) (hl : Linked B C E t p)
    (hp : p≤limit) : NodeSound A B C E w g whole u ∧ u.payload.parentDepth≤limit := by
  induction hc generalizing p with
  | here t _ _ => exact ⟨sound_root A B C E w g whole t hs,by rw [linked_root B C E t p hl]; exact hp⟩
  | left hd _ ih => exact ih _ hs.2.1 hl.2.1 (Nat.le_of_lt hd)
  | right hd _ ih => exact ih _ hs.2.2 hl.2.2 (Nat.le_of_lt hd)

structure Answer where
  value : Bool
  work : Nat
  locateWork : Nat

def query {A : DFA (Fin σ)} (B C E : DFA (Fin σ)) {w : Word (Fin σ)}
    (idx : Index A B C E w) (j : Fin (w.length+1)) (right : Nat) : Answer :=
  let limit:=right-j.val
  let loc:=StartLocate.query idx.levels idx.addresses j limit
  match loc.value with
  | none => ⟨false,loc.work+1,loc.work⟩
  | some found =>
    let row:=StartStep.query B C E idx.cuts idx.cranges idx.eranges found.cell.payload limit
    let accepted:=StartStep.accept E row.states
    ⟨accepted.1,loc.work+row.work+accepted.2+4,loc.work⟩

theorem located_sound (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (hg : g≤w.length) (j : Fin (w.length+1)) (hj : g≤j.val) (right : Nat) (hr : right≤w.length) :
    ∃out,(StartLocate.query (build A B C E w fallback g hg).levels
      (build A B C E w fallback g hg).addresses j (right-j.val)).value=some out ∧
      out.cell.payload.parentDepth≤right-j.val ∧ right-j.val≤out.cell.payload.depth ∧
      out.cell.payload.start+out.cell.payload.depth≤w.length ∧
      ∀q,(StartStep.query B C E (StartCuts.build B C E w) (Range.build C w) (Range.build E w)
        out.cell.payload (right-j.val)).states.get q=true ↔
          Words A B C E w g (build A B C E w fallback g hg).trie.tree j (right-j.val) (right-j.val) q := by
  let idx:=build A B C E w fallback g hg
  obtain ⟨out,u,hout,hcut,hd,he,_⟩:=StartLocate.query_located idx.levels idx.paths
    (build_good A B C E w fallback g hg) (build_capacity A B C E w fallback g hg) j
    (build_target A B C E w fallback g hg j hj) (right-j.val) (build_targetDepth A B C E w fallback g hg j right hr)
  have hs:=cut_sound A B C E w g idx.trie.tree idx.paths u j (right-j.val) 0 hcut
    (build_sound A B C E w fallback g hg) (build_linked A B C E w fallback g hg) (Nat.zero_le _)
  have hc:=StartLocate.cutPath_target j (right-j.val) idx.paths u hcut
  refine ⟨out,hout,?_,?_,?_,?_⟩
  · rw [he]; exact hs.2
  · rw [he,hs.1.1]; exact hc.2
  · rw [he]; exact hs.1.2.1
  · intro q
    rw [he]
    exact hs.1.2.2 j hc.1 (right-j.val) hs.2 hc.2 q

theorem query_words (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (hg : g≤w.length) (j : Fin (w.length+1)) (hj : g≤j.val) (right : Nat) (hr : right≤w.length) :
    (query B C E (build A B C E w fallback g hg) j right).value=true ↔
      ∃q,Words A B C E w g (build A B C E w fallback g hg).trie.tree j (right-j.val) (right-j.val) q ∧ E.final q=true := by
  obtain ⟨out,hout,_,_,_,hs⟩:=located_sound A B C E w fallback g hg j hj right hr
  simp only [query,hout]
  rw [StartStep.accept_correct]
  change (∃q,(StartStep.query B C E (StartCuts.build B C E w) (Range.build C w) (Range.build E w)
    out.cell.payload (right-j.val)).states.get q=true ∧ E.final q=true) ↔ _
  simp only [hs]

def Predicate (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat) (j : Fin (w.length+1)) (right : Nat) : Prop :=
  ∃i : Fin (w.length+1),i.val≤g ∧ ∃L,L≤g-i.val ∧ j.val+L≤right ∧
    slice w i.val (i.val+L)=slice w j.val (j.val+L) ∧
    A.accepts (slice w 0 i.val) ∧ B.accepts (slice w j.val (j.val+L)) ∧
    C.accepts (slice w (i.val+L) g) ∧ E.accepts (slice w (j.val+L) right)

theorem words_predicate (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (hg : g≤w.length) (j : Fin (w.length+1)) (right : Nat) (hj : j.val≤right) (hr : right≤w.length) :
    (∃q,Words A B C E w g (build A B C E w fallback g hg).trie.tree j (right-j.val) (right-j.val) q ∧ E.final q=true) ↔
      Predicate A B C E w g j right := by
  have hjr : j.val+(right-j.val)=right := by omega
  constructor
  · rintro ⟨q,⟨a,ha,i,ht,L,hL,hs,_,he,hA,hB,hC,hE⟩,hf⟩
    have hv:=trie_valid w fallback g hg a ha
    simp only [StartKeys.ValidKey,StartKeys.originalKey,ht] at hv
    refine ⟨i,hv.1,L,hs,by omega,he,hA,hB,hC,?_⟩
    unfold DFA.accepts
    rw [hjr] at hE
    rwa [hE]
  · rintro ⟨i,hi,L,hs,hL,he,hA,hB,hC,hE⟩
    obtain ⟨a,ha,ht⟩:=forward_source w g hg i hi
    have hm:=(BoundaryTrie.Build.run_correct w.toArray fallback (StartKeys.forwardKeys w g hg)).1.mem_iff.mpr ha
    refine ⟨E.run E.initial (slice w (j.val+L) right),?_,hE⟩
    exact ⟨a,hm,i,ht,L,by omega,hs,by omega,he,hA,hB,hC,by rw [hjr]⟩

theorem query_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (hg : g≤w.length) (j : Fin (w.length+1)) (hj : g≤j.val) (right : Nat)
    (hjr : j.val≤right) (hr : right≤w.length) :
    (query B C E (build A B C E w fallback g hg) j right).value=true ↔ Predicate A B C E w g j right :=
  (query_words A B C E w fallback g hg j hj right hr).trans
    (words_predicate A B C E w fallback g hg j right hjr hr)

theorem query_iff_cuts (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (hg : g≤w.length) (j : Fin (w.length+1)) (hj : g≤j.val) (right : Nat)
    (hjr : j.val≤right) (hr : right≤w.length) :
    (query B C E (build A B C E w fallback g hg) j right).value=true ↔
      ∃i L,i≤g ∧ L≤g-i ∧ j.val+L≤right ∧
        slice w i (i+L)=slice w j.val (j.val+L) ∧
        A.accepts (slice w 0 i) ∧ B.accepts (slice w j.val (j.val+L)) ∧
        C.accepts (slice w (i+L) g) ∧ E.accepts (slice w (j.val+L) right) := by
  rw [query_correct A B C E w fallback g hg j hj right hjr hr]
  constructor
  · rintro ⟨i,hi,L,hL,hR,he,hA,hB,hC,hE⟩
    exact ⟨i.val,L,hi,hL,hR,he,hA,hB,hC,hE⟩
  · rintro ⟨i,L,hi,hL,hR,he,hA,hB,hC,hE⟩
    exact ⟨⟨i,by omega⟩,hi,L,hL,hR,he,hA,hB,hC,hE⟩

theorem query_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (hg : g≤w.length) (j : Fin (w.length+1)) (hj : g≤j.val) (right : Nat) (hr : right≤w.length) :
    (query B C E (build A B C E w fallback g hg) j right).work≤
      6*levels w.length+StartStep.budget B C E w.length+E.stateCount+10 := by
  obtain ⟨out,hout,hp,hm,hd,_⟩:=located_sound A B C E w fallback g hg j hj right hr
  have hl:=StartLocate.query_work (build A B C E w fallback g hg).levels
    (build A B C E w fallback g hg).addresses j (right-j.val)
  have hq:=StartStep.query_work B C E w out.cell.payload (right-j.val) hp hm hd
  simp only [query,hout,StartStep.accept_work]
  change _+ (StartStep.query B C E (StartCuts.build B C E w) (Range.build C w) (Range.build E w)
    out.cell.payload (right-j.val)).work+E.stateCount+4≤_
  change _≤6*levels w.toArray.size+6 at hl
  rw [List.size_toArray] at hl
  omega

end REWB.BoundaryApplication.StartIndex
