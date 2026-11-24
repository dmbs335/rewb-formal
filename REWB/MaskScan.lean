import REWB.P1Index

/-! Materialized finite-state masks and whole-column scans.
    Each set is a list of states of a fixed DFA. Tabulation after every
    transition prevents unbounded duplicate accumulation. -/
namespace REWB.MaskScan
open FiniteRelation
open REWB.Spec (slice)
open REWB.IndexedMarked (decorate)
variable {α : Type}

abbrev Bits (d : DFA α) := List (Fin d.stateCount)

def bit (d : DFA α) (s : Bits d) (q : Fin d.stateCount) : Bool :=
  decide (q ∈ s)

def tab (d : DFA α) (f : Fin d.stateCount → Bool) : Bits d :=
  (finEnum d.stateCount).elems.filter f

theorem bit_tab_true (d : DFA α) (f : Fin d.stateCount → Bool)
    (q : Fin d.stateCount) :
    bit d (tab d f) q=true ↔ f q=true := by
  simp only [bit,tab,decide_eq_true_eq,List.mem_filter]
  exact ⟨fun h=>h.2,fun h=>⟨(finEnum d.stateCount).complete q,h⟩⟩

theorem bit_tab (d : DFA α) (f : Fin d.stateCount → Bool)
    (q : Fin d.stateCount) : bit d (tab d f) q=f q := by
  have h := bit_tab_true d f q
  cases h1 : bit d (tab d f) q <;> cases h2 : f q <;> simp_all

/-- Backward absorption for every suffix, computed by one pass. -/
def backward (d : DFA α) (terminal : Bool) : MarkedDP.MarkedWord α → List (Bits d)
  | [] => [tab d (fun q => terminal && d.final q)]
  | (c,m)::xs =>
    let rest := backward d terminal xs
    tab d (fun q => (m && d.final q) ||
      bit d (rest.headD []) (d.step q c)) :: rest

theorem backward_length (d : DFA α) (terminal : Bool) (w : MarkedDP.MarkedWord α) :
    (backward d terminal w).length=w.length+1 := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c,m⟩
    change (backward d terminal xs).length+1=xs.length+1+1
    rw [ih]

theorem backward_head (d : DFA α) (terminal : Bool) (w : MarkedDP.MarkedWord α)
    (q : Fin d.stateCount) :
    bit d ((backward d terminal w).headD []) q=MarkedDP.reachEnd d terminal w q := by
  induction w generalizing q with
  | nil =>
    change bit d (tab d (fun q => terminal && d.final q)) q=_
    rw [bit_tab]
    rfl
  | cons x xs ih =>
    rcases x with ⟨c,m⟩
    change bit d (tab d (fun q => (m && d.final q) ||
      bit d ((backward d terminal xs).headD []) (d.step q c))) q=_
    rw [bit_tab,ih]
    rfl

theorem backward_get (d : DFA α) (terminal : Bool) (w : MarkedDP.MarkedWord α)
    (i : Nat) (q : Fin d.stateCount) (hi : i≤w.length) :
    ((backward d terminal w)[i]?).map (fun s=>bit d s q) =
      some (MarkedDP.reachEnd d terminal (w.drop i) q) := by
  induction w generalizing i with
  | nil =>
    have he : i=0 := by simpa using hi
    subst i
    change some (bit d (tab d (fun q => terminal && d.final q)) q)=_
    rw [bit_tab]
    rfl
  | cons x xs ih =>
    rcases x with ⟨c,m⟩
    cases i with
    | zero =>
      change some (bit d (tab d (fun q => (m && d.final q) ||
        bit d ((backward d terminal xs).headD []) (d.step q c))) q)=_
      rw [bit_tab,backward_head]
      rfl
    | succ i =>
      have hh : i≤xs.length := by simpa using hi
      exact ih i hh

theorem reachEnd_indices (d : DFA α) (m : Nat→Bool) (w : Word α)
    (l r : Nat) (q : Fin d.stateCount) (hl : l≤r) (hr : r≤w.length) :
    MarkedDP.reachEnd d (m r) (decorate m l (slice w l r)) q=true ↔
      ∃ e, l≤e ∧ e≤r ∧ m e=true ∧ d.final (d.run q (slice w l e))=true := by
  rw [MarkedDP.reachEnd_correct]
  constructor
  · rintro ⟨u,v,he,hm,hq⟩
    obtain ⟨e,hle,her,hu,hv⟩ := (P1Index.decorate_split m w l r hl hr u v).mp he
    subst u
    subst v
    rw [P1Index.boundary_mark m w e r her hr] at hm
    rw [IndexedMarked.decorate_text] at hq
    exact ⟨e,hle,her,hm,hq⟩
  · rintro ⟨e,hle,her,hm,hq⟩
    refine ⟨decorate m l (slice w l e),decorate m e (slice w e r),
      (P1Index.decorate_join m w l e r hle her hr).symm,?_,?_⟩
    · rw [P1Index.boundary_mark m w e r her hr]
      exact hm
    · rw [IndexedMarked.decorate_text]
      exact hq

private theorem take_length (w : List α) : w.take w.length=w := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
    change c::cs.take cs.length=c::cs
    rw [ih]

theorem slice_to_end (w : Word α) (t : Nat) (ht : t≤w.length) :
    slice w t w.length=w.drop t := by
  unfold slice
  rw [← List.length_drop,take_length]

def readyRow (P : SevenDFA α) (w : Word α) (outer : Nat→Bool) : Array (Bits P.F) :=
  (backward P.F (outer w.length) (decorate outer 0 w)).toArray

def rowBit (d : DFA α) (row : Array (Bits d)) (i : Nat) (q : Fin d.stateCount) : Bool :=
  bit d (row[i]?.getD []) q

theorem readyRow_correct (P : SevenDFA α) (w : Word α) (p t : Nat)
    (outer : Nat→Bool) (ht : t≤w.length)
    (ho : ∀ e, e≤w.length → (outer e=true ↔ NestedColumns.Outer P w p e))
    (q : Fin P.F.stateCount) :
    rowBit P.F (readyRow P w outer) t q=true ↔
      NestedColumns.ReadyState P w p t q := by
  have h := backward_get P.F (outer w.length) (decorate outer 0 w) t q
    (by simpa only [IndexedMarked.decorate_length] using ht)
  have he : rowBit P.F (readyRow P w outer) t q =
      MarkedDP.reachEnd P.F (outer w.length) (decorate outer t (slice w t w.length)) q := by
    unfold rowBit readyRow
    rw [List.getElem?_toArray]
    rw [IndexedMarked.decorate_drop,Nat.zero_add,← slice_to_end w t ht] at h
    cases hx : (backward P.F (outer w.length) (decorate outer 0 w))[t]? with
    | none => simp [hx] at h
    | some s =>
      simpa only [hx,Option.map,Option.getD,Option.some.injEq] using h
  rw [he,reachEnd_indices P.F outer w t w.length q ht (Nat.le_refl _)]
  constructor
  · rintro ⟨e,hte,hen,hm,hq⟩
    exact ⟨e,hte,(ho e hen).mp hm,hq⟩
  · rintro ⟨e,hte,⟨f,hf⟩,hq⟩
    have hef := hf.2.1
    have hfn := hf.2.2.1
    have hen : e≤w.length := by omega
    exact ⟨e,hte,hen,(ho e hen).mpr ⟨f,hf⟩,hq⟩

/-- State advance with fresh seeds at the next boundary. -/
def forwardStep (d : DFA α) (c : α) (prev seed : Bits d) : Bits d :=
  tab d (fun q => bit d seed q || prev.any (fun r => decide (d.step r c=q)))

theorem forwardStep_true (d : DFA α) (c : α) (prev seed : Bits d)
    (q : Fin d.stateCount) :
    bit d (forwardStep d c prev seed) q=true ↔
      bit d seed q=true ∨ ∃ r, bit d prev r=true ∧ d.step r c=q := by
  unfold forwardStep
  rw [bit_tab]
  simp only [Bool.or_eq_true,List.any_eq_true,bit,decide_eq_true_eq]

/-- The supplied seed array/function is read only at the current boundary.
    Every emitted active set is materialized. -/
def forwardFrom (d : DFA α) (seed : Nat→Bits d) :
    Nat→Bits d→Word α→List (Bits d)
  | _, active, [] => [active]
  | off, active, c::cs =>
    active :: forwardFrom d seed (off+1) (forwardStep d c active (seed (off+1))) cs

def forward (d : DFA α) (w : Word α) (seed : Nat→Bits d) : Array (Bits d) :=
  (forwardFrom d seed 0 (seed 0) w).toArray

theorem forwardFrom_get (d : DFA α) (seed : Nat→Bits d) (w pre rest : Word α)
    (hw : w=pre++rest) (active : Bits d)
    (ha : ∀ q, bit d active q=true ↔
      OuterColumn.Active d w (fun i r=>bit d (seed i) r=true) pre.length q)
    (i : Nat) (hi : i≤rest.length) (q : Fin d.stateCount) :
    (((forwardFrom d seed pre.length active rest)[i]?).map
      (fun s=>bit d s q) = some true) ↔
      OuterColumn.Active d w (fun j r=>bit d (seed j) r=true) (pre.length+i) q := by
  induction rest generalizing pre active i with
  | nil =>
    have hz : i=0 := by simpa using hi
    subst i
    simpa only [forwardFrom,List.getElem?_cons_zero,Option.map,Option.some.injEq,Nat.add_zero] using ha q
  | cons c cs ih =>
    cases i with
    | zero =>
      simpa only [forwardFrom,List.getElem?_cons_zero,Option.map,Option.some.injEq,Nat.add_zero] using ha q
    | succ i =>
      have hh : i≤cs.length := by simpa using hi
      let next := forwardStep d c active (seed (pre.length+1))
      let pp := pre++[c]
      have hplen : pp.length=pre.length+1 := by simp [pp]
      have hwp : w=pp++cs := by
        rw [hw]; simp [pp,List.append_assoc]
      have hchar : slice w pre.length (pre.length+1)=[c] :=
        NestedColumns.slice_at w pre [c] cs pre.length (pre.length+1)
          (by simpa only [List.append_assoc,List.singleton_append] using hw) rfl rfl
      have hnext : ∀ r, bit d next r=true ↔
          OuterColumn.Active d w (fun j s=>bit d (seed j) s=true) pp.length r := by
        intro r
        rw [hplen,OuterColumn.active_succ,hchar]
        change bit d (forwardStep d c active (seed (pre.length+1))) r=true ↔ _
        rw [forwardStep_true]
        constructor
        · rintro (hs | ⟨v,hv,he⟩)
          · exact Or.inl hs
          · exact Or.inr ⟨v,(ha v).mp hv,he⟩
        · rintro (hs | ⟨v,hv,he⟩)
          · exact Or.inl hs
          · exact Or.inr ⟨v,(ha v).mpr hv,he⟩
      have h := ih pp hwp next hnext i hh
      rw [hplen] at h
      change (((forwardFrom d seed (pre.length+1) next cs)[i]?).map
        (fun s=>bit d s q)=some true) ↔ _
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using h

theorem forward_correct (d : DFA α) (w : Word α) (seed : Nat→Bits d)
    (i : Nat) (hi : i≤w.length) (q : Fin d.stateCount) :
    rowBit d (forward d w seed) i q=true ↔
      OuterColumn.Active d w (fun j r=>bit d (seed j) r=true) i q := by
  have h := forwardFrom_get d seed w [] w rfl (seed 0)
    (fun r=>(OuterColumn.active_zero d w (fun j r=>bit d (seed j) r=true) r).symm)
    i hi q
  simp only [List.length_nil,Nat.zero_add] at h
  unfold rowBit forward
  rw [List.getElem?_toArray]
  cases he : (forwardFrom d seed 0 (seed 0) w)[i]? with
  | none =>
    simp only [he,Option.map,reduceCtorEq,false_iff] at h
    simp only [bit,decide_eq_true_eq] at h
    simp [he,bit,h]
  | some s =>
    simpa only [he,Option.map,Option.getD,Option.some.injEq] using h

def prefixStates (d : DFA α) (q : Fin d.stateCount) : Word α→List (Fin d.stateCount)
  | [] => [q]
  | c::cs => q::prefixStates d (d.step q c) cs

theorem prefixStates_get (d : DFA α) (w : Word α) (i : Nat) (hi : i≤w.length)
    (q : Fin d.stateCount) :
    (prefixStates d q w)[i]?=some (d.run q (w.take i)) := by
  induction w generalizing i q with
  | nil =>
    have hz : i=0 := by simpa using hi
    subst i
    rfl
  | cons c cs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hh : i≤cs.length := by simpa using hi
      exact ih i hh (d.step q c)

def prefixMask (d : DFA α) (w : Word α) : Nat→Bool :=
  let arr := (prefixStates d d.initial w).toArray
  fun i => (arr[i]?.map d.final).getD false

theorem prefixMask_correct (d : DFA α) (w : Word α) (i : Nat) (hi : i≤w.length) :
    prefixMask d w i=true ↔ d.accepts (slice w 0 i) := by
  unfold prefixMask
  rw [List.getElem?_toArray,prefixStates_get d w i hi d.initial]
  rfl

def firstSeed (P : SevenDFA α) (w : Word α) (ready : Nat→Bool) :
    Nat→Bits P.B :=
  let pref := prefixMask P.A w
  fun p => if ready p && pref p then [P.B.initial] else []

theorem firstSeed_correct (P : SevenDFA α) (w : Word α) (t p : Nat)
    (ready : Nat→Bool) (hp : p≤w.length)
    (hr : ∀ i, i≤w.length → (ready i=true ↔ NestedColumns.Ready P w i t))
    (q : Fin P.B.stateCount) :
    bit P.B (firstSeed P w ready p) q=true ↔
      NestedColumns.Ready P w p t ∧ P.A.accepts (slice w 0 p) ∧ q=P.B.initial := by
  have h1 := hr p hp
  have h2 := prefixMask_correct P.A w p hp
  unfold firstSeed
  cases hready : ready p <;> cases hprefix : prefixMask P.A w p <;>
    simp_all [bit]

def first2Row (P : SevenDFA α) (w : Word α) (ready : Nat→Bool) :
    Array (Bits P.B) :=
  forward P.B w (firstSeed P w ready)

def accepted (d : DFA α) (row : Array (Bits d)) (i : Nat) : Bool :=
  any (finEnum d.stateCount) (fun q => rowBit d row i q && d.final q)

theorem first2Row_correct (P : SevenDFA α) (w : Word α) (t i : Nat)
    (ready : Nat→Bool) (hi : i≤w.length)
    (hr : ∀ p, p≤w.length → (ready p=true ↔ NestedColumns.Ready P w p t)) :
    accepted P.B (first2Row P w ready) i=true ↔ NestedColumns.First2 P w i t := by
  rw [NestedColumns.first2_active]
  simp only [accepted,any_true,Bool.and_eq_true,first2Row,forward_correct P.B w _ i hi]
  constructor
  · rintro ⟨q,⟨p,q0,hpi,hs,he⟩,hf⟩
    exact ⟨q,⟨p,q0,hpi,(firstSeed_correct P w t p ready (by omega) hr q0).mp hs,he⟩,hf⟩
  · rintro ⟨q,⟨p,q0,hpi,hs,he⟩,hf⟩
    exact ⟨q,⟨p,q0,hpi,(firstSeed_correct P w t p ready (by omega) hr q0).mpr hs,he⟩,hf⟩

end REWB.MaskScan
