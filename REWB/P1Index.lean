import REWB.OrderedExit

/-! P1 uses two products separated by the fixed position z=t-d.
    Before z only C-to-D is possible. After z the A state is tracked
    alongside C/D, and an accepting D/A pair may enter B. The Ready
    mask is shared by both indices; it does not depend on the pair (a,t)
    except through the column t. -/
namespace REWB.P1Index
open FiniteRelation
open REWB.Spec (slice)
open REWB.MarkedDP (MarkedWord)
open REWB.IndexedMarked (decorate)
variable {α : Type}

abbrev CD (P : SevenDFA α) := MarkedTransfer.Phase P.C P.D
abbrev Left (P : SevenDFA α) := CD P × Fin P.A.stateCount

def cdEnum (P : SevenDFA α) : Enumeration (CD P) :=
  MarkedTransfer.enum P.C P.D

def rightMachine (P : SevenDFA α) : OrderedExit.Machine (Left P) α :=
  ⟨TensorRelation.pairEnum (cdEnum P) (finEnum P.A.stateCount),
    fun x => TensorRelation.tensor (MarkedTransfer.letter P.C P.D x)
      (fun q => P.A.step q x.1),
    fun m s => P.A.final s.2 &&
      pre (cdEnum P) (MarkedTransfer.epsilon P.C P.D m)
        (MarkedTransfer.final P.C P.D) s.1,
    P.B⟩

theorem left_product (P : SevenDFA α) (w : MarkedWord α) :
    (rightMachine P).leftProduct w =
      TensorRelation.tensor (MarkedTransfer.transfer P.C P.D w)
        (fun q => P.A.run q (MarkedDP.text w)) := by
  induction w with
  | nil =>
    change ident = TensorRelation.tensor ident (id : Fin P.A.stateCount → Fin P.A.stateCount)
    exact TensorRelation.tensor_ident.symm
  | cons x xs ih =>
    rw [OrderedExit.leftProduct_cons,ih]
    change comp (TensorRelation.pairEnum (cdEnum P) (finEnum P.A.stateCount))
      (TensorRelation.tensor (MarkedTransfer.letter P.C P.D x) (fun q => P.A.step q x.1))
      (TensorRelation.tensor (MarkedTransfer.transfer P.C P.D xs)
        (fun q => P.A.run q (MarkedDP.text xs))) = _
    rw [TensorRelation.tensor_comp]
    rfl

private theorem pre_guard {S : Type} (e : Enumeration S) (r : Rel S)
    (b : Bool) (v : S → Bool) (p : S) :
    pre e r (fun q => b && v q) p = true ↔ b=true ∧ pre e r v p=true := by
  simp only [pre_true,Bool.and_eq_true]
  constructor
  · rintro ⟨q,hq,hb,hv⟩
    exact ⟨hb,q,hq,hv⟩
  · rintro ⟨hb,q,hq,hv⟩
    exact ⟨q,hq,hb,hv⟩

/-- The second product may exit at j exactly when A accepts the
    prefix up to j and the C-to-D path has reached a final D state. -/
theorem right_spec (P : SevenDFA α) (terminal : Bool) (w : MarkedWord α)
    (s : CD P) (qa : Fin P.A.stateCount) :
    (rightMachine P).run terminal w (.inl (s,qa))=true ↔
      ∃ x y, w=x++y ∧
        P.A.final (P.A.run qa (MarkedDP.text x))=true ∧
        MarkedTransfer.run P.C P.D (MarkedDP.markAtHead terminal y) x s=true ∧
        P.B.accepts (MarkedDP.text y) := by
  rw [OrderedExit.run_left]
  constructor
  · rintro ⟨x,y,he,hg,hb⟩
    rw [left_product] at hg
    change pre (TensorRelation.pairEnum (cdEnum P) (finEnum P.A.stateCount))
      (TensorRelation.tensor (MarkedTransfer.transfer P.C P.D x)
        (fun q => P.A.run q (MarkedDP.text x))) _ (s,qa)=true at hg
    rw [TensorRelation.pre_tensor] at hg
    change pre (cdEnum P) (MarkedTransfer.transfer P.C P.D x)
      (fun r => P.A.final (P.A.run qa (MarkedDP.text x)) &&
        pre (cdEnum P) (MarkedTransfer.epsilon P.C P.D (MarkedDP.markAtHead terminal y))
          (MarkedTransfer.final P.C P.D) r) s=true at hg
    rw [pre_guard] at hg
    exact ⟨x,y,he,hg.1,hg.2,hb⟩
  · rintro ⟨x,y,he,ha,hcd,hb⟩
    refine ⟨x,y,he,?_,hb⟩
    rw [left_product]
    change pre (TensorRelation.pairEnum (cdEnum P) (finEnum P.A.stateCount))
      (TensorRelation.tensor (MarkedTransfer.transfer P.C P.D x)
        (fun q => P.A.run q (MarkedDP.text x))) _ (s,qa)=true
    rw [TensorRelation.pre_tensor]
    change pre (cdEnum P) (MarkedTransfer.transfer P.C P.D x)
      (fun r => P.A.final (P.A.run qa (MarkedDP.text x)) &&
        pre (cdEnum P) (MarkedTransfer.epsilon P.C P.D (MarkedDP.markAtHead terminal y))
          (MarkedTransfer.final P.C P.D) r) s=true
    exact (pre_guard _ _ _ _ _).mpr ⟨ha,hcd⟩

def whole (P : SevenDFA α) (terminal : Bool) (x y : MarkedWord α)
    (qa : Fin P.A.stateCount) : Bool :=
  pre (cdEnum P) (MarkedTransfer.transfer P.C P.D x)
    (fun s => (rightMachine P).run terminal y (.inl (s,qa))) (.inl P.C.initial)

theorem cd_append_run (P : SevenDFA α) (terminal : Bool) (x y : MarkedWord α)
    (q : CD P) :
    MarkedTransfer.run P.C P.D terminal (x++y) q =
      pre (cdEnum P) (MarkedTransfer.transfer P.C P.D x)
        (fun s => MarkedTransfer.run P.C P.D terminal y s) q := by
  unfold MarkedTransfer.run
  rw [MarkedTransfer.transfer_append,pre_comp]
  rfl

theorem whole_spec (P : SevenDFA α) (terminal : Bool) (x y : MarkedWord α)
    (qa : Fin P.A.stateCount) :
    whole P terminal x y qa=true ↔
      ∃ u v, y=u++v ∧
        P.A.final (P.A.run qa (MarkedDP.text u))=true ∧
        MarkedTransfer.run P.C P.D (MarkedDP.markAtHead terminal v) (x++u)
          (.inl P.C.initial)=true ∧
        P.B.accepts (MarkedDP.text v) := by
  unfold whole
  rw [pre_true]
  constructor
  · rintro ⟨s,hs,hr⟩
    obtain ⟨u,v,he,ha,hcd,hb⟩ := (right_spec P terminal y s qa).mp hr
    refine ⟨u,v,he,ha,?_,hb⟩
    rw [cd_append_run,pre_true]
    exact ⟨s,hs,hcd⟩
  · rintro ⟨u,v,he,ha,hcd,hb⟩
    rw [cd_append_run,pre_true] at hcd
    obtain ⟨s,hs,hcd⟩ := hcd
    exact ⟨s,hs,(right_spec P terminal y s qa).mpr ⟨u,v,he,ha,hcd,hb⟩⟩

private theorem take_prefix {X : Type} (x y : List X) :
    (x++y).take x.length=x := by
  induction x with
  | nil => rfl
  | cons c cs ih =>
    change c::(cs++y).take cs.length=c::cs
    rw [ih]

private theorem drop_prefix {X : Type} (x y : List X) :
    (x++y).drop x.length=y := by
  induction x with
  | nil => rfl
  | cons c cs ih => exact ih

theorem decorate_join (m : Nat → Bool) (w : Word α) (a z j : Nat)
    (haz : a≤z) (hzj : z≤j) (hj : j≤w.length) :
    decorate m a (slice w a z) ++ decorate m z (slice w z j) =
      decorate m a (slice w a j) := by
  have hlen := OuterColumn.slice_length w a z haz (by omega)
  have he : a+(slice w a z).length=z := by omega
  rw [OuterColumn.slice_split w a z j haz hzj,IndexedMarked.decorate_append,he]

/-- A split of decorated text has the same absolute boundary as its
    undecorated text. -/
theorem decorate_split (m : Nat → Bool) (w : Word α) (z t : Nat)
    (hzt : z≤t) (ht : t≤w.length) (u v : MarkedWord α) :
    decorate m z (slice w z t)=u++v ↔
      ∃ j, z≤j ∧ j≤t ∧
        u=decorate m z (slice w z j) ∧ v=decorate m j (slice w j t) := by
  constructor
  · intro he
    have hlen := congrArg List.length he
    rw [IndexedMarked.decorate_length,List.length_append,
      OuterColumn.slice_length w z t hzt ht] at hlen
    let j := z+u.length
    have hzj : z≤j := by dsimp [j]; omega
    have hjt : j≤t := by dsimp [j]; omega
    have hsplit := decorate_join m w z j t hzj hjt ht
    have hsize : (decorate m z (slice w z j)).length=u.length := by
      rw [IndexedMarked.decorate_length,OuterColumn.slice_length w z j hzj (by omega)]
      dsimp [j]; omega
    have hboth : u++v = decorate m z (slice w z j) ++ decorate m j (slice w j t) :=
      he.symm.trans hsplit.symm
    have hp := congrArg (List.take u.length) hboth
    change (u++v).take u.length =
      (decorate m z (slice w z j) ++ decorate m j (slice w j t)).take u.length at hp
    rw [take_prefix] at hp
    rw [← hsize,take_prefix] at hp
    have hs := congrArg (List.drop u.length) hboth
    change (u++v).drop u.length =
      (decorate m z (slice w z j) ++ decorate m j (slice w j t)).drop u.length at hs
    rw [drop_prefix] at hs
    rw [← hsize,drop_prefix] at hs
    exact ⟨j,hzj,hjt,hp,hs⟩
  · rintro ⟨j,hzj,hjt,rfl,rfl⟩
    exact (decorate_join m w z j t hzj hjt ht).symm

theorem boundary_mark (m : Nat → Bool) (w : Word α) (j t : Nat)
    (hjt : j≤t) (ht : t≤w.length) :
    MarkedDP.markAtHead (m t) (decorate m j (slice w j t)) = m j := by
  have hlen := OuterColumn.slice_length w j t hjt ht
  have he : j+(slice w j t).length=t := by omega
  have h := IndexedMarked.mark_after_drop m j (slice w j t) 0 (Nat.zero_le _)
  simpa only [he,Nat.add_zero,List.drop_zero] using h

def AnchoredMask (P : SevenDFA α) (m : Nat → Bool) (w : Word α)
    (a z t : Nat) (qa : Fin P.A.stateCount) : Prop :=
  ∃ p j, a≤p ∧ p≤j ∧ z≤j ∧ j≤t ∧ m p=true ∧
    P.C.accepts (slice w a p) ∧ P.D.accepts (slice w p j) ∧
    P.A.final (P.A.run qa (slice w z j))=true ∧ P.B.accepts (slice w j t)

theorem whole_indices (P : SevenDFA α) (m : Nat → Bool) (w : Word α)
    (a z t : Nat) (qa : Fin P.A.stateCount)
    (haz : a≤z) (hzt : z≤t) (ht : t≤w.length) :
    whole P (m t) (decorate m a (slice w a z)) (decorate m z (slice w z t)) qa=true ↔
      AnchoredMask P m w a z t qa := by
  rw [whole_spec]
  constructor
  · rintro ⟨u,v,he,ha,hcd,hb⟩
    obtain ⟨j,hzj,hjt,hu,hv⟩ := (decorate_split m w z t hzt ht u v).mp he
    subst u
    subst v
    rw [IndexedMarked.decorate_text] at ha hb
    rw [boundary_mark m w j t hjt ht,decorate_join m w a z j haz hzj (by omega)] at hcd
    obtain ⟨p,hap,hpj,hm,hc,hd⟩ := (IndexedMarked.switch_iff_indices P.C P.D m w a j
      P.C.initial (by omega) (by omega)).mp hcd
    exact ⟨p,j,hap,hpj,hzj,hjt,hm,hc,hd,ha,hb⟩
  · rintro ⟨p,j,hap,hpj,hzj,hjt,hm,hc,hd,ha,hb⟩
    refine ⟨decorate m z (slice w z j),decorate m j (slice w j t),
      (decorate_join m w z j t hzj hjt ht).symm,?_,?_,?_⟩
    · simpa only [IndexedMarked.decorate_text] using ha
    · rw [boundary_mark m w j t hjt ht,decorate_join m w a z j haz hzj (by omega)]
      exact (IndexedMarked.switch_iff_indices P.C P.D m w a j P.C.initial
        (by omega) (by omega)).mpr ⟨p,hap,hpj,hm,hc,hd⟩
    · simpa only [IndexedMarked.decorate_text] using hb

/-! Materialized indices. The generic wrapper works on any relation letter
    function over a fixed enumerated state space. -/
namespace RelIndex
variable {S X : Type} [DecidableEq S]

def letters (e : Enumeration S) (step : X → Rel S) (xs : List X) :
    List (MatrixTable.Matrix e) :=
  xs.map (fun x => MatrixTable.ofRel e (step x))

theorem letters_length (e : Enumeration S) (step : X → Rel S) (xs : List X) :
    (letters e step xs).length=xs.length := by simp [letters]

def build (e : Enumeration S) (step : X → Rel S) (xs : List X) :
    DyadicIndex.Tree (MatrixTable.Matrix e) × Nat :=
  DyadicIndex.buildFor (MatrixTable.ops e) (letters e step xs)

def query (e : Enumeration S) (idx : DyadicIndex.Tree (MatrixTable.Matrix e))
    (l r : Nat) : Option (Rel S) :=
  (DyadicIndex.query (MatrixTable.ops e) idx l r).answer.map MatrixTable.denote

private theorem map_take {e : Enumeration S} (f : X → MatrixTable.Matrix e) (xs : List X) (k : Nat) :
    (xs.map f).take k=(xs.take k).map f := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      change f x::(xs.map f).take k=f x::(xs.take k).map f
      rw [ih]

private theorem map_drop {e : Enumeration S} (f : X → MatrixTable.Matrix e) (xs : List X) (k : Nat) :
    (xs.map f).drop k=(xs.drop k).map f := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs => exact ih xs

theorem query_correct (e : Enumeration S) (step : X → Rel S) (xs : List X)
    (l r : Nat) (hl : l≤r) (hr : r≤xs.length) :
    query e (build e step xs).1 l r =
      some (RangeProducts.product (FiniteRelation.ops e) ((slice xs l r).map step)) := by
  have h := (DyadicIndex.queryFor_spec (MatrixTable.ops e) (letters e step xs)
    l r hl (by simpa only [letters_length] using hr)).1
  unfold query build
  rw [h]
  simp only [Option.map,MatrixTable.denote_product,letters,slice,map_drop,map_take,
    List.map_map,Function.comp_def,MatrixTable.denote_ofRel]

end RelIndex

structure Indices (P : SevenDFA α) where
  first : DyadicIndex.Tree (MatrixTable.Matrix (cdEnum P))
  second : DyadicIndex.Tree (MatrixTable.Matrix (rightMachine P).enum)

def build (P : SevenDFA α) (w : MarkedWord α) : Indices P :=
  ⟨(RelIndex.build (cdEnum P) (MarkedTransfer.letter P.C P.D) w).1,
    (RelIndex.build (rightMachine P).enum (rightMachine P).letter w).1⟩

/-- Two indexed products, followed by a finite-state join at z. -/
def query (P : SevenDFA α) (idx : Indices P) (terminal : Bool)
    (a z t : Nat) (qa : Fin P.A.stateCount) : Option Bool := do
  let x ← RelIndex.query (cdEnum P) idx.first a z
  let y ← RelIndex.query (rightMachine P).enum idx.second z t
  return pre (cdEnum P) x (fun s =>
    pre (rightMachine P).enum y ((rightMachine P).final terminal) (.inl (s,qa)))
      (.inl P.C.initial)

theorem query_correct (P : SevenDFA α) (w : MarkedWord α) (terminal : Bool)
    (a z t : Nat) (qa : Fin P.A.stateCount)
    (haz : a≤z) (hzt : z≤t) (ht : t≤w.length) :
    query P (build P w) terminal a z t qa =
      some (whole P terminal (slice w a z) (slice w z t) qa) := by
  unfold query build
  rw [RelIndex.query_correct _ _ _ _ _ haz (by omega),
    RelIndex.query_correct _ _ _ _ _ hzt ht]
  rfl

theorem p1_query (P : SevenDFA α) (w : Word α) (a t d : Nat)
    (m : Nat → Bool) (hat : a≤t) (ht : t≤w.length) (hd : d≤t-a)
    (hm : ∀ i, i≤w.length → (m i=true ↔ NestedColumns.Ready P w i t)) :
    query P (build P (decorate m 0 w)) (m t) a (t-d) t
      (P.A.run P.A.initial (slice w 0 (a-d))) = some true ↔
      NestedColumns.Anchored1 P w a t d := by
  rw [query_correct P _ _ _ _ _ _ (by omega) (by omega)
    (by simpa only [IndexedMarked.decorate_length] using ht),
    Option.some.injEq,IndexedMarked.decorate_slice,IndexedMarked.decorate_slice,
    whole_indices P m w a (t-d) t _ (by omega) (by omega) ht]
  constructor
  · rintro ⟨p,j,hap,hpj,hzj,hjt,hmark,hc,hgap,ha,hb⟩
    exact ⟨p,j,hap,hpj,hzj,hjt,(hm p (by omega)).mp hmark,hc,hgap,ha,hb⟩
  · rintro ⟨p,j,hap,hpj,hzj,hjt,hmark,hc,hgap,ha,hb⟩
    exact ⟨p,j,hap,hpj,hzj,hjt,(hm p (by omega)).mpr hmark,hc,hgap,ha,hb⟩

end REWB.P1Index
