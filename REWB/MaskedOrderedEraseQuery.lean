import REWB.MaskedOrderedErase
import REWB.MaskedOrderedQuery

/-! Inclusive interval witnesses from one ordered-tree successor query.
The zero lower endpoint uses the cached minimum; every other endpoint
uses the existing one-descent strict successor. -/
namespace REWB.MaskedOrdered.Tree

variable {h : Nat}

def LowerSpec (xs : List Nat) (lo : Nat) : Option Nat→Prop
  | none => ∀x,x∈xs→x<lo
  | some x => x∈xs ∧ lo≤x ∧ ∀y,y∈xs→lo≤y→x≤y

def lowerBound (t : Tree h) (capacity lo : Nat) : Option Nat×Nat :=
  if lo=0 then (t.first,2)
  else
    let r:=succ t capacity (lo-1)
    (r.1,r.2+2)

theorem lowerBound_work (t : Tree h) (capacity lo : Nat) :
    (lowerBound t capacity lo).2≤7*h+5 := by
  unfold lowerBound
  split
  · omega
  · have hh:=succ_work t capacity (lo-1)
    dsimp only
    omega

theorem lowerBound_correct (t : Tree h) (capacity lo : Nat)
    (hg : Good t) (hf : Fits t 0) (hc : capacity=2^h) :
    LowerSpec t.entries lo (lowerBound t capacity lo).1 := by
  unfold lowerBound
  split
  next he =>
    subst lo
    have hh:=first_spec t 0 hg hf
    cases hv : t.first with
    | none =>
      simp only [hv,MinSpec] at hh
      simp only [LowerSpec,hh,List.not_mem_nil,false_implies,implies_true]
    | some x =>
      simp only [hv,MinSpec] at hh
      exact ⟨hh.1,Nat.zero_le _,fun y hy _=>hh.2 y hy⟩
  next he =>
    have hh:=succ_correct t capacity (lo-1) hg hf hc
    cases hv : (succ t capacity (lo-1)).1 with
    | none =>
      simp only [hv,SuccSpec] at hh
      intro x hx
      have hh':=hh x hx
      omega
    | some x =>
      simp only [hv,SuccSpec] at hh
      refine ⟨hh.1,by omega,?_⟩
      intro y hy hlo
      exact hh.2.2 y hy (by omega)

/-- Exact least live key in the inclusive interval, or `none`. -/
def interval (t : Tree h) (capacity lo hi : Nat) : Option Nat×Nat :=
  let r:=lowerBound t capacity lo
  match r.1 with
  | none => (none,r.2+1)
  | some x => (if x≤hi then some x else none,r.2+2)

theorem interval_work (t : Tree h) (capacity lo hi : Nat) :
    (interval t capacity lo hi).2≤7*h+7 := by
  have hh:=lowerBound_work t capacity lo
  unfold interval
  cases hv : (lowerBound t capacity lo).1 <;> simp only [hv] <;> omega

theorem interval_some (t : Tree h) (capacity lo hi x : Nat)
    (hg : Good t) (hf : Fits t 0) (hc : capacity=2^h)
    (hx : (interval t capacity lo hi).1=some x) :
    x∈t.entries ∧ lo≤x ∧ x≤hi ∧ ∀y,y∈t.entries→lo≤y→x≤y := by
  have hh:=lowerBound_correct t capacity lo hg hf hc
  unfold interval at hx
  cases hv : (lowerBound t capacity lo).1 with
  | none => simp only [hv] at hx; contradiction
  | some q =>
    simp only [hv,LowerSpec] at hh
    simp only [hv] at hx
    split at hx
    next hq =>
      have he : q=x:=Option.some.inj hx
      subst q
      exact ⟨hh.1,hh.2.1,hq,hh.2.2⟩
    next hq => contradiction

theorem interval_exists (t : Tree h) (capacity lo hi : Nat)
    (hg : Good t) (hf : Fits t 0) (hc : capacity=2^h) :
    (∃x,(interval t capacity lo hi).1=some x) ↔
      ∃x,x∈t.entries ∧ lo≤x ∧ x≤hi := by
  constructor
  · rintro ⟨x,hx⟩
    have hh:=interval_some t capacity lo hi x hg hf hc hx
    exact ⟨x,hh.1,hh.2.1,hh.2.2.1⟩
  · rintro ⟨x,hx,hlo,hhi⟩
    have hh:=lowerBound_correct t capacity lo hg hf hc
    unfold interval
    cases hv : (lowerBound t capacity lo).1 with
    | none =>
      simp only [hv,LowerSpec] at hh
      have hn:=hh x hx
      omega
    | some q =>
      simp only [hv,LowerSpec] at hh
      have hq:=hh.2.2 x hx hlo
      simp only [hv,if_pos (show q≤hi by omega)]
      exact ⟨q,rfl⟩

end REWB.MaskedOrdered.Tree
