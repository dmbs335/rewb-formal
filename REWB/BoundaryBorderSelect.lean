import REWB.BoundaryBorderGeometry

/-! A constant-query selector for one periodic source component.  Two
    measured LCEs locate the source and target period breaks.  A third
    LCE is used only for the unique exceptional source past the break.
    The output is one physical AP window, one point, or the empty set;
    it does not enumerate periods, phases, starts or capture lengths.
    The caller still supplies a correctly located occurrence component.
-/
namespace REWB.BoundaryBorder
open Periodic RunGeometry LCEIndex
variable {σ : Nat}

abbrev Member (first q lo hi p : Nat) : Prop :=
  lo≤p ∧ p≤hi ∧ first≤p ∧ (p-first)%q=0

inductive Choice where
  | empty
  | progression (first step lower upper : Nat)
  | point (position : Nat)
deriving Repr,DecidableEq

def Choice.Holds : Choice→Nat→Prop
  | .empty,_ => False
  | .progression first step lower upper,p => Member first step lower upper p
  | .point position,p => p=position

structure Selection where
  choice : Choice
  work : Nat

theorem band_iff (first q lo hi a targetExtent p : Nat) :
    Choice.Holds (.progression first q (max lo (a-targetExtent)) (min hi a)) p ↔
      Member first q lo hi p ∧ p≤a ∧ a-p≤targetExtent := by
  constructor
  · rintro ⟨hlo,hhi,hs,hm⟩
    have hl:=Nat.le_trans (Nat.le_max_left lo (a-targetExtent)) hlo
    have ht:=Nat.le_trans (Nat.le_max_right lo (a-targetExtent)) hlo
    have hh:=Nat.le_trans hhi (Nat.min_le_left hi a)
    have ha:=Nat.le_trans hhi (Nat.min_le_right hi a)
    exact ⟨⟨hl,hh,hs,hm⟩,ha,by omega⟩
  · rintro ⟨⟨hl,hh,hs,hm⟩,ha,ht⟩
    exact ⟨Nat.max_le.mpr ⟨hl,by omega⟩,Nat.le_min.mpr ⟨hh,ha⟩,hs,hm⟩

def choose (idx : RankIndex.Index) (n first q lo hi a j right targetExtent : Nat) : Selection :=
  if a≤right then
    ⟨.progression first q (max lo (a-targetExtent)) (min hi a),12⟩
  else
    let p:=right-targetExtent
    if Member first q lo hi p ∧ p≤a then
      let equal:=lceMeasured idx n p j
      if a-p≤equal.length then ⟨.point p,equal.countedWork+20⟩
      else ⟨.empty,equal.countedWork+20⟩
    else ⟨.empty,16⟩

theorem choose_work (idx : RankIndex.Index) (n first q lo hi a j right targetExtent : Nat) :
    (choose idx n first q lo hi a j right targetExtent).work≤13*(n.log2+1)+21 := by
  have hh:=lceMeasured_work idx n (right-targetExtent) j
  unfold choose
  split
  · simp only [Selection.work]; omega
  · dsimp only
    split
    · split <;> simp only [Selection.work] <;> omega
    · simp only [Selection.work]; omega

theorem choose_correct (f : Nat→Fin σ) (n first q lo hi a j sourceExtent targetExtent : Nat)
    (hs : PeriodPrefix f n first q sourceExtent) (ht : PeriodPrefix f n j q targetExtent)
    (hq : 0<q) (hsq : q≤sourceExtent) (ha : a≤n) (hspan : hi+q≤first+sourceExtent)
    (hseed : ∀p,Member first q lo hi p→segment f p q=segment f j q) (p : Nat) :
    (choose (prepare f n) n first q lo hi a j (first+sourceExtent) targetExtent).choice.Holds p ↔
      Member first q lo hi p ∧ p≤a ∧ Agree f n p j (a-p) := by
  have hper : OnPeriod f first (first+sourceExtent) q := by
    apply (on_iff f first (first+sourceExtent) q).mpr
    simpa only [Nat.add_sub_cancel_left] using hs.periodic
  have hstop : first+sourceExtent=n ∨
      f (first+sourceExtent-q)≠f (first+sourceExtent) := by
    by_cases he : first+sourceExtent=n
    · exact Or.inl he
    · exact Or.inr (prefix_failure f n first q sourceExtent hs hq hsq (by have hb:=hs.bounded; omega))
  by_cases hab : a≤first+sourceExtent
  · rw [choose,if_pos hab]
    rw [band_iff]
    have heq (x : Nat) (hm : Member first q lo hi x) (hx : x≤a) :
        Agree f n x j (a-x) ↔ a-x≤targetExtent := by
      have ho:=on_restrict f first (first+sourceExtent) q x a hper hm.2.2.1 hab
      exact inside_iff f n x j q targetExtent (a-x) hq (by omega)
        ((on_iff f x a q).mp ho) (hseed x hm) ht
    constructor
    · rintro ⟨hm,hx,hL⟩
      exact ⟨hm,hx,(heq p hm hx).mpr hL⟩
    · rintro ⟨hm,hx,hL⟩
      exact ⟨hm,hx,(heq p hm hx).mp hL⟩
  · have unique (x : Nat) (hm : Member first q lo hi x) (heq : Agree f n x j (a-x)) :
        x=first+sourceExtent-targetExtent :=
      outside_unique_candidate f n first (first+sourceExtent) x j q targetExtent a
        hper hm.2.2.1 hq (by have hh:=hm.2.1; omega) hs.bounded hstop ht (by omega) heq
    let candidate:=first+sourceExtent-targetExtent
    rw [choose,if_neg hab]
    by_cases hc : Member first q lo hi candidate ∧ candidate≤a
    · rw [if_pos hc]
      have hlce:=lceMeasured_correct f n candidate j (by have hp:=hc.2; omega)
        (by have hb:=ht.bounded; omega)
      have hiff:=lce_agree_iff f n candidate j _ (a-candidate) hlce
      by_cases he : a-candidate≤(lceMeasured (prepare f n) n candidate j).length
      · rw [if_pos he]
        change p=candidate ↔ _
        constructor
        · intro hp
          subst p
          exact ⟨hc.1,hc.2,hiff.mpr he⟩
        · rintro ⟨hm,_,heq⟩
          exact unique p hm heq
      · rw [if_neg he]
        change False ↔ _
        constructor
        · exact False.elim
        · rintro ⟨hm,hpa,heq⟩
          have hp : p=candidate := unique p hm heq
          subst p
          exact he (hiff.mp heq)
    · rw [if_neg hc]
      change False ↔ _
      constructor
      · exact False.elim
      · rintro ⟨hm,hpa,heq⟩
        have hp : p=candidate := unique p hm heq
        subst p
        exact hc ⟨hm,hpa⟩

def select (idx : RankIndex.Index) (n first q lo hi a j : Nat) : Selection :=
  let source:=extend idx n first q
  let target:=extend idx n j q
  let picked:=choose idx n first q lo hi a j (first+source.extent) target.extent
  ⟨picked.choice,source.work+target.work+picked.work+5⟩

theorem select_correct (f : Nat→Fin σ) (n first q lo hi a j : Nat)
    (hq : 0<q) (hs : first+q≤n) (hj : j+q≤n) (ha : a≤n)
    (hspan : hi+q≤first+(extend (prepare f n) n first q).extent)
    (hseed : ∀p,Member first q lo hi p→segment f p q=segment f j q) (p : Nat) :
    (select (prepare f n) n first q lo hi a j).choice.Holds p ↔
      Member first q lo hi p ∧ p≤a ∧ Agree f n p j (a-p) := by
  exact choose_correct f n first q lo hi a j _ _ (extend_correct f n first q hs)
    (extend_correct f n j q hj) hq (by change q≤q+_; omega) ha hspan hseed p

theorem select_work (idx : RankIndex.Index) (n first q lo hi a j : Nat) :
    (select idx n first q lo hi a j).work≤39*(n.log2+1)+34 := by
  have hs:=extend_work idx n first q
  have ht:=extend_work idx n j q
  have hc:=choose_work idx n first q lo hi a j
    (first+(extend idx n first q).extent) (extend idx n j q).extent
  change _+_+_+5≤_
  omega

end REWB.BoundaryBorder
