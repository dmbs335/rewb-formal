import REWB.BoundaryBorderRegularSelection
import REWB.MaskedProgressionAP

/-! Constant-work clipping and alignment of a physical AP. Only quotient,
remainder and endpoint arithmetic is used; no residue or exponent list
is materialized. -/
namespace REWB.BoundaryBorder.Regular
open REWB.MaskedProgression

/-- First member of the residue class at or above the lower endpoint. -/
def firstAt (first q lo : Nat) : Nat := first+ceilDiv (lo-first) q*q

theorem member_progression (first q lo hi p : Nat) (hq : 0<q) :
    Member first q lo hi p ↔ ∃k,p=firstAt first q lo+k*q ∧ firstAt first q lo+k*q≤hi := by
  have ha : aligned (lo-first) q 0=ceilDiv (lo-first) q*q := by
    simp only [aligned,Nat.sub_zero,Nat.zero_add]
  constructor
  · rintro ⟨hl,hh,hfirst,hmod⟩
    obtain ⟨k,hk⟩:=(aligned_progression (lo-first) q 0 (p-first) hq hq).mp ⟨by omega,hmod⟩
    rw [ha] at hk
    have he : p=firstAt first q lo+k*q := by unfold firstAt; omega
    exact ⟨k,he,by omega⟩
  · rintro ⟨k,rfl,hh⟩
    have hb:=(aligned_progression (lo-first) q 0 (ceilDiv (lo-first) q*q+k*q) hq hq).mpr
      ⟨k,by rw [ha]⟩
    refine ⟨?_,hh,?_,?_⟩
    · unfold firstAt
      omega
    · unfold firstAt
      omega
    · simpa only [firstAt,Nat.add_assoc,Nat.add_sub_cancel_left] using hb.2

theorem member_normalized (first q lo hi p : Nat) (hq : 0<q)
    (hh : firstAt first q lo≤hi) :
    Member first q lo hi p ↔
      ∃k,k≤(hi-firstAt first q lo)/q ∧ p=firstAt first q lo+k*q := by
  rw [member_progression first q lo hi p hq]
  constructor
  · rintro ⟨k,hp,hb⟩
    exact ⟨k,(Nat.le_div_iff_mul_le hq).mpr (by omega),hp⟩
  · rintro ⟨k,hk,hp⟩
    have hm:=(Nat.le_div_iff_mul_le hq).mp hk
    exact ⟨k,hp,by omega⟩

def align (first q lo hi : Nat) : Option (Nat×Nat)×Nat :=
  if q=0 then (none,2)
  else
    let start:=firstAt first q lo
    if hi<start then (none,11)
    else (some (start,(hi-start)/q),14)

theorem align_work (first q lo hi : Nat) : (align first q lo hi).2≤14 := by
  unfold align
  split
  · decide
  · dsimp only
    split <;> dsimp only <;> omega

theorem align_some (first q lo hi start m : Nat)
    (he : (align first q lo hi).1=some (start,m)) :
    0<q ∧ start=firstAt first q lo ∧ m=(hi-start)/q ∧ start≤hi := by
  unfold align at he
  split at he
  · contradiction
  · rename_i hq
    dsimp only at he
    split at he
    · contradiction
    · rename_i hh
      have hh':(firstAt first q lo,(hi-firstAt first q lo)/q)=(start,m) := Option.some.inj he
      cases hh'
      exact ⟨by omega,rfl,rfl,by omega⟩

theorem align_correct (first q lo hi : Nat) (hq : 0<q) (p : Nat) :
    Member first q lo hi p ↔
      ∃start m,(align first q lo hi).1=some (start,m) ∧ ∃k,k≤m ∧ p=start+k*q := by
  by_cases hh : hi<firstAt first q lo
  · have he : (align first q lo hi).1=none := by simp only [align,show q≠0 by omega,if_false,hh,if_true]
    rw [he]
    constructor
    · intro hp
      obtain ⟨k,_,hb⟩:=(member_progression first q lo hi p hq).mp hp
      omega
    · rintro ⟨_,_,hh,_⟩
      cases hh
  · have hb : firstAt first q lo≤hi := by omega
    have he : (align first q lo hi).1=some (firstAt first q lo,(hi-firstAt first q lo)/q) := by
      simp only [align,show q≠0 by omega,if_false,hh]
    rw [member_normalized first q lo hi p hq hb,he]
    simp only [Option.some.injEq,Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨_,_,⟨rfl,rfl⟩,h⟩
    · rintro ⟨start,m,⟨rfl,rfl⟩,h⟩
      exact h

theorem align_member (first q lo hi start m p : Nat)
    (he : (align first q lo hi).1=some (start,m)) :
    Member first q lo hi p ↔∃k,k≤m ∧ p=start+k*q := by
  obtain ⟨hq,hs,hm,hh⟩:=align_some first q lo hi start m he
  subst start
  subst m
  exact member_normalized first q lo hi p hq hh

theorem align_first (first q lo hi start m : Nat)
    (he : (align first q lo hi).1=some (start,m)) : Member first q lo hi start :=
  (align_member first q lo hi start m start he).mpr ⟨0,Nat.zero_le _,by simp only [Nat.zero_mul,Nat.add_zero]⟩

theorem align_last (first q lo hi start m : Nat)
    (he : (align first q lo hi).1=some (start,m)) : Member first q lo hi (start+m*q) :=
  (align_member first q lo hi start m (start+m*q) he).mpr ⟨m,Nat.le_refl _,rfl⟩

/-- Endpoint clipping includes a source precisely when its second copy
ends by r. The enclosing query handles j>r before this operation. -/
theorem clip_member (first q lo hi a j r p : Nat) (hj : j≤r) :
    Member first q (max lo (a-(r-j))) (min hi a) p ↔
      Member first q lo hi p ∧ p≤a ∧ endAt j a p≤r := by
  rw [show endAt j a p≤r ↔ a-p≤r-j by unfold endAt; omega]
  exact band_iff first q lo hi a (r-j) p

end REWB.BoundaryBorder.Regular
