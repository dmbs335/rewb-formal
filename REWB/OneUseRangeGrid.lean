import REWB.OneUseRangeBorderPartition

/-! Constant-work addresses for the two prefix-cache families. The
last forward position is clipped at n, so terminal empty captures are
covered without an out-of-range sentinel or a scan for a grid cell. -/
namespace REWB.OneUseRange.Grid
open REWB.MaskedProgression

def count (n width : Nat) : Nat := n/width+2
def position (n width slot : Nat) : Nat := min n (slot*width)
def backward (n width slot : Nat) : Nat := n-position n width slot

theorem position_bound (n width slot : Nat) : position n width slot≤n := Nat.min_le_left _ _

theorem floor_slot (n width right : Nat) (hw : 0<width) (hr : right≤n) : right/width<count n width := by
  have h:=(Nat.le_div_iff_mul_le hw).mpr (Nat.le_trans (Nat.div_mul_le_self right width) hr)
  unfold count
  omega

theorem ceil_slot (n width left : Nat) (hw : 0<width) (hl : left≤n) : ceilDiv left width<count n width := by
  have hn:=Nat.mod_add_div n width
  have hm:=Nat.mod_lt n hw
  rw [Nat.mul_comm width (n/width)] at hn
  have hu : left≤(n/width+1)*width := by rw [Nat.add_mul,Nat.one_mul]; omega
  have h:=(ceilDiv_le left width (n/width+1) hw).mpr hu
  unfold count
  omega

theorem floor_bounds (n width right : Nat) (hw : 0<width) (hr : right≤n) :
    position n width (right/width)≤right ∧ right-position n width (right/width)<width := by
  have hp:=Nat.div_mul_le_self right width
  have hm:=Nat.mod_lt right hw
  have he:=Nat.mod_add_div right width
  rw [Nat.mul_comm width (right/width)] at he
  unfold position
  rw [Nat.min_eq_right (by omega)]
  omega

theorem ceil_bounds (n width left : Nat) (hw : 0<width) (hl : left≤n) :
    left≤position n width (ceilDiv left width) ∧
      position n width (ceilDiv left width)-left<width := by
  have hc:=ceilDiv_cover left width hw
  have hb:=Nat.div_mul_le_self (left+width-1) width
  change ceilDiv left width*width≤left+width-1 at hb
  unfold position
  omega

structure Choice (n width : Nat) where
  leftSlot : Fin (count n width)
  rightSlot : Fin (count n width)
  leftGrid : Nat
  rightGrid : Nat
  work : Nat

def choose (n width : Nat) (hw : 0<width) (left right : Nat)
    (hlr : left≤right) (hr : right≤n) : Choice n width :=
  let l:=ceilDiv left width
  let r:=right/width
  ⟨⟨l,ceil_slot n width left hw (by omega)⟩,⟨r,floor_slot n width right hw hr⟩,
    position n width l,position n width r,14⟩

theorem choose_positions (n width : Nat) (hw : 0<width) (left right : Nat)
    (hlr : left≤right) (hr : right≤n) :
    (choose n width hw left right hlr hr).leftGrid=
      position n width (choose n width hw left right hlr hr).leftSlot.val ∧
    (choose n width hw left right hlr hr).rightGrid=
      position n width (choose n width hw left right hlr hr).rightSlot.val := ⟨rfl,rfl⟩

theorem choose_bounds (n width : Nat) (hw : 0<width) (left right : Nat)
    (hlr : left≤right) (hr : right≤n) :
    left≤(choose n width hw left right hlr hr).leftGrid ∧
    (choose n width hw left right hlr hr).leftGrid≤n ∧
    (choose n width hw left right hlr hr).rightGrid≤right ∧
    (choose n width hw left right hlr hr).leftGrid-left<width ∧
    right-(choose n width hw left right hlr hr).rightGrid<width := by
  have hl:=ceil_bounds n width left hw (by omega)
  have hg:=position_bound n width (ceilDiv left width)
  have hr':=floor_bounds n width right hw hr
  exact ⟨hl.1,hg,hr'.1,hl.2,hr'.2⟩

theorem choose_work (n width : Nat) (hw : 0<width) (left right : Nat)
    (hlr : left≤right) (hr : right≤n) : (choose n width hw left right hlr hr).work=14 := rfl

theorem reverse_grid_bound (n width left : Nat) (hw : 0<width) (hl : left≤n) :
    backward n width (ceilDiv left width)≤n-left := by
  have hh:=ceil_bounds n width left hw hl
  unfold backward
  omega

end REWB.OneUseRange.Grid
