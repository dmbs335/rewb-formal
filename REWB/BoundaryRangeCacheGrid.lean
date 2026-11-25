import REWB.OneUseRangeGrid

/-! Arithmetic addresses for a clipped boundary block. Position n is a
real boundary; when left=n the last block may have zero width. -/
namespace REWB.BoundaryRange.CacheGrid
open REWB.OneUseRange

abbrev count := Grid.count
def lower (n width slot : Nat) : Nat := Grid.position n width slot
def upper (n width slot : Nat) : Nat := Grid.position n width (slot+1)

theorem bounds (n width slot : Nat) : lower n width slot≤upper n width slot ∧ upper n width slot≤n := by
  unfold lower upper Grid.position
  have hh : slot*width≤(slot+1)*width := by rw [Nat.add_mul,Nat.one_mul]; omega
  omega

theorem span (n width slot : Nat) : upper n width slot-lower n width slot≤width := by
  unfold lower upper Grid.position
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem slot_bound (n width left : Nat) (hw : 0<width) (hl : left≤n) : left/width<count n width :=
  Grid.floor_slot n width left hw hl

theorem selected_bounds (n width left : Nat) (hw : 0<width) (hl : left≤n) :
    lower n width (left/width)≤left ∧ left≤upper n width (left/width) ∧
      upper n width (left/width)-left≤width := by
  have hLo:=(Grid.floor_bounds n width left hw hl).1
  have hm:=Nat.mod_lt left hw
  have he:=Nat.mod_add_div left width
  rw [Nat.mul_comm width (left/width)] at he
  have hb:=span n width (left/width)
  change Grid.position n width (left/width)≤left ∧ left≤upper n width (left/width) ∧ _
  have hHi : left≤upper n width (left/width) := by
    unfold upper Grid.position
    rw [Nat.add_mul,Nat.one_mul]
    omega
  exact ⟨hLo,hHi,by change Grid.position n width (left/width+1)-Grid.position n width (left/width)≤width at hb; change Grid.position n width (left/width+1)-left≤width; omega⟩

end REWB.BoundaryRange.CacheGrid
