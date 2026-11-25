import REWB.MaskedProgression

/-! Constant-slot queries on a stepped prefix-count array.

    `grid counts step start wanted` asks for a marked position among
    start, start+step, ..., start+(wanted-1)*step, clipped to the array.
    Empty requests and starts outside the window are rejected before any
    prefix cell is read. The query reads at most two count cells. -/
namespace REWB.MaskedProgression

structure Answer where
  answer : Bool
  slots : Nat
  arithmetic : Nat
  deriving Repr

def grid (counts : Array Nat) (step start wanted : Nat) : Answer :=
  if wanted=0 then ⟨false,0,1⟩
  else if counts.size≤start then ⟨false,0,2⟩
  else
    let capacity := (counts.size-1-start)/step+1
    let used := min wanted capacity
    let last := start+(used-1)*step
    let earlier := if step≤start then readCount counts (start-step) else 0
    ⟨decide (earlier<readCount counts last),
      1+(if step≤start then 1 else 0),12+(if step≤start then 1 else 0)⟩

theorem grid_slots (counts : Array Nat) (step start wanted : Nat) :
    (grid counts step start wanted).slots≤2 := by
  unfold grid
  split
  · decide
  · split
    · decide
    · split <;> simp

theorem grid_arithmetic (counts : Array Nat) (step start wanted : Nat) :
    (grid counts step start wanted).arithmetic≤13 := by
  unfold grid
  split
  · decide
  · split
    · decide
    · split <;> simp

/-- This clipping formula is also valid when step exceeds the window. -/
theorem capacity_correct (size step start t : Nat) (hs : 0<step) (ha : start<size) :
    t<(size-1-start)/step+1 ↔ start+t*step<size := by
  have hh := Nat.le_div_iff_mul_le (x:=t) (y:=size-1-start) hs
  omega

theorem grid_correct (counts : Array Nat) (mask : Nat → Bool) (step : Nat)
    (hs : 0<step)
    (hc : ∀ i, i<counts.size → readCount counts i=countAt mask step hs i)
    (start wanted : Nat) :
    (grid counts step start wanted).answer=true ↔
      ∃ t, t<wanted ∧ start+t*step<counts.size ∧ mask (start+t*step)=true := by
  by_cases hw : wanted=0
  · subst wanted
    simp [grid]
  · by_cases ho : counts.size≤start
    · simp only [grid,hw,if_false,ho,if_true,Bool.false_eq_true,false_iff]
      rintro ⟨t,_,ht,_⟩
      omega
    · have hstart : start<counts.size := by omega
      let capacity := (counts.size-1-start)/step+1
      let used := min wanted capacity
      have hcap : 0<capacity := Nat.succ_pos _
      have hu : 0<used := by dsimp [used]; omega
      have hclip (t : Nat) : t<used ↔ t<wanted ∧ start+t*step<counts.size := by
        have hh := capacity_correct counts.size step start t hs hstart
        change t<capacity ↔ _ at hh
        dsimp only [used]
        omega
      let last := start+(used-1)*step
      have hlast : last<counts.size := (hclip (used-1)).mp (by omega) |>.2
      have hbefore : (if step≤start then readCount counts (start-step) else 0)=
          before mask step hs start := by
        unfold before
        by_cases hp : step≤start
        · rw [if_pos hp,if_pos hp,hc _ (by omega)]
        · rw [if_neg hp,if_neg hp]
      have hhigh : readCount counts last=before mask step hs start+tally mask step start used := by
        rw [hc last hlast]
        change countAt mask step hs (start+(used-1)*step)=_
        rw [countAt_tally,show used-1+1=used by omega]
      simp only [grid,hw,if_false,ho]
      change decide ((if step≤start then readCount counts (start-step) else 0)<
        readCount counts last)=true ↔ _
      rw [decide_eq_true_eq,hbefore,hhigh]
      have he : before mask step hs start<before mask step hs start+tally mask step start used ↔
          0<tally mask step start used := by omega
      rw [he,tally_pos]
      constructor
      · rintro ⟨t,ht,hm⟩
        obtain ⟨hw,hbound⟩ := (hclip t).mp ht
        exact ⟨t,hw,hbound,hm⟩
      · rintro ⟨t,hw,hbound,hm⟩
        exact ⟨t,(hclip t).mpr ⟨hw,hbound⟩,hm⟩

theorem grid_build_correct (mask : Array Bool) (base len step : Nat) (hs : 0<step)
    (start wanted : Nat) :
    (grid (build mask base len step).counts step start wanted).answer=true ↔
      ∃ t, t<wanted ∧ start+t*step<len ∧ readMask mask (base+(start+t*step))=true := by
  have hh := grid_correct (build mask base len step).counts
    (fun i => readMask mask (base+i)) step hs
    (fun i hi => build_correct mask base len step hs i (by simpa only [build_size] using hi))
    start wanted
  simpa only [build_size] using hh

end REWB.MaskedProgression
