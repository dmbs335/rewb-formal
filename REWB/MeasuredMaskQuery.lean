import REWB.MaskedReporting

/-! A concrete measured interval-existence query over a materialized source
    mask.  This supplies an executable reference instance for the reporting
    interface.  It scans the interval: no logarithmic query-time claim is
    made, and constructing the input mask is a separate obligation.

    Array reads and loop tests are the counted primitives.  An empty scan
    uses one test; a nonempty scan uses one test and one array read, then
    either terminates or recurses.  The cost includes unsuccessful scans.
    Unit-time array access is the explicit abstract model. -/
namespace REWB.MeasuredMaskQuery
open MaskedReporting

def read (mask : Array Bool) (s : Nat) : Bool :=
  mask[s]?.getD false

def scan (mask : Array Bool) : Nat → Nat → Bool × Nat
  | 0, _ => (false,1)
  | len+1, lo =>
    if read mask lo then (true,2)
    else
      let rest := scan mask len (lo+1)
      (rest.1,2+rest.2)

theorem scan_correct (mask : Array Bool) (len lo : Nat) :
    (scan mask len lo).1 = true ↔
      ∃ s, lo ≤ s ∧ s < lo+len ∧ read mask s = true := by
  induction len generalizing lo with
  | zero =>
    simp only [scan,Bool.false_eq_true,Nat.add_zero,false_iff]
    rintro ⟨s,hl,hr,_⟩
    omega
  | succ len ih =>
    simp only [scan]
    split
    next hp =>
      simp only [true_iff]
      exact ⟨lo,Nat.le_refl _,by omega,hp⟩
    next hp =>
      rw [ih]
      constructor
      · rintro ⟨s,hl,hr,hs⟩
        exact ⟨s,by omega,by omega,hs⟩
      · rintro ⟨s,hl,hr,hs⟩
        have hn : s≠lo := by intro he; subst s; exact hp hs
        exact ⟨s,by omega,by omega,hs⟩

theorem scan_cost (mask : Array Bool) (len lo : Nat) :
    (scan mask len lo).2 ≤ 2*len+1 := by
  induction len generalizing lo with
  | zero => exact Nat.le_refl _
  | succ len ih =>
    have hh := ih (lo+1)
    simp only [scan]
    split <;> omega

/-- Query endpoints are clipped to the materialized mask.  This also makes
    arbitrary reversed/out-of-bounds intervals behave as empty intervals. -/
def query (mask : Array Bool) (l r : Nat) : Bool × Nat :=
  scan mask (min r mask.size-l) l

theorem query_correct (mask : Array Bool) :
    QueryCorrect (query mask) (fun s => s<mask.size ∧ read mask s=true) := by
  intro l r
  rw [query,scan_correct]
  constructor
  · rintro ⟨s,hl,hr,hs⟩
    have hmin : min r mask.size ≤ r := Nat.min_le_left _ _
    have hsize : min r mask.size ≤ mask.size := Nat.min_le_right _ _
    exact ⟨s,hl,by omega,by omega,hs⟩
  · rintro ⟨s,hl,hr,hsize,hs⟩
    have hmin : s<min r mask.size := by omega
    exact ⟨s,hl,by omega,hs⟩

theorem query_cost (mask : Array Bool) (l r : Nat) :
    (query mask l r).2 ≤ 2*mask.size+1 := by
  have hh := scan_cost mask (min r mask.size-l) l
  have hm := Nat.min_le_right r mask.size
  dsimp [query]
  omega

def all (mask : Array Bool) : Result :=
  report (query mask) (DyadicIndex.heightFor mask.size) 0

theorem all_correct (mask : Array Bool) (s : Nat) :
    s ∈ (all mask).starts ↔ s<mask.size ∧ read mask s=true := by
  rw [all,report_correct _ _ (query_correct mask)]
  constructor
  · exact fun hs => hs.2.2
  · intro hs
    have hc := DyadicIndex.capacity mask.size
    exact ⟨Nat.zero_le _,by omega,hs⟩

theorem all_calls (mask : Array Bool) :
    (all mask).calls ≤ 1+2*(Nat.log2 mask.size+1)*(all mask).starts.length :=
  report_calls _ _ (query_correct mask) _ _

theorem all_queryWork (mask : Array Bool) :
    (all mask).queryWork ≤ (2*mask.size+1)*(all mask).calls :=
  report_queryWork _ _ (query_cost mask) _ _

theorem all_copies (mask : Array Bool) :
    (all mask).copies ≤ (Nat.log2 mask.size+1)*(all mask).starts.length :=
  report_copies _ _ _

/-- This baseline includes its scan cost.  It is deliberately not the fast
    index required for the headline matcher bound. -/
theorem all_totalWork (mask : Array Bool) :
    totalWork (all mask) ≤
      (2*mask.size+2)+(4*mask.size+5)*(Nat.log2 mask.size+1)*(all mask).starts.length := by
  have hh := report_totalWork (query mask) _ (query_correct mask)
    (2*mask.size+1) (query_cost mask) (DyadicIndex.heightFor mask.size) 0
  change totalWork (all mask) ≤ (2*mask.size+1+1)+
    (2*(2*mask.size+1)+3)*(Nat.log2 mask.size+1)*(all mask).starts.length at hh
  have h1 : 2*mask.size+1+1=2*mask.size+2 := by omega
  have h2 : 2*(2*mask.size+1)+3=4*mask.size+5 := by omega
  rwa [h1,h2] at hh

namespace SharedTargetRegression
open MaskedReporting.SharedTargetRegression

def mask : Array Bool := #[true,true,true,false,false]

theorem mask_exact (s : Nat) :
    (s<mask.size ∧ read mask s=true) ↔ s<3 := by
  have hsize : mask.size=5 := rfl
  rw [hsize]
  by_cases hs : s<5
  · have he : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl <;> decide
  · constructor
    · exact fun h => False.elim (hs h.1)
    · intro h
      omega

/-- The concrete scan query meets the original REWB masked-start contract
    for this word, with no external existence oracle. -/
theorem query_spec :
    MaskedQueryCorrect singleton arbitrary arbitrary word target
      (fun _ => true) (query mask) := by
  intro l r
  rw [query_correct]
  constructor
  · rintro ⟨s,hl,hr,hs⟩
    exact ⟨s,hl,hr,rfl,(exact_sources s).mpr ((mask_exact s).mp hs)⟩
  · rintro ⟨s,hl,hr,_,hs⟩
    exact ⟨s,hl,hr,(mask_exact s).mpr ((exact_sources s).mp hs)⟩

def result : Result := reportMasked (query mask) word.length

/-- Kernel computation exercises the actual query, pruning and counters. -/
theorem execution :
    result.starts = [0,1,2] ∧ result.calls = 9 ∧ result.queryWork = 20 ∧
      result.copies = 7 ∧ totalWork result = 36 := by
  have hh : DyadicIndex.heightFor (word.length+1)=3 := by
    simp [DyadicIndex.heightFor,word,Nat.log2]
  unfold result reportMasked
  rw [hh]
  decide

theorem execution_correct (s : Nat) :
    s ∈ result.starts ↔ Spec.maskedStart singleton arbitrary arbitrary word target s := by
  have hh := reportMasked_correct singleton arbitrary arbitrary word target
    (fun _ => true) (query mask) query_spec s
  simpa only [true_and] using hh

end SharedTargetRegression
end REWB.MeasuredMaskQuery
