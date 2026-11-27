import REWB.MaskedPeriodicTextTail
import REWB.MaskedPeriodicRegression

/-! Kernel checks for genuine text witnesses and a direct finite-text
    reference for the runtime audit. Only this reference enumerates L,k;
    the indexed query does not enumerate capture lengths or cut phases.
-/
namespace REWB.MaskedPeriodic.Text.Regression
open REWB.Periodic REWB.Spec REWB.MaskedCut.DFAIndex
open REWB.MaskedPeriodic.Regression (universal odd even accept)

def unary : Word Bool := [true,true,true,true,true,true]
def target3 : Array Bool := #[false,false,false,true,false,false]

theorem unary_period : RunGeometry.OnPeriod (ArrayText.read unary.toArray false) 1 5 1 := by
  intro i hi hb
  have hc : i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hc with rfl|rfl|rfl <;> rfl

theorem unary_witness : Witness universal universal universal unary [] 1 5 1 target3 0 6 := by
  refine ⟨2,2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try simp only [DFA.accepts,Marked]) <;> decide

theorem unary_full_witness : FullWitness universal universal odd unary 1 5 1 target3 0 6 := by
  refine ⟨2,2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try simp only [DFA.accepts,Marked]) <;> decide

theorem indexed_real_text (prepared : PreparedPattern 1 1 1) :
    (inRun universal universal universal prepared (build universal universal universal unary).1
      1 5 1 (MaskedProgression.build target3 0 6 (prepared.K*1)).counts 0).result.answer=true := by
  apply (inRun_correct universal universal universal prepared unary false 1 5 1 target3 0 6
    (by decide) (by decide) unary_period).mpr
  exact unary_witness

theorem indexed_real_tail (prepared : PreparedPattern 1 1 2) :
    (query universal universal odd prepared (build universal universal odd unary).1
      (prepareTail universal universal odd (build universal universal odd unary).1 5 unary.length).map
      1 5 1 (MaskedProgression.build target3 0 6 (prepared.K*1)).counts 0).result.answer=true := by
  apply (query_full_correct universal universal odd prepared unary false 1 5 1 target3 0 6
    (by decide) (by decide) unary_period).mpr
  exact unary_full_witness

def alternating : Word Bool := [false]++repeatWord [true,false] 5++[true]++[false]
def target7 : Array Bool := #[false,false,false,false,false,false,false,true,false,false,false,false,false]

/-- rho=1, q=2, k+a=N: the final partial-period case uses the real
    empty in-run suffix at the physical endpoint R=12. -/
theorem actual_ending_witness :
    Witness universal universal universal alternating [] 1 12 2 target7 0 13 := by
  refine ⟨5,3,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try simp only [DFA.accepts,Marked]) <;> decide

theorem guard_short (prepared : PreparedPattern 1 1 1) :
    (inRun universal universal universal prepared (build universal universal universal unary).1
      5 5 1 #[] 0).result.answer=false := rfl

/-- A small audit oracle over actual slices, deliberately independent of
    quotient/remainder word-family identities and cut-tuple compilation. -/
def direct (b c e : DFA Bool) (w tail : Word Bool) (s R q : Nat)
    (mask : Array Bool) (base len : Nat) : Bool :=
  if q=0 then false else
    (List.range (R+1)).any fun L=>
      (List.range (R+1)).any fun k=>
        let t := s+k*q
        decide (2*q≤L ∧ s+L≤t ∧ t+L≤R ∧ base≤t ∧ t<base+len) &&
          decide (slice w s (s+L)=slice w t (t+L)) &&
          MaskedProgression.readMask mask t &&
          accept b (slice w s (s+L)) && accept c (slice w (s+L) t) &&
          accept e (slice w (t+L) R++tail)

end REWB.MaskedPeriodic.Text.Regression
