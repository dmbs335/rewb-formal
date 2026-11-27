import REWB.CountedProjection
import REWB.MaskedFiniteActionMaps

/-! Actual finite-orbit compilation for the within-run masked branch.
    The transition is a materialized map on a fixed finite state set.
    Cycle discovery uses `FiniteOrbit.compress`; no periodicity oracle is
    supplied by the caller. All descriptor sizes depend only on the state
    count. The subsequent formula compiler never iterates over a text
    period, cut position, or repetition exponent.
-/
namespace REWB.MaskedPeriodic
open REWB.FiniteOrbit REWB.FiniteRelation
open REWB.AffineProjection REWB.PhaseSolver REWB.UniformProjection
open REWB.MaskedFiniteAction.Maps

structure OrbitData (m : Nat) where
  step : Map m
  initial : Fin m
  accept : Fin m → Bool

def OrbitData.test {m : Nat} (o : OrbitData m) (n : Nat) : Bool :=
  o.accept (orbit o.step.get o.initial n)

def OrbitData.descriptor {m : Nat} (o : OrbitData m) : Descriptor :=
  (compress (finEnum m) o.step.get o.initial o.accept).getD ⟨0,1,[],[]⟩

theorem OrbitData.descriptor_spec {m : Nat} (o : OrbitData m) :
    0<o.descriptor.period ∧ o.descriptor.threshold+o.descriptor.period≤m ∧
    o.descriptor.initialCounts.length+o.descriptor.residues.length≤m ∧
    (∀ r,r∈o.descriptor.residues→r<o.descriptor.period) ∧
    (∀ n,o.descriptor.test n=true ↔ o.test n=true) := by
  obtain ⟨D,hD,hp,hb,hr,ht⟩ := compress_spec (finEnum m) o.step.get o.initial o.accept
  have he : o.descriptor=D := by simp only [OrbitData.descriptor,hD,Option.getD_some]
  rw [he]
  have hs := compress_size (finEnum m) o.step.get o.initial o.accept D hD
  simp only [finEnum,List.length_ofFn] at hb hs
  exact ⟨hp,hb,hs,hr,ht⟩

def OrbitData.formula {m : Nat} (o : OrbitData m) (t : Aff) : Formula :=
  descriptorFormula o.descriptor t

theorem OrbitData.formula_correct {m : Nat} (o : OrbitData m) (t : Aff)
    (env : List Int) (n : Nat) (ht : t.eval env=(n:Int)) :
    Satisfies (o.formula t) env ↔ o.test n=true := by
  obtain ⟨hp,_,_,hr,hc⟩ := o.descriptor_spec
  exact (descriptorFormula_correct o.descriptor t env n ht hp hr).trans (hc n)

theorem OrbitData.formula_good {m : Nat} (o : OrbitData m) (t : Aff) :
    FormulaGood (o.formula t) :=
  descriptorFormula_good o.descriptor t o.descriptor_spec.1

theorem OrbitData.formula_covered {m : Nat} (o : OrbitData m) (t : Aff) :
    Covered (o.formula t) (descriptors m (LiteralShape.aff t)) := by
  obtain ⟨hp,hb,hs,hr,ht⟩ := o.descriptor_spec
  exact covered_descriptor o.descriptor m t hs (by omega)

/-- Before/after contexts are materialized maps. Their contents may
    depend on a period rotation, one joint cut, and the external tail;
    their dimensions and the resulting orbit search space do not. -/
def ofMaps {α : Type} (d : DFA α) (period before after : Map d.stateCount) :
    OrbitData d.stateCount :=
  ⟨period,before.get d.initial,fun state=>d.final (after.get state)⟩

theorem ofMaps_word {α : Type} (d : DFA α) (period before after : Word α)
    (n : Nat) :
    (ofMaps d (wordMap d period) (wordMap d before) (wordMap d after)).test n=true ↔
      d.accepts (before++Periodic.repeatWord period n++after) := by
  have horbit : orbit (wordMap d period).get (d.run d.initial before) n=
      d.run (d.run d.initial before) (Periodic.repeatWord period n) := by
    rw [Periodic.run_repeat]
    congr 2
    funext state
    exact wordMap_get d period state
  simp only [OrbitData.test,ofMaps,wordMap_get,horbit,DFA.accepts,DFA.run_append]

end REWB.MaskedPeriodic
