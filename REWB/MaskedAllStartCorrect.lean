import REWB.MaskedAllStart
import REWB.MaskedTraversalExecuteSuffix

/-! Exact original maskedStart semantics of the public actual solver.
All preparations, bands, repairs, cut queries, outputs and erasures are
executed by solve. Completeness combines the initial empty/periodic
branch with actual exhaustion of every positive suffix-trie band.
This is a functional-correctness theorem; the full running-time theorem
still requires the separately tracked operation/cost obligations.
-/
namespace REWB.MaskedAllStart
open REWB.MaskedTraversalExecute
variable {σ : Nat}

theorem solve_preserves (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    let prepared:=prepare B C E text fallback source target
    let out:=(solve B C E text fallback source target).output
    out.Valid text fallback source prepared.env prepared.geometry.frontier.state prepared.template.capacity 0 ∧
      Effect (MaskedRunDiscovery.positions (MaskedRunDiscovery.prepareSuffixes text fallback).trie.tree) prepared.global out.global ∧
      MaskedTraversalPositiveCoverage.Exhausted B C E text.toList source target prepared.template.capacity
        out.global.answers.history prepared.geometry.plan := by
  have hh:=suffix_preserves text fallback source (prepare B C E text fallback source target).env
    (prepare_static B C E text fallback source target) (prepare B C E text fallback source target).template.capacity
    (prepare_capacity B C E text fallback source target) (MaskedSuffixClass.height_capacity text.size)
    (prepare B C E text fallback source target).global (prepare_global B C E text fallback source target)
  simpa only [solve_output,prepare_geometry,prepare_target] using hh

/-- The caller supplies only the automata, finite text and independent
source/target masks. Short masks read false; arbitrary nonperiodic target
masks are allowed. No index correctness or answer premise remains. -/
theorem solve_correct (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (p : Nat) :
    MaskedProgression.readMask (solve B C E text fallback source target).bits p=true ↔
      MaskedProgression.readMask source p=true ∧ Spec.maskedStart B C E text.toList (MaskedProgression.readMask target) p := by
  have preserved:=solve_preserves B C E text fallback source target
  have valid : MaskedTraversalAnswers.Valid text.size
      (fun p=>MaskedProgression.readMask source p=true ∧ Spec.maskedStart B C E text.toList (MaskedProgression.readMask target) p)
      (solve B C E text fallback source target).output.global.answers := preserved.1.global.answers
  have history : ∀p,p∈(MaskedTraversalInitial.start B C E text fallback source target
        (MaskedCluster.modulus C.stateCount E.stateCount)).answers.history→
      p∈(solve B C E text fallback source target).output.global.answers.history := preserved.2.1.history
  have done : MaskedTraversalPositiveCoverage.Exhausted B C E text.toList source target
      (prepare B C E text fallback source target).template.capacity
      (solve B C E text fallback source target).output.global.answers.history
      (MaskedTraversalDriver.run (MaskedSuffixClass.height text.size) (MaskedRunDiscovery.prepareSuffixes text fallback).trie.tree).plan :=
    preserved.2.2
  exact MaskedTraversalPositiveCoverage.answers_correct B C E text fallback source target
    (MaskedCluster.modulus C.stateCount E.stateCount) (MaskedSuffixClass.height text.size)
    (prepare B C E text fallback source target).template.capacity (prepare_capacity B C E text fallback source target)
    (MaskedSuffixClass.height_capacity text.size) (solve B C E text fallback source target).output.global.answers
    valid history done p

theorem solve_size (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : (solve B C E text fallback source target).bits.size=text.size+1 :=
  (solve_preserves B C E text fallback source target).1.global.answers.size

theorem solve_count (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : (solve B C E text fallback source target).output.global.answers.count≤text.size+1 :=
  (solve_preserves B C E text fallback source target).1.global.answers.count_le

theorem solve_nodup (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : (solve B C E text fallback source target).output.global.answers.history.Nodup :=
  (solve_preserves B C E text fallback source target).1.global.answers.nodup

theorem solve_sources_valid (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : MaskedMutableProgression.Batch.Valid source
      (solve B C E text fallback source target).output.global.answers.history
      (solve B C E text fallback source target).output.global.store.sources :=
  (solve_preserves B C E text fallback source target).1.global.sources

end REWB.MaskedAllStart
