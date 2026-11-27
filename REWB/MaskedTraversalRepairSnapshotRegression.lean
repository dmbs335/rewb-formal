import REWB.MaskedTraversalRepairSnapshotCost

namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster
variable {α : Type} {C E : DFA α} {h σ : Nat}

/-- Initial constructed snapshots satisfy the more general contract;
later erasures need preserve only its actual source/run facts. -/
theorem Setup.snapshot {text : Array (Fin σ)} {fallback : Fin σ} {source : Array Bool} {removed : List Nat}
    {env : Env C E text.size (MaskedSuffixClass.height text.size)}
    {partition : MaskedClusterLeaders.State h} {capacity L base : Nat} {st : Mutable.Store.State C E}
    (hs : Setup text fallback source removed env partition capacity L base st) :
    Snapshot text fallback source removed env partition capacity L base st := by
  refine ⟨hs.catalog,hs.classes,hs.valid,?_,hs.modulus,?_,hs.invariant,hs.capacity_eq,hs.complete,hs.positive,hs.slot_size⟩
  · rw [hs.sources]
    exact MaskedMutableProgression.Batch.eraseMany_n removed _
  · rw [hs.sources]
    exact MaskedMutableProgression.Batch.eraseMany_runs removed _

end REWB.MaskedTraversalRepairCoherence
