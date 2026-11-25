import REWB.MaskedTraversalRepairTransportShorten

namespace REWB.MaskedTraversalRepairTransport.Regression
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate

def D : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩

example : Cells.Unclipped 7
    ((List.replicate 8 (none : Option (Mutable.Store.Entry D D))).map
      (Cells.reindexedEntry (ReplayMaps.one 1 1) 0)) := by
  apply reindexed_unclipped
  intro first entry he
  simp only [List.getElem?_replicate] at he
  split at he <;> cases he

example (z : ReplayMaps.Value 1 1) (fresh : Nat) (entry : Mutable.Store.Entry D D) :
    (entryAt z fresh entry).config.window=entry.config.window := rfl

example (z : ReplayMaps.Value 1 1) (fresh : Nat) (entry : Mutable.Store.Entry D D) :
    (entryAt z fresh entry).config.anchor=entry.config.anchor := rfl

example (capacity length : Nat) (s : MaskedClusterLeaders.State h) :
    (MaskedClusterLeaders.shorten capacity length s).state.occurrences=s.occurrences := rfl

end REWB.MaskedTraversalRepairTransport.Regression
