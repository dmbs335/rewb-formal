import REWB.MaskedTraversalExecutePlan
import REWB.MaskedTraversalBandNonempty

/-! The actual suffix trie discharges every band metadata obligation of
the Plan induction. No caller supplies occurrence classes, witnesses,
banks, affected keys, transition maps or masked query answers.
-/
namespace REWB.MaskedTraversalExecute
open REWB.MaskedTraversalAggregate
open REWB.MaskedRunDiscovery (positions)
open REWB.MaskedTraversalPositiveCoverage (Exhausted)
variable {σ h : Nat} {B C E : DFA (Fin σ)}

theorem suffix_preserves (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity : Nat) (hc : capacity=2^h) (hn : text.size<2^h)
    (global : Global C E) (valid : global.Valid text fallback source env) :
    let geometry:=MaskedTraversalDriver.run h (MaskedRunDiscovery.prepareSuffixes text fallback).trie.tree
    let out:=plan env capacity (MaskedTraversalAggregate.prepare C E h) geometry.plan global
    out.Valid text fallback source env geometry.frontier.state capacity 0 ∧
      Effect (positions (MaskedRunDiscovery.prepareSuffixes text fallback).trie.tree) global out.global ∧
      Exhausted B C E text.toList source env.repair.shared.target capacity out.global.answers.history geometry.plan := by
  have capEq : (MaskedOrdered.capacity h).1=capacity:=(MaskedOrdered.capacity_value h).trans hc.symm
  have good : (MaskedRunDiscovery.prepareSuffixes text fallback).trie.tree.Good (ArrayText.read text fallback):=
    (BoundaryTrie.Build.run_correct text fallback (MaskedRunDiscovery.suffixKeys text.size)).2.1
  have metadata : ∀b,(MaskedTraversalDriver.build (h:=h) capacity 0 (MaskedRunDiscovery.prepareSuffixes text fallback).trie.tree).plan.HasBand b→
      MaskedTraversalPositiveCoverage.Metadata text fallback capacity b := by
    intro b hb
    apply MaskedTraversalPositiveCoverage.actual_band_metadata text fallback h capacity hc hn b
    simpa only [MaskedTraversalDriver.run,capEq] using hb
  have hh:=build_preserves text fallback source env hs capacity 0 hc hn (MaskedRunDiscovery.prepareSuffixes text fallback).trie.tree
    good (Nat.zero_le _) (MaskedRunTrieBridge.suffix_positions_nodup text fallback) metadata global valid
  simpa only [MaskedTraversalDriver.run,capEq] using hh

end REWB.MaskedTraversalExecute
