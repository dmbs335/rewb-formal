import REWB.MaskedTraversalDriverCost
import REWB.MaskedTraversalDriverCoverage
import REWB.MaskedTraversalEdgeRegression

namespace REWB.MaskedTraversalDriver.Regression
open REWB.BoundaryTrie REWB.MaskedRunDiscovery

/-- Binary refinement of the suffix trie of 0101. The two depth-zero
nodes distinguish the empty suffix and the two first-letter branches. -/
def sample : Tree 4 Nat :=
  .node (suffixKey 4 4) 0 (.leaf (suffixKey 4 4))
    (.node (suffixKey 4 2) 0
      (.node (suffixKey 4 2) 2 (.leaf (suffixKey 4 2)) (.leaf (suffixKey 4 0)))
      (.node (suffixKey 4 3) 1 (.leaf (suffixKey 4 3)) (.leaf (suffixKey 4 1))))

/-- Bounded regression reference; not used by the geometric driver. -/
def rows : Plan h→List (Nat×Nat×List Nat)
  | .empty s => s.lowered.edge.path.bands.map (fun b=>(b.lo,b.hi,b.snapshot.occurrences.entries))
  | .leaf _ _ s => s.lowered.edge.path.bands.map (fun b=>(b.lo,b.hi,b.snapshot.occurrences.entries))
  | .node l r _ s => rows l++rows r++s.lowered.edge.path.bands.map
      (fun b=>(b.lo,b.hi,b.snapshot.occurrences.entries))

def top : Plan h→Step h
  | .empty s => s
  | .leaf _ _ s => s
  | .node _ _ _ s => s

theorem equal_depth_root : (top (run 3 sample).plan).lowered.edge.path.bands=[] := rfl

def text : Array (Fin 2) := #[0,1,0,1]

theorem actual_suffix_coverage (p : Fin 5) (L : Nat) (hl : 0<L) (hh : L≤4-p.val) :
    ∃b,(run 3 (prepareSuffixes text 0).trie.tree).plan.HasBand b ∧
      b.lo≤L ∧ L≤b.hi ∧ p.val∈b.snapshot.occurrences.entries :=
  suffix_cover text 0 3 (by decide) p L hl hh

theorem actual_suffix_balance :
    (run 3 (prepareSuffixes text 0).trie.tree).popped+
      (run 3 (prepareSuffixes text 0).trie.tree).discarded+
      MaskedThresholdQueue.count (run 3 (prepareSuffixes text 0).trie.tree).frontier.state.queue=
      (run 3 (prepareSuffixes text 0).trie.tree).generated := by
  have hg:=(Build.run_correct text 0 (suffixKeys text.size)).2.1
  exact (build_measured (MaskedOrdered.capacity 3).1 0 _ _ hg
    (MaskedOrdered.capacity_value 3) (by decide) (Nat.zero_le _)).balance

end REWB.MaskedTraversalDriver.Regression
