import REWB.MaskedOrderedOwnerEnumeration

namespace REWB.MaskedOrdered.Owner.Regression
open REWB.BoundaryTrie (Key)

def k0 : Key 6 Nat := ⟨0,4,by decide,0⟩
def k1 : Key 6 Nat := ⟨1,4,by decide,1⟩
def k2 : Key 6 Nat := ⟨2,4,by decide,2⟩

/-- The lower equal-depth node contains a temporary gap-two pair.
The full completed class contains the missing middle occurrence. -/
def refinements : Trie 6 Nat := .node k0 4 (.node k0 4 (.leaf k0) (.leaf k2)) (.leaf k1)

def saved : Store 3 := (run 3 refinements).2

def project (r : Record 3) : Nat×Nat×Option (Nat×Nat)×List Nat :=
  (r.depth,r.owner,r.children,r.state.tree.entries)

theorem equal_depth_owner : saved.nodes[1]?.map project=some (4,0,some (2,3),[0,2]) := by decide

theorem completed_root : saved.nodes[0]?.map project=some (4,0,some (1,4),[0,1,2]) := by decide

theorem fresh_pair_forwarded : (⟨0,(0,2)⟩ : Event)∈saved.events.toList := by decide

def constantText : Array (Fin 2) := #[0,0,0,0,0,0]

theorem stale_pair_rejected :
    (probe (LCEIndex.prepare (ArrayText.read constantText 0) 6)
      (LCEIndex.prepareReverse (ArrayText.read constantText 0) 6) 6 8 saved.nodes ⟨0,(0,2)⟩).1=none := by decide

theorem owner_query_preserves_versions :
    saved.nodes[1]?.map project=some (4,0,some (2,3),[0,2]) ∧
      saved.nodes[0]?.map project=some (4,0,some (1,4),[0,1,2]) :=
  ⟨equal_depth_owner,completed_root⟩

end REWB.MaskedOrdered.Owner.Regression
