import REWB.MaskedTraversalIncomingConfig

namespace REWB.MaskedTraversalIncoming.Regression
open REWB.MaskedTraversalBankReady

def before : MaskedClusterLeaders.State 7 :=
  (MaskedClusterLeaders.execute 7 4
    [.insert 0,.insert 2,.insert 10,.insert 12,.insert 20,.insert 22,.insert 30,.insert 32,
     .insert 40,.insert 42,.insert 50,.insert 52,.insert 60,.insert 62]).state

def after : MaskedClusterLeaders.State 7 := (MaskedClusterLeaders.add 128 4 11 before).state

def dirty : MaskedTraversalDirty.Marked 7 :=
  MaskedTraversalDirty.markChange before.leaders after.leaders 128 11 (MaskedTraversalDirty.empty 7)

def contexts : MaskedTraversalDirty.Marked 7 :=
  MaskedTraversalContext.successors after.leaders 128 dirty.keys.positions (MaskedTraversalDirty.empty 7)

def anchors : Array (Option Nat) := (Array.replicate 65 (some 4)).setIfInBounds 30 (some 9)

def resetAnchors : Array (Option Nat) :=
  (MaskedTraversalRepair.anchorsLoop 4 dirty.keys.positions anchors 0).1

theorem successor_only_refresh_is_needed :
    40∉dirty.keys.positions ∧ 40∈contexts.keys.positions ∧
      (incoming before 128 40 4 anchors).enabled=true ∧
      (incoming after 128 40 4 resetAnchors).enabled=false := by decide

theorem distant_cursor_retained :
    50∉contexts.keys.positions ∧
      (incoming before 128 50 4 anchors).cursor=(incoming after 128 50 4 resetAnchors).cursor ∧
      (incoming before 128 50 4 anchors).enabled=(incoming after 128 50 4 resetAnchors).enabled := by decide

end REWB.MaskedTraversalIncoming.Regression
