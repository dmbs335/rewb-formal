import REWB.MaskedTraversalRepairTransport
import REWB.MaskedTraversalAggregateWindowMarks

/-! Full source windows survive actual permanent bank repair. Primary
resets use the shared environment's full window. Successor refreshes keep
the existing window, including when its raw length is older. Temporary
report clipping is never written back into the permanent model.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h n h' : Nat}

theorem refreshBank_window (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L p first : Nat) (anchors : Array (Option Nat))
    (entry : Mutable.Store.Entry C E)
    (he : (refreshBank env partition capacity L p anchors st).slots[first]?.join=some entry) :
    ∃old,st.slots[first]?.join=some old ∧ entry.config.window=old.config.window := by
  by_cases hp : p=first
  · subst p
    change ((st.slots.setIfInBounds first _)[first]?).join=some entry at he
    rw [Array.getElem?_setIfInBounds_self] at he
    split at he
    · simp only [Option.join] at he
      obtain ⟨old,hs,_,hc,_⟩:=MaskedTraversalContext.compile_selected C E env.book env.prepared env.cRanges env.eRanges
        partition capacity first L anchors env.target st entry he
      exact ⟨old,hs,by rw [hc]; rfl⟩
    · cases he
  · have hh:=MaskedTraversalContext.write_other C E env.book env.prepared env.cRanges env.eRanges
      partition capacity p first L anchors env.target st hp
    exact ⟨entry,by simpa only [refreshBank,hh] using he,rfl⟩

theorem refreshLoop_window (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L first : Nat) (anchors : Array (Option Nat))
    (ps : List Nat) (entry : Mutable.Store.Entry C E)
    (he : (refreshLoop env partition capacity L anchors ps st).slots[first]?.join=some entry) :
    ∃old,st.slots[first]?.join=some old ∧ entry.config.window=old.config.window := by
  induction ps generalizing st with
  | nil => exact ⟨entry,he,rfl⟩
  | cons p ps ih =>
    obtain ⟨middle,hm,hw⟩:=ih _ he
    obtain ⟨old,hs,hw'⟩:=refreshBank_window env st partition capacity L p first anchors middle hm
    exact ⟨old,hs,hw.trans hw'⟩

theorem resetBanks_window (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (hp : first∈dirty.keys.positions) (entry : Mutable.Store.Entry C E)
    (he : (resetBanks env partition capacity L anchors dirty st).store.slots[first]?.join=some entry) :
    entry.config.window=env.window := by
  have hb:=slot_bound _ first entry he
  rw [resetBanks_size] at hb
  have hcompile:=(resetBanks_compiled env partition capacity L first anchors dirty st hp hb).symm.trans he
  have hprep:=(MaskedTraversalBankReady.compile_selected C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity first L _ env.window env.catalog env.classes st.sources env.shared.target entry hcompile).1
  exact (prepare_descriptor partition capacity first L _ env.window env.catalog env.classes entry.config hprep).2.2.2.2.2

theorem apply_unclipped (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L size : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (tree : BankTree C E h) (entries : List (Option (Mutable.Store.Entry C E)))
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hp : Pending env partition capacity L anchors dirty st entries)
    (hw : env.window=⟨true,0,size+1⟩) (hu : Cells.Unclipped size entries) :
    Cells.Unclipped size (model env partition capacity L anchors dirty st tree entries) := by
  intro first entry he
  have hb:=(List.getElem?_eq_some_iff.mp he).1
  rw [model_length] at hb
  rw [model_get env partition capacity L anchors dirty st tree entries first hb] at he
  by_cases hsel : first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions
  · simp only [if_pos hsel,Option.some.injEq] at he
    obtain ⟨middle,hm,hwindows⟩:=refreshLoop_window env.shared (resetBanks env partition capacity L anchors dirty st).store
      partition capacity L first (resetBanks env partition capacity L anchors dirty st).anchors
      (contextKeys partition capacity dirty).keys.positions entry he
    rw [hwindows]
    by_cases hprimary : first∈dirty.keys.positions
    · exact (resetBanks_window env partition capacity L first anchors dirty st hprimary middle hm).trans hw
    · have hcontext:=hsel.resolve_left hprimary
      have hleader:=contextKeys_member partition capacity L first dirty hi hc hcontext
      obtain ⟨old,hold⟩:=hp.complete first hleader hprimary
      obtain ⟨raw,hraw,hcfg⟩:=(hp.coherent first hprimary old hold).raw
      rw [resetBanks_other env partition capacity L first anchors dirty st hprimary] at hm
      have heq : middle=raw := Option.some.inj (hm.symm.trans hraw)
      subst middle
      have hwin:=congrArg Mutable.Store.Config.window hcfg
      exact hwin.trans (hu first old hold)
  · simp only [if_neg hsel] at he
    exact hu first entry he

end REWB.MaskedTraversalRepairCoherence
