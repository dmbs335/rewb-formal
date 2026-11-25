import REWB.MaskedAllStartFullCostUpdates

/-! Measured complete-band repair. Both sparse passes execute the new
cost-bearing compilers; anchor writes and aggregate replacements keep
their original measured implementations. The returned original repair
record is unchanged, while the additional ledger includes formula and
orbit construction inside every selected bank.
-/
namespace REWB.MaskedAllStart.FullCost.Repair
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {α : Type} {C E : DFA α} {h n h' : Nat}

def factor (C E : DFA α) (K : Nat) : Nat := Bank.extra C E K+1

theorem scalar (extra work : Nat) : work≤(extra+1)*work := by
  rw [Nat.add_mul,Nat.one_mul]
  omega

def reset (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) : Bank.Result (MaskedTraversalRepair.Reset C E) :=
  let ⟨fresh,anchorWork⟩:=MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0
  let prior:=st.repairWork
  let ⟨done,bankWork⟩:=Updates.loop (Updates.resetOne env partition capacity L fresh) dirty.keys.positions st
  (⟨fresh,done,anchorWork+(done.repairWork-prior)+4⟩,anchorWork+bankWork+4)

theorem reset_value (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) :
    (reset env partition capacity L anchors dirty st).1=
      MaskedTraversalRepairCoherence.resetBanks env partition capacity L anchors dirty st := by
  simp only [reset,MaskedTraversalRepairCoherence.resetBanks,MaskedTraversalRepair.reset,Updates.resetLoop_value]

theorem reset_work (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) :
    (reset env partition capacity L anchors dirty st).2≤
      factor C E env.shared.prepared.K*(reset env partition capacity L anchors dirty st).1.work := by
  let fresh:=(MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1
  have hb:=Updates.loop_work (Updates.resetOne env partition capacity L fresh) (Bank.extra C E env.shared.prepared.K)
    (Updates.resetOne_charged env partition capacity L fresh)
    (Updates.resetOne_progress env partition capacity L fresh) dirty.keys.positions st
  have hs:=scalar (Bank.extra C E env.shared.prepared.K)
    ((MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).2+4)
  simp only [reset,factor,Nat.mul_add] at hs ⊢
  dsimp only [fresh] at hb
  omega

def apply (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    Bank.Result (MaskedTraversalRepairCoherence.Result C E h) :=
  let ⟨reseted,resetWork⟩:=reset env partition capacity L anchors dirty st
  let contexts:=MaskedTraversalRepairCoherence.contextKeys partition capacity dirty
  let prior:=reseted.store.repairWork
  let ⟨done,contextWork⟩:=Updates.loop (Updates.contextOne env partition capacity L reseted.anchors)
    contexts.keys.positions reseted.store
  let ⟨first,firstWork⟩:=refreshMany done dirty.keys.positions tree
  let ⟨second,secondWork⟩:=refreshMany done contexts.keys.positions first
  (⟨reseted.anchors,done,second,contexts,
      reseted.work+contexts.work+(done.repairWork-prior)+firstWork+secondWork+7⟩,
    resetWork+contexts.work+contextWork+firstWork+secondWork+7)

theorem apply_value (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (apply env partition capacity L anchors dirty st tree).1=
      MaskedTraversalRepairCoherence.apply env partition capacity L anchors dirty st tree := by
  simp only [apply,reset_value,Updates.contextLoop_value,MaskedTraversalRepairCoherence.apply,
    MaskedTraversalRepairCoherence.contextBanks]

theorem apply_work (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (apply env partition capacity L anchors dirty st tree).2≤
      factor C E env.shared.prepared.K*(apply env partition capacity L anchors dirty st tree).1.work := by
  let reseted:=(reset env partition capacity L anchors dirty st).1
  let contexts:=MaskedTraversalRepairCoherence.contextKeys partition capacity dirty
  let done:=(Updates.loop (Updates.contextOne env partition capacity L reseted.anchors)
    contexts.keys.positions reseted.store).1
  let first:=refreshMany done dirty.keys.positions tree
  let second:=refreshMany done contexts.keys.positions first.1
  have hr:=reset_work env partition capacity L anchors dirty st
  have hc:=Updates.loop_work (Updates.contextOne env partition capacity L reseted.anchors)
    (Bank.extra C E env.shared.prepared.K)
    (Updates.contextOne_charged env partition capacity L reseted.anchors)
    (Updates.contextOne_progress env partition capacity L reseted.anchors) contexts.keys.positions reseted.store
  have hs:=scalar (Bank.extra C E env.shared.prepared.K) (contexts.work+first.2+second.2+7)
  change (reset env partition capacity L anchors dirty st).2+contexts.work+
      (Updates.loop (Updates.contextOne env partition capacity L reseted.anchors) contexts.keys.positions reseted.store).2+
      first.2+second.2+7≤
    factor C E env.shared.prepared.K*(reseted.work+contexts.work+(done.repairWork-reseted.store.repairWork)+first.2+second.2+7)
  change (reset env partition capacity L anchors dirty st).2≤factor C E env.shared.prepared.K*reseted.work at hr
  change (Updates.loop (Updates.contextOne env partition capacity L reseted.anchors) contexts.keys.positions reseted.store).2≤
    factor C E env.shared.prepared.K*(done.repairWork-reseted.store.repairWork) at hc
  change contexts.work+first.2+second.2+7≤factor C E env.shared.prepared.K*(contexts.work+first.2+second.2+7) at hs
  simp only [Nat.mul_add] at hs ⊢
  omega

end REWB.MaskedAllStart.FullCost.Repair
