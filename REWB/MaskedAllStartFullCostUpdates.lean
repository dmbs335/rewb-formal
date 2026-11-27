import REWB.MaskedAllStartFullCostBank
import REWB.MaskedTraversalRepairCoherence

/-! New implementation of sparse measured bank updates after the
2026-11-25 environment interruption. The generic loop is instantiated
below with actual leader-reset and successor-context compilers. Its
credit proof uses the real returned repairWork increments; it does not
accept a caller-supplied bank or answer oracle. -/
namespace REWB.MaskedAllStart.FullCost.Updates
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h n h' : Nat}

abbrev Store (C E : DFA α) := Mutable.Store.State C E

def write (compiled : Store C E→Bank.Result (Option (Mutable.Store.Entry C E)×Nat))
    (first : Nat) (st : Store C E) : Bank.Result (Store C E) :=
  let ⟨⟨entry,oldWork⟩,fullWork⟩:=compiled st
  ({st with
      slots:=st.slots.setIfInBounds first entry
      repairWork:=st.repairWork+oldWork+5
      rebuilds:=st.rebuilds+1
      writes:=st.writes+1},fullWork+5)

theorem write_charged (compiled : Store C E→Bank.Result (Option (Mutable.Store.Entry C E)×Nat))
    (extra first : Nat) (st : Store C E)
    (hc : (compiled st).2≤(compiled st).1.2+extra) :
    (write compiled first st).2+st.repairWork≤(write compiled first st).1.repairWork+extra := by
  have hh:=Nat.add_le_add_right (Nat.add_le_add_left hc st.repairWork) 5
  simpa only [write,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem write_progress (compiled : Store C E→Bank.Result (Option (Mutable.Store.Entry C E)×Nat))
    (first : Nat) (st : Store C E) :
    st.repairWork+1≤(write compiled first st).1.repairWork := by
  simp only [write]
  omega

def loop (step : Nat→Store C E→Bank.Result (Store C E)) : List Nat→Store C E→Bank.Result (Store C E)
  | [],st=>({st with repairWork:=st.repairWork+1},1)
  | first::rest,st=>
    let ⟨next,work⟩:=step first st
    let ⟨done,later⟩:=loop step rest {next with repairWork:=next.repairWork+3}
    (done,work+3+later)

theorem loop_credit (step : Nat→Store C E→Bank.Result (Store C E)) (extra : Nat)
    (hc : ∀first st,(step first st).2+st.repairWork≤(step first st).1.repairWork+extra)
    (keys : List Nat) (st : Store C E) :
    (loop step keys st).2+st.repairWork≤(loop step keys st).1.repairWork+extra*keys.length := by
  induction keys generalizing st with
  | nil=>
    simp only [loop,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
  | cons first rest ih=>
    have hs:=hc first st
    have ht:=ih {(step first st).1 with repairWork:=(step first st).1.repairWork+3}
    simp only [loop,List.length_cons,Nat.mul_add,Nat.mul_one]
    dsimp only at ht
    omega

theorem loop_progress (step : Nat→Store C E→Bank.Result (Store C E))
    (hp : ∀first st,st.repairWork+1≤(step first st).1.repairWork)
    (keys : List Nat) (st : Store C E) :
    st.repairWork+keys.length≤(loop step keys st).1.repairWork := by
  induction keys generalizing st with
  | nil=>
    simp only [loop,List.length_nil,Nat.add_zero]
    omega
  | cons first rest ih=>
    have hs:=hp first st
    have ht:=ih {(step first st).1 with repairWork:=(step first st).1.repairWork+3}
    simp only [loop,List.length_cons]
    dsimp only at ht
    omega

theorem loop_work (step : Nat→Store C E→Bank.Result (Store C E)) (extra : Nat)
    (hc : ∀first st,(step first st).2+st.repairWork≤(step first st).1.repairWork+extra)
    (hp : ∀first st,st.repairWork+1≤(step first st).1.repairWork)
    (keys : List Nat) (st : Store C E) :
    (loop step keys st).2≤(extra+1)*((loop step keys st).1.repairWork-st.repairWork) := by
  have hcredit:=loop_credit step extra hc keys st
  have hprogress:=loop_progress step hp keys st
  have hlen : keys.length≤(loop step keys st).1.repairWork-st.repairWork := by omega
  have hh:=Nat.mul_le_mul_left extra hlen
  simp only [Nat.add_mul,Nat.one_mul]
  omega

def resetOne (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (first : Nat) (st : Store C E) : Bank.Result (Store C E) :=
  write (fun before=>Bank.readyCompile C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity first L anchors env.window env.catalog env.classes before.sources env.shared.target) first st

theorem resetOne_value (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (first : Nat) (st : Store C E) :
    (resetOne env partition capacity L anchors first st).1=
      MaskedTraversalBankReady.write C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
        partition capacity first L anchors env.window env.catalog env.classes env.shared.target st := by
  simp only [resetOne,write,Bank.readyCompile_value,MaskedTraversalBankReady.write]

theorem resetOne_charged (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (first : Nat) (st : Store C E) :
    (resetOne env partition capacity L anchors first st).2+st.repairWork≤
      (resetOne env partition capacity L anchors first st).1.repairWork+Bank.extra C E env.shared.prepared.K := by
  apply write_charged
  simpa only [Bank.readyCompile_value] using
    Bank.readyCompile_extra C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
      partition capacity first L anchors env.window env.catalog env.classes st.sources env.shared.target

theorem resetOne_progress (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (first : Nat) (st : Store C E) :
    st.repairWork+1≤(resetOne env partition capacity L anchors first st).1.repairWork :=
  write_progress _ first st

theorem resetLoop_value (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (keys : List Nat) (st : Store C E) :
    (loop (resetOne env partition capacity L anchors) keys st).1=
      MaskedTraversalRepair.banksLoop C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
        partition capacity L anchors env.window env.catalog env.classes env.shared.target keys st := by
  induction keys generalizing st with
  | nil=>rfl
  | cons first rest ih=>
    simp only [loop,MaskedTraversalRepair.banksLoop,ih,resetOne_value]

def contextOne (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (first : Nat) (st : Store C E) : Bank.Result (Store C E) :=
  write (fun before=>Bank.contextCompile C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity first L anchors env.shared.target before) first st

theorem contextOne_value (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (first : Nat) (st : Store C E) :
    (contextOne env partition capacity L anchors first st).1=
      MaskedTraversalContext.write C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
        partition capacity first L anchors env.shared.target st := by
  simp only [contextOne,write,Bank.contextCompile_value,MaskedTraversalContext.write]

theorem contextOne_charged (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (first : Nat) (st : Store C E) :
    (contextOne env partition capacity L anchors first st).2+st.repairWork≤
      (contextOne env partition capacity L anchors first st).1.repairWork+Bank.extra C E env.shared.prepared.K := by
  apply write_charged
  simpa only [Bank.contextCompile_value] using
    Bank.contextCompile_extra C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
      partition capacity first L anchors env.shared.target st

theorem contextOne_progress (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (first : Nat) (st : Store C E) :
    st.repairWork+1≤(contextOne env partition capacity L anchors first st).1.repairWork :=
  write_progress _ first st

theorem contextLoop_value (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (keys : List Nat) (st : Store C E) :
    (loop (contextOne env partition capacity L anchors) keys st).1=
      MaskedTraversalContext.applyLoop C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
        partition capacity L anchors env.shared.target keys st := by
  induction keys generalizing st with
  | nil=>rfl
  | cons first rest ih=>
    simp only [loop,MaskedTraversalContext.applyLoop,ih,contextOne_value]

end REWB.MaskedAllStart.FullCost.Updates
