import REWB.MaskedAllStartFullCostBank
import REWB.MaskedTraversalAggregateWindow

/-! Actual measured source-window clipping. Only the selected boundary
banks are compiled, through the cost-bearing store compiler; persistent
tree replacements and the original query counters are preserved exactly.
-/
namespace REWB.MaskedAllStart.FullCost.Clipping
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {α : Type} {C E : DFA α} {h : Nat}

def atLeader (env : Clip.Env C E) (st : Mutable.Store.State C E) (first old lo hi : Nat)
    (tree : BankTree C E h) : Bank.Result (Clip.Update C E h) :=
  match st.slots[first]?.join with
  | none=>(⟨tree,false,3,0⟩,3)
  | some entry=>
    let ⟨⟨bank,oldWork⟩,fullWork⟩:=Bank.compile C E env.book env.prepared env.cRanges env.eRanges
      st.sources env.target (Clip.config entry.config old lo hi)
    match bank with
    | none=>(⟨tree,false,oldWork+6,1⟩,fullWork+6)
    | some value=>
      let ⟨replaced,replaceWork⟩:=Tree.replace tree first value
      (⟨replaced,true,oldWork+replaceWork+9,1⟩,fullWork+replaceWork+9)

theorem atLeader_value (env : Clip.Env C E) (st : Mutable.Store.State C E) (first old lo hi : Nat)
    (tree : BankTree C E h) :
    (atLeader env st first old lo hi tree).1=Clip.atLeader env st first old lo hi tree := by
  cases hs : st.slots[first]?.join with
  | none=>simp only [atLeader,Clip.atLeader,hs]
  | some entry=>
    simp only [atLeader,Clip.atLeader,hs,Bank.compile_value,Clip.compiled]
    cases hb : (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      st.sources env.target (Clip.config entry.config old lo hi)).1 <;> rfl

theorem atLeader_extra (env : Clip.Env C E) (st : Mutable.Store.State C E) (first old lo hi : Nat)
    (tree : BankTree C E h) :
    (atLeader env st first old lo hi tree).2≤(atLeader env st first old lo hi tree).1.work+
      Bank.extra C E env.prepared.K*(atLeader env st first old lo hi tree).1.calls := by
  rw [atLeader_value]
  cases hs : st.slots[first]?.join with
  | none=>simp only [atLeader,Clip.atLeader,hs,Nat.mul_zero,Nat.add_zero,Nat.le_refl]
  | some entry=>
    have hc:=Bank.compile_extra C E env.book env.prepared env.cRanges env.eRanges
      st.sources env.target (Clip.config entry.config old lo hi)
    simp only [atLeader,Clip.atLeader,hs,Bank.compile_value,Clip.compiled]
    cases hb : (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      st.sources env.target (Clip.config entry.config old lo hi)).1 <;>
      simp only [Nat.mul_one] <;> omega

def step (env : Clip.Env C E) (st : Mutable.Store.State C E) (old lo hi : Nat)
    (acc : Bank.Result (Clip.Update C E h)) (first : Nat) : Bank.Result (Clip.Update C E h) :=
  let ⟨before,total⟩:=acc
  let ⟨one,work⟩:=atLeader env st first old lo hi before.tree
  (⟨one.tree,before.ready && one.ready,before.work+one.work+1,before.calls+one.calls⟩,total+work+1)

theorem fold_value (env : Clip.Env C E) (st : Mutable.Store.State C E) (old lo hi : Nat)
    (keys : List Nat) (acc : Bank.Result (Clip.Update C E h)) :
    (keys.foldl (step env st old lo hi) acc).1=
      keys.foldl (fun before first=>let one:=Clip.atLeader env st first old lo hi before.tree
        ; Clip.Update.mk one.tree (before.ready && one.ready) (before.work+one.work+1) (before.calls+one.calls)) acc.1 := by
  induction keys generalizing acc with
  | nil=>rfl
  | cons first rest ih=>simp only [List.foldl_cons,ih,step,atLeader_value]

theorem fold_extra (env : Clip.Env C E) (st : Mutable.Store.State C E) (old lo hi : Nat)
    (keys : List Nat) (acc : Bank.Result (Clip.Update C E h))
    (ha : acc.2≤acc.1.work+Bank.extra C E env.prepared.K*acc.1.calls) :
    (keys.foldl (step env st old lo hi) acc).2≤
      (keys.foldl (step env st old lo hi) acc).1.work+
        Bank.extra C E env.prepared.K*(keys.foldl (step env st old lo hi) acc).1.calls := by
  induction keys generalizing acc with
  | nil=>exact ha
  | cons first rest ih=>
    apply ih
    have hh:=atLeader_extra env st first old lo hi acc.1.tree
    simp only [step,Nat.mul_add]
    omega

def applyKeys (env : Clip.Env C E) (st : Mutable.Store.State C E) (keys : List Nat) (old lo hi : Nat)
    (tree : BankTree C E h) : Bank.Result (Clip.Update C E h) :=
  keys.foldl (step env st old lo hi) (⟨tree,true,0,0⟩,0)

theorem applyKeys_value (env : Clip.Env C E) (st : Mutable.Store.State C E) (keys : List Nat) (old lo hi : Nat)
    (tree : BankTree C E h) :
    (applyKeys env st keys old lo hi tree).1=Clip.applyKeys env st keys old lo hi tree :=
  fold_value _ _ _ _ _ _ _

theorem applyKeys_extra (env : Clip.Env C E) (st : Mutable.Store.State C E) (keys : List Nat) (old lo hi : Nat)
    (tree : BankTree C E h) :
    (applyKeys env st keys old lo hi tree).2≤(applyKeys env st keys old lo hi tree).1.work+
      Bank.extra C E env.prepared.K*(applyKeys env st keys old lo hi tree).1.calls :=
  fold_extra _ _ _ _ _ _ _ (Nat.zero_le _)

def window (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (tree : BankTree C E h) : Bank.Result (Clip.Window C E h) :=
  if lo<hi then
    let keys:=Clip.plan partition.leaders capacity lo hi
    let ⟨out,work⟩:=applyKeys env st keys.keys old lo hi tree
    (⟨out,keys.lower,keys.work+out.work+2⟩,keys.work+work+2)
  else (⟨⟨tree,false,0,0⟩,lo,1⟩,1)

theorem window_value (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (tree : BankTree C E h) :
    (window env st partition capacity old lo hi tree).1=Clip.window env st partition capacity old lo hi tree := by
  simp only [window,Clip.window,applyKeys_value]
  split <;> rfl

theorem window_extra (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (tree : BankTree C E h) :
    (window env st partition capacity old lo hi tree).2≤
      (window env st partition capacity old lo hi tree).1.work+2*Bank.extra C E env.prepared.K := by
  rw [window_value]
  simp only [window,Clip.window]
  split
  · have hh:=applyKeys_extra env st (Clip.plan partition.leaders capacity lo hi).keys old lo hi tree
    rw [applyKeys_value] at hh
    have hc:=Nat.le_trans (Clip.applyKeys_calls env st (Clip.plan partition.leaders capacity lo hi).keys old lo hi tree)
      (Clip.plan_length partition.leaders capacity lo hi)
    have hm:=Nat.mul_le_mul_left (Bank.extra C E env.prepared.K) hc
    simp only [applyKeys_value]
    rw [Nat.mul_comm (Bank.extra C E env.prepared.K) 2] at hm
    omega
  · simp only; omega

end REWB.MaskedAllStart.FullCost.Clipping
