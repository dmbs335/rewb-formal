import REWB.MaskedTraversalAggregateClipPlan
import REWB.MaskedTraversalContextStored

/-! Actual temporary source-window clipping. At most two real stored
leader banks are compiled with the current length and a new source
window. Their descriptors, incoming contexts, local anchors, run IDs and
immutable target counts are retained. Neither the source store nor the
permanent aggregate is modified. Missing/inconsistent banks reject the
query instead of silently replacing a physical block with identity.
-/
namespace REWB.MaskedTraversalAggregate.Clip
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {h : Nat}

structure Env (C E : DFA α) where
  book : ReplayMaps.Prepared C.stateCount E.stateCount
  prepared : Prepared C.stateCount E.stateCount
  cRanges : BoundaryApplication.Range.Index C
  eRanges : BoundaryApplication.Range.Index E
  target : Array Bool

def config (cfg : Mutable.Store.Config) (old lo hi : Nat) : Mutable.Store.Config :=
  {cfg with length:=old,window:=⟨true,lo,hi⟩}

theorem config_anchor (cfg : Mutable.Store.Config) (old lo hi : Nat) :
    (config cfg old lo hi).anchor=cfg.anchor ∧ (config cfg old lo hi).incoming=cfg.incoming ∧
      (config cfg old lo hi).runId=cfg.runId ∧ (config cfg old lo hi).targetCounts=cfg.targetCounts :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem config_runBacked (sources : Mutable.Batch.Sources) (target : Array Bool) (K : Nat)
    (cfg : Mutable.Store.Config) (old lo hi : Nat)
    (hr : MaskedTraversalContext.RunBacked sources target K cfg) :
    MaskedTraversalContext.RunBacked sources target K (config cfg old lo hi) := hr

def compiled (env : Env C E) (st : Mutable.Store.State C E) (cfg : Mutable.Store.Config) :
    Option (Mutable.Store.Bank C E)×Nat :=
  Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges st.sources env.target cfg

structure Update (C E : DFA α) (h : Nat) where
  tree : BankTree C E h
  ready : Bool
  work : Nat
  calls : Nat

def atLeader (env : Env C E) (st : Mutable.Store.State C E) (first old lo hi : Nat)
    (tree : BankTree C E h) : Update C E h :=
  match st.slots[first]?.join with
  | none => ⟨tree,false,3,0⟩
  | some entry =>
    let bank:=compiled env st (config entry.config old lo hi)
    match bank.1 with
    | none => ⟨tree,false,bank.2+6,1⟩
    | some value =>
      let replaced:=Tree.replace tree first value
      ⟨replaced.1,true,bank.2+replaced.2+9,1⟩

/-- The selected actual compiler counter, used only to state accounting. -/
def selectedWork (env : Env C E) (st : Mutable.Store.State C E) (first old lo hi : Nat) : Nat :=
  match st.slots[first]?.join with
  | none => 0
  | some entry => (compiled env st (config entry.config old lo hi)).2

theorem atLeader_good (env : Env C E) (st : Mutable.Store.State C E) (first old lo hi : Nat)
    (tree : BankTree C E h) (hg : tree.Good) : (atLeader env st first old lo hi tree).tree.Good := by
  cases he : st.slots[first]?.join with
  | none => simpa only [atLeader,he] using hg
  | some entry =>
    cases hb : (compiled env st (config entry.config old lo hi)).1 with
    | none => simpa only [atLeader,he,hb] using hg
    | some bank => simpa only [atLeader,he,hb] using Tree.replace_good tree hg first bank

theorem atLeader_calls (env : Env C E) (st : Mutable.Store.State C E) (first old lo hi : Nat)
    (tree : BankTree C E h) : (atLeader env st first old lo hi tree).calls≤1 := by
  cases he : st.slots[first]?.join with
  | none => simp only [atLeader,he]; exact Nat.zero_le 1
  | some entry =>
    cases hb : (compiled env st (config entry.config old lo hi)).1 <;>
      simp only [atLeader,he,hb,Nat.le_refl]

theorem atLeader_work (env : Env C E) (st : Mutable.Store.State C E) (first old lo hi : Nat)
    (tree : BankTree C E h) :
    (atLeader env st first old lo hi tree).work≤selectedWork env st first old lo hi+
      (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
        (2*(MaskedClusterStage.dfa C E).stateCount)+9 := by
  cases he : st.slots[first]?.join with
  | none => simp only [atLeader,selectedWork,he]; omega
  | some entry =>
    cases hb : (compiled env st (config entry.config old lo hi)).1 with
    | none => simp only [atLeader,selectedWork,he,hb]; omega
    | some bank =>
      have hr:=Tree.replace_steps tree first bank
      simp only [atLeader,selectedWork,he,hb]
      omega

theorem atLeader_cells (env : Env C E) (st : Mutable.Store.State C E) (first old lo hi : Nat)
    (tree : BankTree C E h) (ok : (atLeader env st first old lo hi tree).ready=true) :
    ∃entry bank,st.slots[first]?.join=some entry ∧
      (compiled env st (config entry.config old lo hi)).1=some bank ∧
      (atLeader env st first old lo hi tree).tree.leaves=tree.leaves.set first bank.view := by
  cases he : st.slots[first]?.join with
  | none => simp only [atLeader,he] at ok; cases ok
  | some entry =>
    cases hb : (compiled env st (config entry.config old lo hi)).1 with
    | none => simp only [atLeader,he,hb] at ok; cases ok
    | some bank =>
      exact ⟨entry,bank,rfl,hb,by simp only [atLeader,he,hb,Tree.replace_leaves]⟩

def applyKeys (env : Env C E) (st : Mutable.Store.State C E) (keys : List Nat) (old lo hi : Nat)
    (tree : BankTree C E h) : Update C E h :=
  keys.foldl (fun acc first=>
    let one:=atLeader env st first old lo hi acc.tree
    ⟨one.tree,acc.ready && one.ready,acc.work+one.work+1,acc.calls+one.calls⟩)
    ⟨tree,true,0,0⟩

theorem applyKeys_good (env : Env C E) (st : Mutable.Store.State C E) (keys : List Nat) (old lo hi : Nat)
    (tree : BankTree C E h) (hg : tree.Good) : (applyKeys env st keys old lo hi tree).tree.Good := by
  have go : ∀(ps : List Nat) (acc : Update C E h),acc.tree.Good→
      (ps.foldl (fun acc first=>let one:=atLeader env st first old lo hi acc.tree
        ; Update.mk one.tree (acc.ready && one.ready) (acc.work+one.work+1) (acc.calls+one.calls)) acc).tree.Good := by
    intro ps
    induction ps with
    | nil => intro acc hv; exact hv
    | cons first ps ih => intro acc hv; exact ih _ (atLeader_good env st first old lo hi acc.tree hv)
  exact go keys _ hg

theorem applyKeys_calls (env : Env C E) (st : Mutable.Store.State C E) (keys : List Nat) (old lo hi : Nat)
    (tree : BankTree C E h) : (applyKeys env st keys old lo hi tree).calls≤keys.length := by
  have go : ∀(ps : List Nat) (acc : Update C E h),
      (ps.foldl (fun acc first=>let one:=atLeader env st first old lo hi acc.tree
        ; Update.mk one.tree (acc.ready && one.ready) (acc.work+one.work+1) (acc.calls+one.calls)) acc).calls≤acc.calls+ps.length := by
    intro ps
    induction ps with
    | nil => intro acc; simp only [List.foldl_nil,List.length_nil,Nat.add_zero,Nat.le_refl]
    | cons first ps ih =>
      intro acc
      have hh:=ih (Update.mk (atLeader env st first old lo hi acc.tree).tree
        (acc.ready && (atLeader env st first old lo hi acc.tree).ready)
        (acc.work+(atLeader env st first old lo hi acc.tree).work+1)
        (acc.calls+(atLeader env st first old lo hi acc.tree).calls))
      have hc:=atLeader_calls env st first old lo hi acc.tree
      simp only [List.foldl_cons,List.length_cons]
      dsimp only at hh
      omega
  simpa only [applyKeys,Nat.zero_add] using go keys (Update.mk tree true 0 0)

structure Window (C E : DFA α) (h : Nat) where
  update : Update C E h
  lower : Nat
  work : Nat

def window (env : Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (tree : BankTree C E h) : Window C E h :=
  if lo<hi then
    let keys:=plan partition.leaders capacity lo hi
    let out:=applyKeys env st keys.keys old lo hi tree
    ⟨out,keys.lower,keys.work+out.work+2⟩
  else ⟨⟨tree,false,0,0⟩,lo,1⟩

theorem window_good (env : Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (tree : BankTree C E h) (hg : tree.Good) : (window env st partition capacity old lo hi tree).update.tree.Good := by
  unfold window
  split
  · exact applyKeys_good env st _ old lo hi tree hg
  · exact hg

theorem window_calls (env : Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (tree : BankTree C E h) : (window env st partition capacity old lo hi tree).update.calls≤2 := by
  unfold window
  split
  · exact Nat.le_trans (applyKeys_calls env st _ old lo hi tree) (plan_length _ _ _ _)
  · exact Nat.zero_le 2

end REWB.MaskedTraversalAggregate.Clip
