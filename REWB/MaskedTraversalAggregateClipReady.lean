import REWB.MaskedTraversalAggregateMeaning

/-! Actual complete leader slots guarantee that both boundary compilers
and the temporary window aggregate are ready. Window and current-length
changes cannot alter the compiler's run/index availability guards.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h : Nat}

theorem clipped_presence (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (cfg : Mutable.Store.Config) (old lo hi : Nat) :
    (Clip.compiled env st (Clip.config cfg old lo hi)).1.isSome=(Clip.compiled env st cfg).1.isSome := by
  unfold Clip.compiled
  by_cases hm : cfg.descriptor.repetitions=0
  · simp only [Mutable.Store.compile,Clip.config,hm,if_true,Option.isSome_some]
  · simp only [Mutable.Store.compile,Clip.config,hm,if_false]
    cases hid : cfg.runId with
    | none=>rfl
    | some id=>
      simp only
      cases hrun : st.sources.runs[id]? with
      | none=>rfl
      | some run=>
        simp only
        by_cases hr : run.period=cfg.descriptor.period ∧ run.lo≤cfg.descriptor.first ∧
            cfg.descriptor.last+cfg.anchor≤run.hi+1
        · simp only [hr,true_and,if_true,Mutable.Batch.compileRun]
          by_cases hK : st.sources.modulus=env.prepared.K
          · simp only [hK,if_true,hrun]
            cases hidx : st.sources.indexes[id]? <;> simp only [Option.isSome_none,Option.isSome_some]
          · simp only [hK,if_false]
        · simp only [hr,if_false]

theorem clippedEntry_present (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old first lo hi : Nat)
    (entry : Mutable.Store.Entry C E) (hh : EntryState env st partition capacity old first entry) :
    ∃next,clippedEntry env st first old lo hi=some next ∧
      next.config=Clip.config entry.config old lo hi ∧
      Current env st partition capacity old first next := by
  obtain ⟨before,hs,hn⟩:=hh.raw
  have hp:=clipped_presence env st entry.config old lo hi
  rw [hh.compiled] at hp
  have hcfg : Clip.config before.config old lo hi=Clip.config entry.config old lo hi := by rw [←hn]; rfl
  cases hb : (Clip.compiled env st (Clip.config entry.config old lo hi)).1 with
  | none=>simp only [hb,Option.isSome_none,Option.isSome_some] at hp; cases hp
  | some bank=>
    refine ⟨⟨Clip.config entry.config old lo hi,bank⟩,?_,rfl,⟨hh.descriptor,rfl,hb⟩⟩
    simp only [clippedEntry,hs,Option.bind,hcfg,hb,Option.map]

theorem atLeader_ready (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old first lo hi : Nat)
    (entry : Mutable.Store.Entry C E) (hh : EntryState env st partition capacity old first entry)
    (tree : BankTree C E h) : (Clip.atLeader env st first old lo hi tree).ready=true := by
  obtain ⟨before,hs,hn⟩:=hh.raw
  have hp:=clipped_presence env st entry.config old lo hi
  rw [hh.compiled] at hp
  have hcfg : Clip.config before.config old lo hi=Clip.config entry.config old lo hi := by rw [←hn]; rfl
  simp only [Clip.atLeader,hs,hcfg]
  cases hb : (Clip.compiled env st (Clip.config entry.config old lo hi)).1 with
  | none=>simp only [hb,Option.isSome_none,Option.isSome_some] at hp; cases hp
  | some bank=>rfl

theorem applyKeys_ready (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (keys : List Nat) (hk : ∀p,p∈keys→p∈partition.leaders.entries) (tree : BankTree C E h) :
    (Clip.applyKeys env st keys old lo hi tree).ready=true := by
  have go : ∀(ps : List Nat) (acc : Clip.Update C E h),
      (∀p,p∈ps→p∈partition.leaders.entries)→acc.ready=true→
      (ps.foldl (fun acc first=>let one:=Clip.atLeader env st first old lo hi acc.tree
        ; Clip.Update.mk one.tree (acc.ready && one.ready) (acc.work+one.work+1) (acc.calls+one.calls)) acc).ready=true := by
    intro ps
    induction ps with
    | nil=>intro acc _ ha; exact ha
    | cons first ps ih=>
      intro acc hps ha
      obtain ⟨entry,he⟩:=complete first (hps first List.mem_cons_self)
      have hon:=atLeader_ready env st partition capacity old first lo hi entry (coherent first entry he) acc.tree
      apply ih _ (fun p hp=>hps p (List.mem_cons_of_mem first hp))
      simp only [ha,hon,Bool.true_and]
  exact go keys ⟨tree,true,0,0⟩ hk rfl

theorem plan_keys_leaders (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h) :
    ∀p,p∈(Clip.plan partition.leaders capacity lo hi).keys→p∈partition.leaders.entries := by
  intro p hp
  rcases (Clip.selected_mem _ _ p).mp hp with hl|hr
  · have hh:=MaskedOrdered.Tree.pred_correct partition.leaders capacity (lo+1) hv.leadGood hv.leadFits hc
    rw [hl] at hh
    exact hh.1
  · have hh:=MaskedOrdered.Tree.pred_correct partition.leaders capacity hi hv.leadGood hv.leadFits hc
    rw [hr] at hh
    exact hh.1

theorem window_ready (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (tree : BankTree C E h) (hwindow : lo<hi) :
    (Clip.window env st partition capacity old lo hi tree).update.ready=true := by
  simp only [Clip.window,hwindow,if_true]
  exact applyKeys_ready env st partition capacity old lo hi entries coherent complete _
    (plan_keys_leaders partition capacity old lo hi hv hc) tree

end REWB.MaskedTraversalAggregate.Cells
