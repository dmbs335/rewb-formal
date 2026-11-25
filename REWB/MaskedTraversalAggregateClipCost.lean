import REWB.MaskedTraversalAggregateClip
import REWB.MaskedClusterMutableStoreCost

/-! The boundary clips use the actual mutable bank compiler. The bound
includes its selected source-tree/range work and both persistent tree
replacements. No per-query bank enumeration or text scan is performed.
-/
namespace REWB.MaskedTraversalAggregate.Clip
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {h : Nat}

theorem config_geometry (cfg : Mutable.Store.Config) (old lo hi n : Nat)
    (hg : Mutable.Store.Geometry cfg n) (hc : old≤cfg.anchor) :
    Mutable.Store.Geometry (config cfg old lo hi) n :=
  ⟨hc,hg.period,hg.penultimate,hg.separated,hg.nextBound,hg.endBound,hg.incoming⟩

theorem selectedWork_bound (env : Env C E) (st : Mutable.Store.State C E)
    (w : Word α) (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hn : st.sources.n=w.length)
    (hc : env.cRanges=BoundaryApplication.Range.build C w)
    (he : env.eRanges=BoundaryApplication.Range.build E w)
    (first old lo hi : Nat)
    (hg : ∀entry,st.slots[first]?.join=some entry→
      Mutable.Store.Geometry (config entry.config old lo hi) w.length) :
    selectedWork env st first old lo hi≤Mutable.Store.bankLimit C E env.prepared.K w.length := by
  cases hs : st.slots[first]?.join with
  | none => simp only [selectedWork,hs]; exact Nat.zero_le _
  | some entry =>
    have hw:=Mutable.Store.compile_work C E env.book env.prepared w source removed st.sources hv hn
      env.target (config entry.config old lo hi) (hg entry hs)
    simpa only [selectedWork,hs,compiled,hc,he] using hw

theorem applyKeys_work (env : Env C E) (st : Mutable.Store.State C E)
    (keys : List Nat) (old lo hi limit : Nat) (tree : BankTree C E h)
    (bound : ∀p,p∈keys→selectedWork env st p old lo hi≤limit) :
    (applyKeys env st keys old lo hi tree).work≤keys.length*
      (limit+(h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
        (2*(MaskedClusterStage.dfa C E).stateCount)+10) := by
  let budget:=limit+(h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
    (2*(MaskedClusterStage.dfa C E).stateCount)+10
  have go : ∀(ps : List Nat) (acc : Update C E h),
      (∀p,p∈ps→selectedWork env st p old lo hi≤limit)→
      (ps.foldl (fun acc first=>let one:=atLeader env st first old lo hi acc.tree
        ; Update.mk one.tree (acc.ready && one.ready) (acc.work+one.work+1) (acc.calls+one.calls)) acc).work
        ≤acc.work+ps.length*budget := by
    intro ps
    induction ps with
    | nil => intro acc hp; simp only [List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero,Nat.le_refl]
    | cons first ps ih =>
      intro acc hp
      have hw:=atLeader_work env st first old lo hi acc.tree
      have hb:=hp first List.mem_cons_self
      have hh:=ih (Update.mk (atLeader env st first old lo hi acc.tree).tree
        (acc.ready && (atLeader env st first old lo hi acc.tree).ready)
        (acc.work+(atLeader env st first old lo hi acc.tree).work+1)
        (acc.calls+(atLeader env st first old lo hi acc.tree).calls))
        (fun p hmem=>hp p (List.mem_cons_of_mem first hmem))
      simp only [List.foldl_cons,List.length_cons,Nat.succ_mul]
      dsimp only at hh
      dsimp only [budget] at *
      omega
  simpa only [applyKeys,Nat.zero_add] using go keys (Update.mk tree true 0 0) bound

theorem window_work (env : Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (tree : BankTree C E h) (w : Word α) (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hn : st.sources.n=w.length)
    (hc : env.cRanges=BoundaryApplication.Range.build C w)
    (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hg : ∀first,first∈(plan partition.leaders capacity lo hi).keys→
      ∀entry,st.slots[first]?.join=some entry→
        Mutable.Store.Geometry (config entry.config old lo hi) w.length) :
    (window env st partition capacity old lo hi tree).work≤
      14*h+15+2*(Mutable.Store.bankLimit C E env.prepared.K w.length+
        (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
          (2*(MaskedClusterStage.dfa C E).stateCount)+10) := by
  unfold window
  split
  · have ha:=applyKeys_work env st (plan partition.leaders capacity lo hi).keys old lo hi
      (Mutable.Store.bankLimit C E env.prepared.K w.length) tree
      (fun p hp=>selectedWork_bound env st w source removed hv hn hc he p old lo hi (hg p hp))
    have hp:=plan_work partition.leaders capacity lo hi
    have hl:=plan_length partition.leaders capacity lo hi
    have hm:=Nat.mul_le_mul_right
      (Mutable.Store.bankLimit C E env.prepared.K w.length+
        (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
          (2*(MaskedClusterStage.dfa C E).stateCount)+10) hl
    dsimp only
    omega
  · dsimp only; omega

end REWB.MaskedTraversalAggregate.Clip
