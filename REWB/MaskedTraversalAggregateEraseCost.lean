import REWB.MaskedTraversalAggregateErase

/-! Current-length source repair includes the real owner lookup, selected
bank compilation, indexed slot write and persistent leaf replacement.
The source batch separately retains the actual reverse-run fanout work.
-/
namespace REWB.MaskedTraversalAggregate
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {h : Nat}

theorem selectedCurrentWork_bound (env : Clip.Env C E) (first old : Nat) (st : Mutable.Store.State C E)
    (w : Word α) (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hg : ∀entry,st.slots[first]?.join=some entry→Mutable.Store.Geometry (withLength entry.config old) w.length) :
    selectedCurrentWork env first old st≤Mutable.Store.bankLimit C E env.prepared.K w.length := by
  cases hs : st.slots[first]?.join with
  | none => simp only [selectedCurrentWork,hs]; exact Nat.zero_le _
  | some entry =>
    have hw:=Mutable.Store.compile_work C E env.book env.prepared w source removed st.sources hv hn
      env.target (withLength entry.config old) (hg entry hs)
    simpa only [selectedCurrentWork,hs,Clip.compiled,hc,he] using hw

theorem eraseCurrent_work (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (w : Word α) (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hg : ∀first,(MaskedClusterDescriptor.locate partition capacity p).1=some first→
      ∀entry,st.slots[first]?.join=some entry→Mutable.Store.Geometry (withLength entry.config old) w.length) :
    (eraseCurrent env partition capacity old p st tree).work≤11*h+24+
      Mutable.Store.bankLimit C E env.prepared.K w.length+
        (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
          (2*(MaskedClusterStage.dfa C E).stateCount) := by
  have hl:=MaskedClusterDescriptor.locate_work partition capacity p
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none => simp only [eraseCurrent,ho]; omega
  | some first =>
    let next:={st with
      sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
      repairWork:=st.repairWork+(MaskedClusterDescriptor.locate partition capacity p).2+2}
    have hw:=refreshCurrent_work env first old next tree
    have hv':=MaskedMutableProgression.Batch.eraseSource_valid hv p
    have hn' : next.sources.n=w.length := by
      change (MaskedMutableProgression.Batch.eraseSource p st.sources).n=w.length
      rw [MaskedMutableProgression.Batch.eraseSource_n,hn]
    have hb:=selectedCurrentWork_bound env first old next w source (p::removed) hv' hn' hc he (hg first ho)
    simp only [eraseCurrent,ho]
    change (refreshCurrent env first old next tree).work+(MaskedClusterDescriptor.locate partition capacity p).2+3≤_
    omega

theorem refreshCurrent_represents (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (hr : Cells.Represents tree entries)
    (ok : (refreshCurrent env first old st tree).ready=true) :
    Cells.Represents (refreshCurrent env first old st tree).tree
      (entries.set first ((refreshCurrent env first old st tree).store.slots[first]?.join)) := by
  obtain ⟨before,bank,_,_,hs,hcells⟩:=refreshCurrent_selected env first old st tree ok
  simp only [Cells.Represents,hcells,hs,List.map_set,Cells.entryView]
  rw [hr]

theorem eraseCurrent_represents (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (hr : Cells.Represents tree entries)
    (ok : (eraseCurrent env partition capacity old p st tree).ready=true) :
    Cells.Represents (eraseCurrent env partition capacity old p st tree).tree
      (match (MaskedClusterDescriptor.locate partition capacity p).1 with
       | none=>entries
       | some first=>entries.set first ((eraseCurrent env partition capacity old p st tree).store.slots[first]?.join)) := by
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none => simpa only [eraseCurrent,ho] using hr
  | some first =>
    simpa only [eraseCurrent,ho] using refreshCurrent_represents env first old _ tree entries hr
      (by simpa only [eraseCurrent,ho] using ok)

end REWB.MaskedTraversalAggregate
