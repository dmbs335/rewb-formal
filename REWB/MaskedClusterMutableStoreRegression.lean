import REWB.MaskedClusterMutableStoreGeometry

/-! Kernel regressions for actual leader lookup and the dirty-store
    operation. Non-occurrences inside AP hulls perform no bank repair;
    the actual global source batch is nevertheless updated.
-/
namespace REWB.MaskedCluster.Mutable.Store.Regression
variable {α : Type}

def partition := (MaskedClusterLeaders.execute 5 4
  ([0,2,4,10,12,18].map MaskedClusterLeaders.Operation.insert)).state

theorem inside_dense_hulls :
    (MaskedClusterDescriptor.describeLeader partition 32 0).1.map (fun d=>(d.first,d.last))=some (0,4) ∧
    (MaskedClusterDescriptor.describeLeader partition 32 10).1.map (fun d=>(d.first,d.last))=some (10,12) ∧
    (MaskedClusterDescriptor.locate partition 32 1).1=none ∧
    (MaskedClusterDescriptor.locate partition 32 11).1=none := by decide

theorem actual_owners :
    (MaskedClusterDescriptor.locate partition 32 4).1=some 0 ∧
    (MaskedClusterDescriptor.locate partition 32 12).1=some 10 ∧
    (MaskedClusterDescriptor.locate partition 32 18).1=some 18 := by decide

theorem nonoccurrence_no_bank_repair (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (target : Array Bool) (st : State C E) :
    let next:=eraseSource C E book prepared ci ei partition 32 target 1 st
    next.slots=st.slots ∧ next.rebuilds=st.rebuilds ∧ next.writes=st.writes ∧
      next.sources=MaskedMutableProgression.Batch.eraseSource 1 st.sources := by
  simp [eraseSource,inside_dense_hulls.2.2.1]

theorem other_cluster_shared (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (target : Array Bool) (st : State C E) :
    (eraseSource C E book prepared ci ei partition 32 target 4 st).slots[10]?=st.slots[10]? := by
  apply eraseSource_other
  rw [actual_owners.1]
  decide

end REWB.MaskedCluster.Mutable.Store.Regression
