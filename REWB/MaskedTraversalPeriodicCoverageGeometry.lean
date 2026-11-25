import REWB.MaskedRunCatalogDiscovery
import REWB.MaskedPeriodicBatch

/-! Two nonoverlapping current captures in one actual descriptor force
a dense AP. The descriptor's real indexed discovery identifies a maximal
least-period run containing both captures. That run belongs to the actual
global enumerator used by the periodic batch producer. -/
namespace REWB.MaskedTraversalPeriodicCoverage
open REWB.Spec REWB.MaskedClusterDescriptor REWB.MaskedRunDiscovery REWB.RunGeometry
variable {σ h : Nat}

theorem same_owner_run (text : Array (Fin σ)) (fallback : Fin σ)
    (partition : MaskedClusterLeaders.State h) (capacity base L p j : Nat)
    (invariant : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (complete : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (positive : 0<L) (hp : p∈partition.occurrences.entries) (hj : j∈partition.occurrences.entries)
    (same : (locate partition capacity p).1=(locate partition capacity j).1) (nonoverlap : p+L≤j) :
    ∃R : Bounds,∃k : Nat,R∈(MaskedOrdered.Owner.enumerateAuto text fallback).runs ∧
      R.Valid (ArrayText.read text fallback) text.size ∧ R.lo≤p ∧ 2*R.period≤L ∧
      j=p+k*R.period ∧ j+L≤R.hi := by
  obtain ⟨first,hfirst⟩:=locate_exists partition capacity L p invariant hcap hp
  have hsecond : (locate partition capacity j).1=some first := same.symm.trans hfirst
  have sourceOwn:=(locate_correct partition capacity L p first invariant hcap).mp hfirst
  have targetOwn:=(locate_correct partition capacity L j first invariant hcap).mp hsecond
  obtain ⟨d,hd,hdf,sound⟩:=describeLeader_exists partition capacity L first invariant hcap sourceOwn.2.1
  have geom:=describeLeader_geometry partition capacity L first invariant hcap d hd
    (ArrayText.read text fallback) text.size base complete positive
  have ps : p∈partition.occurrences.entries ∧ d.first≤p ∧ p≤d.last :=
    (sound.owns_iff partition capacity L invariant hcap d p).mp (by rw [hdf]; exact sourceOwn)
  have js : j∈partition.occurrences.entries ∧ d.first≤j ∧ j≤d.last :=
    (sound.owns_iff partition capacity L invariant hcap d j).mp (by rw [hdf]; exact targetOwn)
  have dense : 0<d.repetitions := by
    by_cases hz : d.repetitions=0
    · have he:=geom.endpoint
      rw [hz,Nat.zero_mul,Nat.add_zero] at he
      omega
    · omega
  obtain ⟨a,ha,hpa⟩:=(geom.members p).mp ps
  obtain ⟨b,hb,hjb⟩:=(geom.members j).mp js
  have hab : a≤b := by
    by_cases hab : a≤b
    · exact hab
    · have hh:=Nat.mul_lt_mul_of_pos_right (show b<a by omega) geom.period_pos
      omega
  have hdiff : j=p+(b-a)*d.period := by
    rw [Nat.sub_mul]
    have hh:=Nat.mul_le_mul_right d.period hab
    omega
  obtain ⟨R,_,_,_,valid,period,left,right⟩:=MaskedRunCatalog.descriptor_complete text fallback #[] #[] 1
    partition capacity L first base invariant hcap d hd complete positive dense
  have twice : 2*R.period≤L := by rw [period]; exact (geom.dense dense).1
  have sourceBound : R.lo≤p := Nat.le_trans left ps.2.1
  have targetBound : j+L≤R.hi := Nat.le_trans (Nat.add_le_add_right js.2.2 L) right
  have cubic : 3*R.period≤R.hi-R.lo := by omega
  exact ⟨R,b-a,(MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mpr ⟨valid,cubic⟩,
    valid,sourceBound,twice,by rw [period]; exact hdiff,targetBound⟩

theorem class_copy (text : Array (Fin σ)) (fallback : Fin σ)
    (base L : Nat) (xs : List Nat)
    (complete : Complete (ArrayText.read text fallback) text.size base L xs)
    (p j : Nat) (hp : p∈xs) (hj : j∈xs) :
    slice text.toList p (p+L)=slice text.toList j (j+L) := by
  have pp:=(complete p).mp hp
  have jj:=(complete j).mp hj
  have he:=pp.2.trans jj.2.symm
  have pp' : p+L≤text.toList.length := by simpa only [Array.length_toList] using pp.1
  have jj' : j+L≤text.toList.length := by simpa only [Array.length_toList] using jj.1
  rw [show text=text.toList.toArray from Array.toArray_toList.symm] at he
  rw [ArrayText.segment_word text.toList fallback p L pp',ArrayText.segment_word text.toList fallback j L jj'] at he
  simpa only [slice,Nat.add_sub_cancel_left] using he

end REWB.MaskedTraversalPeriodicCoverage
