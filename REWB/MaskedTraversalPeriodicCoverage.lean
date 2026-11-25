import REWB.MaskedTraversalPeriodicCoverageGeometry
import REWB.MaskedTraversalCompleteCorrect
import REWB.MaskedEmptyCorrect

/-! Same-cluster original witnesses are covered by the actual periodic
batch producer. Every remaining positive class/band witness belongs to
the distinct-owner bank-query contract. Source deletion history remains
explicit and the immutable target mask is shared by both branches. -/
namespace REWB.MaskedTraversalPeriodicCoverage
open REWB.Spec REWB.MaskedClusterDescriptor REWB.MaskedRunDiscovery REWB.RunGeometry
open REWB.MaskedCluster REWB.MaskedProgression
variable {σ h : Nat}

theorem same_owner_witness (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (target : Array Bool) (partition : MaskedClusterLeaders.State h) (capacity base L p j : Nat)
    (invariant : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (complete : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (positive : 0<L) (hp : p∈partition.occurrences.entries) (hj : j∈partition.occurrences.entries)
    (same : (locate partition capacity p).1=(locate partition capacity j).1) (nonoverlap : p+L≤j)
    (marked : readMask target j=true)
    (hB : B.accepts (slice text.toList p (p+L))) (hC : C.accepts (slice text.toList (p+L) j))
    (hE : E.accepts (slice text.toList (j+L) text.size)) :
    ∃R : Bounds,R∈(MaskedOrdered.Owner.enumerateAuto text fallback).runs ∧
      R.Valid (ArrayText.read text fallback) text.size ∧ R.lo≤p ∧
      MaskedPeriodic.Text.FullWitness B C E text.toList p R.hi R.period target R.lo (MaskedPeriodic.Batch.span R) := by
  obtain ⟨R,k,henum,valid,left,twice,coord,right⟩:=same_owner_run text fallback partition capacity base L p j
    invariant hcap complete positive hp hj same nonoverlap
  refine ⟨R,henum,valid,left,L,k,twice,?_,?_,?_,hB,?_,?_,?_⟩
  · rw [←coord]; exact nonoverlap
  · rw [←coord]; exact right
  · rw [←coord]; exact class_copy text fallback base L _ complete p j hp hj
  · rw [←coord]; exact hC
  · rw [←coord,←MaskedPeriodic.Text.suffix_slice]
    simpa only [Array.length_toList] using hE
  · change R.lo≤p+k*R.period ∧ p+k*R.period<R.lo+(R.hi-R.lo+1) ∧ readMask target (p+k*R.period)=true
    rw [←coord]
    exact ⟨by omega,by omega,marked⟩

theorem same_owner_covered (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (target : Array Bool) (partition : MaskedClusterLeaders.State h) (capacity base L p j : Nat)
    (invariant : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (complete : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (positive : 0<L) (hp : p∈partition.occurrences.entries) (hj : j∈partition.occurrences.entries)
    (same : (locate partition capacity p).1=(locate partition capacity j).1) (nonoverlap : p+L≤j)
    (marked : readMask target j=true)
    (hB : B.accepts (slice text.toList p (p+L))) (hC : C.accepts (slice text.toList (p+L) j))
    (hE : E.accepts (slice text.toList (j+L) text.size)) :
    MaskedPeriodic.Batch.Covered B C E text fallback target p := by
  obtain ⟨R,_,valid,left,witness⟩:=same_owner_witness B C E text fallback target partition capacity base L p j
    invariant hcap complete positive hp hj same nonoverlap marked hB hC hE
  exact ⟨R,valid,left,witness⟩

theorem same_owner_hit (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (partition : MaskedClusterLeaders.State h) (capacity base L p j : Nat)
    (invariant : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (complete : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (positive : 0<L) (hp : p∈partition.occurrences.entries) (hj : j∈partition.occurrences.entries)
    (same : (locate partition capacity p).1=(locate partition capacity j).1) (nonoverlap : p+L≤j)
    (live : readMask source p=true) (marked : readMask target j=true)
    (hB : B.accepts (slice text.toList p (p+L))) (hC : C.accepts (slice text.toList (p+L) j))
    (hE : E.accepts (slice text.toList (j+L) text.size)) :
    readMask (MaskedPeriodic.Batch.solve B C E text fallback source target).output.hits p=true := by
  apply (MaskedPeriodic.Batch.solve_correct B C E text fallback source target p).mpr
  exact ⟨live,same_owner_covered B C E text fallback target partition capacity base L p j
    invariant hcap complete positive hp hj same nonoverlap marked hB hC hE⟩

theorem member_of_copy (text : Array (Fin σ)) (fallback : Fin σ) (base L p j : Nat) (xs : List Nat)
    (complete : Complete (ArrayText.read text fallback) text.size base L xs) (hp : p∈xs)
    (bound : j+L≤text.size) (copy : slice text.toList p (p+L)=slice text.toList j (j+L)) : j∈xs := by
  have pp:=(complete p).mp hp
  have pp' : p+L≤text.toList.length := by simpa only [Array.length_toList] using pp.1
  have jj' : j+L≤text.toList.length := by simpa only [Array.length_toList] using bound
  have he : Periodic.segment (ArrayText.read text fallback) j L=Periodic.segment (ArrayText.read text fallback) p L := by
    rw [show text=text.toList.toArray from Array.toArray_toList.symm]
    rw [ArrayText.segment_word text.toList fallback j L jj',ArrayText.segment_word text.toList fallback p L pp']
    simpa only [slice,Nat.add_sub_cancel_left] using copy.symm
  exact (complete j).mpr ⟨bound,he.trans pp.2⟩

theorem cut_partition (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (removed : List Nat) (partition : MaskedClusterLeaders.State h)
    (capacity base lengthLo lengthHi L p j : Nat)
    (invariant : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (complete : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (positive : 0<L) (low : lengthLo≤L) (high : L≤lengthHi)
    (live : Mutable.Batch.currentBit source removed p=true) (hp : p∈partition.occurrences.entries)
    (nonoverlap : p+L≤j) (bound : j+L≤text.size) (marked : readMask target j=true)
    (copy : slice text.toList p (p+L)=slice text.toList j (j+L))
    (hB : B.accepts (slice text.toList p (p+L))) (hC : C.accepts (slice text.toList (p+L) j))
    (hE : E.accepts (slice text.toList (j+L) text.size)) :
    readMask (MaskedPeriodic.Batch.solve B C E text fallback source target).output.hits p=true ∨
      MaskedTraversalComplete.BandGood B C E text.toList partition capacity lengthLo lengthHi source removed target p := by
  have hj:=member_of_copy text fallback base L p j _ complete hp bound copy
  by_cases same : (locate partition capacity p).1=(locate partition capacity j).1
  · apply Or.inl
    exact same_owner_hit B C E text fallback source target partition capacity base L p j invariant hcap complete
      positive hp hj same nonoverlap (Bool.and_eq_true_iff.mp live).1 marked hB hC hE
  · exact Or.inr ⟨live,hp,L,low,high,j,hj,marked,same,nonoverlap,by simpa only [Array.length_toList] using bound,hB,hC,
      by simpa only [Array.length_toList] using hE⟩

theorem remaining_distinct (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (removed : List Nat) (partition : MaskedClusterLeaders.State h)
    (capacity base lengthLo lengthHi L p j : Nat)
    (invariant : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (complete : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (positive : 0<L) (low : lengthLo≤L) (high : L≤lengthHi)
    (live : Mutable.Batch.currentBit source removed p=true) (hp : p∈partition.occurrences.entries)
    (nonoverlap : p+L≤j) (bound : j+L≤text.size) (marked : readMask target j=true)
    (copy : slice text.toList p (p+L)=slice text.toList j (j+L))
    (hB : B.accepts (slice text.toList p (p+L))) (hC : C.accepts (slice text.toList (p+L) j))
    (hE : E.accepts (slice text.toList (j+L) text.size))
    (notReported : readMask (MaskedPeriodic.Batch.solve B C E text fallback source target).output.hits p=false) :
    MaskedTraversalComplete.BandGood B C E text.toList partition capacity lengthLo lengthHi source removed target p := by
  rcases cut_partition B C E text fallback source target removed partition capacity base lengthLo lengthHi L p j
    invariant hcap complete positive low high live hp nonoverlap bound marked copy hB hC hE with periodic|cross
  · rw [notReported] at periodic; cases periodic
  · exact cross

theorem original_length (w : Word α) (p a j t : Nat)
    (positive : p<a) (nonoverlap : a≤j) (ordered : j≤t) (bound : t≤w.length)
    (copy : slice w p a=slice w j t) : 0<a-p ∧ a=p+(a-p) ∧ t=j+(a-p) := by
  have hl:=congrArg List.length copy
  rw [OuterColumn.slice_length w p a (by omega) (by omega),OuterColumn.slice_length w j t ordered bound] at hl
  omega

theorem original_partition (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (removed : List Nat) (partition : MaskedClusterLeaders.State h)
    (capacity base lengthLo lengthHi p a j t : Nat)
    (invariant : MaskedClusterLeaders.Invariant (a-p) partition) (hcap : capacity=2^h)
    (complete : Complete (ArrayText.read text fallback) text.size base (a-p) partition.occurrences.entries)
    (low : lengthLo≤a-p) (high : a-p≤lengthHi)
    (live : Mutable.Batch.currentBit source removed p=true) (hp : p∈partition.occurrences.entries)
    (positive : p<a) (nonoverlap : a≤j) (ordered : j≤t) (bound : t≤text.size) (marked : readMask target j=true)
    (copy : slice text.toList p a=slice text.toList j t)
    (hB : B.accepts (slice text.toList p a)) (hC : C.accepts (slice text.toList a j))
    (hE : E.accepts (slice text.toList t text.size)) :
    readMask (MaskedPeriodic.Batch.solve B C E text fallback source target).output.hits p=true ∨
      MaskedTraversalComplete.BandGood B C E text.toList partition capacity lengthLo lengthHi source removed target p := by
  obtain ⟨hL,ha,ht⟩:=original_length text.toList p a j t positive nonoverlap ordered
    (by simpa only [Array.length_toList] using bound) copy
  exact cut_partition B C E text fallback source target removed partition capacity base lengthLo lengthHi (a-p) p j
    invariant hcap complete hL low high live hp (by rw [←ha]; exact nonoverlap)
    (by rw [←ht]; exact bound) marked (by rw [←ha,←ht]; exact copy)
    (by rw [←ha]; exact hB) (by rw [←ha]; exact hC) (by rw [←ht]; exact hE)

end REWB.MaskedTraversalPeriodicCoverage
