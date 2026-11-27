import REWB.MaskedClusterCell
import REWB.MaskedClusterFactors

/-! Correctness of the actual dense-cluster one-jump compiler. Its
    contexts and replay tail come from shared range indices over `w`.
    The hypotheses state real periodicity and physical cursor/anchor
    bounds; no transition or matching-answer oracle is supplied.
    Choosing lo/hi from neighboring cursor modes is a separate geometric
    scheduling obligation, not hidden in an assumed per-query cost.
-/
namespace REWB.MaskedCluster
open REWB.Periodic REWB.Spec REWB.MaskedPeriodic
open REWB.MaskedFiniteAction.Maps
variable {α : Type}

theorem wordCell_anchored (C E : DFA α) (w : Word α) (fallback : α)
    (base I s R q L H lo hi k O : Nat) (source target : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q)
    (hq : q≤H) (hlo : lo≤k) (hhi : k≤hi) (hI : I≤s+lo*q)
    (hb : s+hi*q+H≤R) (hn : R≤w.length) (hO : s+hi*q+H≤O) (hOn : O≤w.length) :
    WordCell C E (slice w I (s+lo*q)) (slice w s (s+q))
      (slice w (s+(H-q)) (s+H)) (slice w (base+L) (base+H))
      (slice w (s+hi*q+H) O) lo hi k source target input output ↔
        MaskedClusterStage.anchored C E w base I (s+k*q) L H O source target input=some output := by
  have hm:=Nat.mul_le_mul_right q hhi
  have hpre:=prefix_factor w fallback I s R q lo k hp hlo hI (by omega) hn
  have hpost:=suffix_factor w fallback s R q H k hi O hp hq hhi hb hn hO hOn
  have hr (a b : Word α) : MaskedClusterStage.read C E (a++b)=
      fun t=>MaskedClusterStage.read C E b (MaskedClusterStage.read C E a t) := by
    funext t
    exact MaskedClusterStage.read_append C E a b t
  unfold WordCell MaskedClusterStage.anchored
  rw [hpre,hpost]
  simp only [hr]

theorem cell_anchored (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (anchor I s R q L H lo hi O : Nat)
    (source target : Array Bool) (base len : Nat)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q)
    (hq : 0<q) (hH : q≤H) (hlo : lo≤hi) (hI : I≤s+lo*q)
    (hb : s+hi*q+H≤R) (hn : R≤w.length) (hO : s+hi*q+H≤O) (hOn : O≤w.length)
    (hLH : L≤H) (hanchor : anchor+H≤w.length) :
    (cell C E prepared
      (contexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        I s H q lo hi O).maps
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        anchor L H).maps lo hi
      (MaskedProgression.build source base len (prepared.K*q)).counts
      (MaskedProgression.build target base len (prepared.K*q)).counts base q s input output).answer=true ↔
        ∃ k,lo≤k ∧ k≤hi ∧ base≤s+k*q ∧ s+k*q<base+len ∧
          MaskedClusterStage.anchored C E w anchor I (s+k*q) L H O
            (MaskedProgression.readMask source (s+k*q))
            (MaskedProgression.readMask target (s+k*q)) input=some output := by
  rw [contexts_value C E w I s H q lo hi O hH hlo hI hO hOn,
    replay_value C E w anchor L H hLH hanchor,cell_words C E prepared _ _ _ _ _ lo hi
      source target base len q s input output hq]
  constructor
  · rintro ⟨k,hl,hh,hbase,hbound,hw⟩
    exact ⟨k,hl,hh,hbase,hbound,(wordCell_anchored C E w fallback anchor I s R q L H lo hi k O
      _ _ input output hp hH hl hh hI hb hn hO hOn).mp hw⟩
  · rintro ⟨k,hl,hh,hbase,hbound,hw⟩
    exact ⟨k,hl,hh,hbase,hbound,(wordCell_anchored C E w fallback anchor I s R q L H lo hi k O
      _ _ input output hp hH hl hh hI hb hn hO hOn).mpr hw⟩

/-- The semantic target is the stage machine's real skip of L
    characters. A local anchor certificate supplies equality at H;
    shortening is represented solely by the replay-tail maps. -/
theorem cell_direct (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (anchor I s R q L H lo hi O : Nat)
    (source target : Array Bool) (base len : Nat)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q)
    (hq : 0<q) (hH : q≤H) (hlo : lo≤hi) (hI : I≤s+lo*q)
    (hb : s+hi*q+H≤R) (hn : R≤w.length) (hO : s+hi*q+H≤O) (hOn : O≤w.length)
    (hLH : L≤H) (hanchor : anchor+H≤w.length)
    (hcopy : ∀ k,lo≤k→k≤hi→slice w anchor (anchor+H)=slice w (s+k*q) (s+k*q+H)) :
    (cell C E prepared
      (contexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        I s H q lo hi O).maps
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        anchor L H).maps lo hi
      (MaskedProgression.build source base len (prepared.K*q)).counts
      (MaskedProgression.build target base len (prepared.K*q)).counts base q s input output).answer=true ↔
        ∃ k,lo≤k ∧ k≤hi ∧ base≤s+k*q ∧ s+k*q<base+len ∧
          MaskedClusterStage.direct C E w I (s+k*q) L O
            (MaskedProgression.readMask source (s+k*q))
            (MaskedProgression.readMask target (s+k*q)) input=some output := by
  rw [cell_anchored C E prepared w fallback anchor I s R q L H lo hi O source target base len
    input output hp hq hH hlo hI hb hn hO hOn hLH hanchor]
  constructor
  · rintro ⟨k,hl,hh,hbase,hbound,hw⟩
    have hm:=Nat.mul_le_mul_right q hh
    rw [MaskedClusterStage.anchored_exact C E w anchor I (s+k*q) L H O _ _ input
      hLH (by omega) (hcopy k hl hh)] at hw
    exact ⟨k,hl,hh,hbase,hbound,hw⟩
  · rintro ⟨k,hl,hh,hbase,hbound,hw⟩
    have hm:=Nat.mul_le_mul_right q hh
    refine ⟨k,hl,hh,hbase,hbound,?_⟩
    rwa [MaskedClusterStage.anchored_exact C E w anchor I (s+k*q) L H O _ _ input
      hLH (by omega) (hcopy k hl hh)]

/-- Taking the first cluster occurrence as the local representative
    derives every anchored-copy equality from actual periodic text. -/
theorem cell_direct_first (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (I s R q L H lo hi O : Nat)
    (source target : Array Bool) (base len : Nat)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q)
    (hq : 0<q) (hH : q≤H) (hlo : lo≤hi) (hI : I≤s+lo*q)
    (hb : s+hi*q+H≤R) (hn : R≤w.length) (hO : s+hi*q+H≤O) (hOn : O≤w.length)
    (hLH : L≤H) :
    (cell C E prepared
      (contexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        I s H q lo hi O).maps
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s L H).maps lo hi
      (MaskedProgression.build source base len (prepared.K*q)).counts
      (MaskedProgression.build target base len (prepared.K*q)).counts base q s input output).answer=true ↔
        ∃ k,lo≤k ∧ k≤hi ∧ base≤s+k*q ∧ s+k*q<base+len ∧
          MaskedClusterStage.direct C E w I (s+k*q) L O
            (MaskedProgression.readMask source (s+k*q))
            (MaskedProgression.readMask target (s+k*q)) input=some output := by
  apply cell_direct C E prepared w fallback s I s R q L H lo hi O source target base len
    input output hp hq hH hlo hI hb hn hO hOn hLH (by omega)
  intro k _ hh
  have hm:=Nat.mul_le_mul_right q hh
  exact MaskedPeriodic.Text.actual_equal_copies w fallback s R q H k hp hn (by omega)

end REWB.MaskedCluster
