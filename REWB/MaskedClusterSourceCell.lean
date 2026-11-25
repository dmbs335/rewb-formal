import REWB.MaskedClusterSourceAP
import REWB.MaskedClusterCertificate

/-! Report-interval clipping changes only waiting-to-C cells. C-to-E
    cells retain the full target window. The semantics exposes the
    resulting source bit explicitly, so clipping both masks cannot be
    mistaken for a valid reporting implementation.
-/
namespace REWB.MaskedCluster
open REWB.MaskedPeriodic REWB.MaskedFiniteAction.Maps REWB.Spec
variable {α : Type}

def filteredCell (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat) (window : SourceWindow) :
    MaskedClusterStage.State C.stateCount E.stateCount→
      MaskedClusterStage.State C.stateCount E.stateCount→MaskedProgression.Answer
  | .waiting,.gap output =>
    sourcePairQuery (always C) (exitOrbit C maps.rightC tail.1 maps.afterC output)
      lo hi sourceCounts base q s prepared.K window
  | input,output => cell C E prepared maps tail lo hi sourceCounts targetCounts base q s input output

/-- Target cells are definitionally unchanged by the source window. -/
theorem filteredCell_target (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat) (window : SourceWindow)
    (input : Fin C.stateCount) (output : MaskedClusterStage.State C.stateCount E.stateCount) :
    filteredCell C E prepared maps tail lo hi sourceCounts targetCounts base q s window (.gap input) output=
      cell C E prepared maps tail lo hi sourceCounts targetCounts base q s (.gap input) output := rfl

theorem filteredCell_words (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (pref V U Y after : Word α) (lo hi : Nat) (source target : Array Bool)
    (base len q s : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) (hq : 0<q) :
    (filteredCell C E prepared (wordContext C E pref V U after) (wordMap C Y,wordMap E Y) lo hi
      (MaskedProgression.build source base len (prepared.K*q)).counts
      (MaskedProgression.build target base len (prepared.K*q)).counts base q s window input output).answer=true ↔
        ∃ k,lo≤k ∧ k≤hi ∧ base≤s+k*q ∧ s+k*q<base+len ∧
          WordCell C E pref V U Y after lo hi k
            (window.allows (s+k*q) && MaskedProgression.readMask source (s+k*q))
            (MaskedProgression.readMask target (s+k*q)) input output := by
  cases input with
  | waiting =>
    cases output with
    | waiting =>
      simp only [filteredCell,cell,Bool.false_eq_true,false_iff]
      rintro ⟨k,_,_,_,_,hw⟩
      have hr:=wordCell_rank C E pref V U Y after lo hi k _ _ _ _ hw
      simp only [MaskedClusterStage.rank] at hr
      omega
    | gap output =>
      simp only [filteredCell,prepared.exact,modulus]
      rw [sourcePairQuery_correct _ _ _ _ _ _ _ _ _ _ window hq (Nat.le_max_left _ _) (Nat.le_max_left _ _)]
      simp only [PairAccepts,always_test,exitOrbit_word,wordContext,wordCell_waiting,Bool.and_eq_true]
      constructor
      · rintro ⟨k,⟨hl,hh,_,he⟩,⟨hb,hn,hm⟩,hw⟩
        exact ⟨k,hl,hh,hb,hn,⟨hw,hm⟩,he⟩
      · rintro ⟨k,hl,hh,hb,hn,⟨hw,hm⟩,he⟩
        exact ⟨k,⟨hl,hh,True.intro,he⟩,⟨hb,hn,hm⟩,hw⟩
    | suffix output =>
      simp only [filteredCell,cell,Bool.false_eq_true,false_iff]
      rintro ⟨k,_,_,_,_,hw⟩
      have hr:=wordCell_rank C E pref V U Y after lo hi k _ _ _ _ hw
      simp only [MaskedClusterStage.rank] at hr
      omega
  | gap input =>
    exact cell_words C E prepared pref V U Y after lo hi source target base len q s (.gap input) output hq
  | suffix input =>
    exact cell_words C E prepared pref V U Y after lo hi source target base len q s (.suffix input) output hq

theorem filteredCell_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (filteredCell C E prepared maps tail lo hi sourceCounts targetCounts base q s window input output).slots+
      (filteredCell C E prepared maps tail lo hi sourceCounts targetCounts base q s window input output).arithmetic≤
        cellBudget C E prepared.K := by
  cases input with
  | waiting =>
    cases output with
    | waiting => exact cell_work C E prepared maps tail lo hi sourceCounts targetCounts base q s _ _
    | gap output =>
      have h:=sourcePairQuery_work (always C) (exitOrbit C maps.rightC tail.1 maps.afterC output)
        lo hi sourceCounts base q s prepared.K window
      have hmul:=Nat.mul_le_mul (Nat.le_max_left C.stateCount E.stateCount)
        (Nat.le_max_left C.stateCount E.stateCount)
      have hmul':=Nat.mul_le_mul_left 47 (Nat.mul_le_mul_left prepared.K hmul)
      exact Nat.le_trans h (by unfold cellBudget; omega)
    | suffix output => exact cell_work C E prepared maps tail lo hi sourceCounts targetCounts base q s _ _
  | gap input => exact cell_work C E prepared maps tail lo hi sourceCounts targetCounts base q s _ _
  | suffix input => exact cell_work C E prepared maps tail lo hi sourceCounts targetCounts base q s _ _

theorem filteredCell_direct_first (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (I s R q L H lo hi O : Nat)
    (source target : Array Bool) (base len : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q)
    (hq : 0<q) (hH : q≤H) (hlo : lo≤hi) (hI : I≤s+lo*q)
    (hb : s+hi*q+H≤R) (hn : R≤w.length) (hO : s+hi*q+H≤O) (hOn : O≤w.length)
    (hLH : L≤H) :
    (filteredCell C E prepared
      (contexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        I s H q lo hi O).maps
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s L H).maps lo hi
      (MaskedProgression.build source base len (prepared.K*q)).counts
      (MaskedProgression.build target base len (prepared.K*q)).counts base q s window input output).answer=true ↔
        ∃ k,lo≤k ∧ k≤hi ∧ base≤s+k*q ∧ s+k*q<base+len ∧
          MaskedClusterStage.direct C E w I (s+k*q) L O
            (window.allows (s+k*q) && MaskedProgression.readMask source (s+k*q))
            (MaskedProgression.readMask target (s+k*q)) input=some output := by
  rw [contexts_value C E w I s H q lo hi O hH hlo hI hO hOn,
    replay_value C E w s L H hLH (by omega),filteredCell_words C E prepared _ _ _ _ _ lo hi
      source target base len q s window input output hq]
  have semantic (k : Nat) (hl : lo≤k) (hh : k≤hi) :
      WordCell C E (slice w I (s+lo*q)) (slice w s (s+q))
        (slice w (s+(H-q)) (s+H)) (slice w (s+L) (s+H))
        (slice w (s+hi*q+H) O) lo hi k
        (window.allows (s+k*q) && MaskedProgression.readMask source (s+k*q))
        (MaskedProgression.readMask target (s+k*q)) input output ↔
      MaskedClusterStage.direct C E w I (s+k*q) L O
        (window.allows (s+k*q) && MaskedProgression.readMask source (s+k*q))
        (MaskedProgression.readMask target (s+k*q)) input=some output := by
    have hm:=Nat.mul_le_mul_right q hh
    rw [wordCell_anchored C E w fallback s I s R q L H lo hi k O _ _ input output
      hp hH hl hh hI hb hn hO hOn,
      MaskedClusterStage.anchored_exact C E w s I (s+k*q) L H O _ _ input hLH (by omega)
        (MaskedPeriodic.Text.actual_equal_copies w fallback s R q H k hp hn (by omega))]
  constructor
  · rintro ⟨k,hl,hh,hbase,hbound,hw⟩
    exact ⟨k,hl,hh,hbase,hbound,(semantic k hl hh).mp hw⟩
  · rintro ⟨k,hl,hh,hbase,hbound,hw⟩
    exact ⟨k,hl,hh,hbase,hbound,(semantic k hl hh).mpr hw⟩

end REWB.MaskedCluster
