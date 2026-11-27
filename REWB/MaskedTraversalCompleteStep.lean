import REWB.MaskedTraversalAggregateSequence

/-! Constructive, finite-coded physical paths. These lemmas build the
literal CursorStep relation used by the actual bank compiler; none
assumes the existence of a matrix path or an accepting query answer. -/
namespace REWB.MaskedTraversalComplete
open REWB.Spec REWB.MaskedCluster REWB.MaskedTraversalAggregate
variable {α : Type}

def stageCode (C E : DFA α) (mode : Bool) (state : MaskedClusterStage.State C.stateCount E.stateCount) :
    Fin (2*(MaskedClusterStage.dfa C E).stateCount) := code _ mode (MaskedClusterStage.encode C E state)

theorem partStep_code (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) (p : Part)
    (inputMode outputMode : Bool) (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    partStep C E w L source removed target p (stageCode C E inputMode input) (stageCode C E outputMode output) ↔
      Mutable.Batch.CursorStep C E w p.config.descriptor.first p.config.descriptor.period
        p.config.descriptor.repetitions L p.config.anchor (p.config.descriptor.nextAt w.length)
        p.config.incoming p.config.incomingEnabled inputMode outputMode source removed target
        (p.config.window.gate p.gate) input output := by
  simp only [partStep,stageCode,codeMode_code,decoded,codeState_code,MaskedClusterStage.decode_encode]

theorem pass_step (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) (p : Part)
    (mode : Bool) (state : MaskedClusterStage.State C.stateCount E.stateCount)
    (allowed : modeAllowed p.config.incomingEnabled mode=true) :
    partStep C E w L source removed target p (stageCode C E mode state)
      (stageCode C E false (MaskedClusterStage.read C E
        (slice w (p.input mode) (p.output w.length false)) state)) := by
  rw [partStep_code]
  refine ⟨allowed,?_⟩
  exact Or.inl rfl

theorem chain_single (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) (p : Part)
    (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount))
    (step : partStep C E w L source removed target p i j) :
    PhysicalChain C E w L source removed target [p] i j := ⟨j,step,rfl⟩

theorem chain_append (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) (a b : List Part)
    (i j k : Fin (2*(MaskedClusterStage.dfa C E).stateCount))
    (first : PhysicalChain C E w L source removed target a i j)
    (second : PhysicalChain C E w L source removed target b j k) :
    PhysicalChain C E w L source removed target (a++b) i k := by
  induction a generalizing i with
  | nil =>
    change i=j at first
    subst i
    exact second
  | cons p ps ih =>
    obtain ⟨mid,head,tail⟩:=first
    exact ⟨mid,head,ih mid tail⟩

theorem waiting_chain (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) (parts : List Part) :
    PhysicalChain C E w L source removed target parts
      (stageCode C E false .waiting) (stageCode C E false .waiting) := by
  induction parts with
  | nil => rfl
  | cons p ps ih =>
    exact ⟨stageCode C E false .waiting,
      pass_step C E w L source removed target p false .waiting (by simp only [modeAllowed,Bool.not_false,Bool.true_or]),ih⟩

def jumpMode (n L : Nat) (p : Part) (k : Nat) : Bool :=
  decide (p.config.descriptor.nextAt n<p.config.descriptor.first+k*p.config.descriptor.period+L)

theorem jump_step (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) (p : Part)
    (mode : Bool) (input output : MaskedClusterStage.State C.stateCount E.stateCount) (k : Nat)
    (allowed : modeAllowed p.config.incomingEnabled mode=true) (hk : k≤p.config.descriptor.repetitions)
    (enter : p.input mode≤p.config.descriptor.first+k*p.config.descriptor.period)
    (jump : MaskedClusterStage.direct C E w (p.input mode)
      (p.config.descriptor.first+k*p.config.descriptor.period) L (p.output w.length (jumpMode w.length L p k))
      ((p.config.window.gate p.gate).allows (p.config.descriptor.first+k*p.config.descriptor.period) &&
        Mutable.Batch.currentBit source removed (p.config.descriptor.first+k*p.config.descriptor.period))
      (MaskedProgression.readMask target (p.config.descriptor.first+k*p.config.descriptor.period)) input=some output) :
    partStep C E w L source removed target p (stageCode C E mode input)
      (stageCode C E (jumpMode w.length L p k) output) := by
  rw [partStep_code]
  refine ⟨allowed,?_⟩
  by_cases ho : p.config.descriptor.nextAt w.length<p.config.descriptor.first+k*p.config.descriptor.period+L
  · simp only [jumpMode,ho,decide_true,if_true] at jump ⊢
    exact ⟨k,hk,enter,ho,jump⟩
  · simp only [jumpMode,ho,decide_false,Bool.false_eq_true,if_false] at jump ⊢
    exact Or.inr ⟨k,hk,enter,by omega,jump⟩

theorem source_direct (C E : DFA α) (w : Word α) (I p L O : Nat) (mark target : Bool)
    (hm : mark=true) :
    MaskedClusterStage.direct C E w I p L O mark target .waiting=
      some (.gap (C.run C.initial (slice w (p+L) O))) := by
  simp only [MaskedClusterStage.direct,MaskedClusterStage.read,MaskedClusterStage.jump,hm,if_true,Option.map_some]
  rfl

theorem target_direct (C E : DFA α) (w : Word α) (sourceEnd I p L O : Nat) (source mark : Bool)
    (hI : sourceEnd≤I) (hIp : I≤p) (hm : mark=true) (hC : C.accepts (slice w sourceEnd p)) :
    MaskedClusterStage.direct C E w I p L O source mark
      (.gap (C.run C.initial (slice w sourceEnd I)))=
      some (.suffix (E.run E.initial (slice w (p+L) O))) := by
  have hRun : C.final (C.run (C.run C.initial (slice w sourceEnd I)) (slice w I p))=true := by
    rw [←DFA.run_append,←OuterColumn.slice_split w sourceEnd I p hI hIp]
    exact hC
  simp only [MaskedClusterStage.direct,MaskedClusterStage.read,MaskedClusterStage.jump,hm,Bool.true_and,hRun,if_true,Option.map_some]
  rfl

end REWB.MaskedTraversalComplete
