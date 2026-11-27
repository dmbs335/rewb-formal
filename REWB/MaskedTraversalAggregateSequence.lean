import REWB.MaskedTraversalAggregateBand

/-! Exact bank-product paths and physical cursor continuity. A sequence
contains actual configurations and source gates, not answer predicates.
The caller must establish slot/tree coherence and neighboring cursor
compatibility from the repair execution. Once those invariants hold,
the matrix path has unconditional soundness for the original slices.
-/
namespace REWB.MaskedTraversalAggregate
open REWB.MaskedFiniteAction REWB.MaskedCluster
variable {α : Type}

structure Part where
  config : Mutable.Store.Config
  gate : Bool

def Part.input (p : Part) (mode : Bool) : Nat :=
  cursor p.config.descriptor.first p.config.incoming mode

def Part.output (p : Part) (n : Nat) (mode : Bool) : Nat :=
  outputCursor p.config.descriptor.first p.config.descriptor.period p.config.descriptor.repetitions
    p.config.anchor (p.config.descriptor.nextAt n) mode

def decoded (C E : DFA α) (i : Fin (2*(MaskedClusterStage.dfa C E).stateCount)) :
    MaskedClusterStage.State C.stateCount E.stateCount :=
  MaskedClusterStage.decode C E (codeState _ i)

def partStep (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) (p : Part)
    (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount)) : Prop :=
  let d:=p.config.descriptor
  Mutable.Batch.CursorStep C E w d.first d.period d.repetitions L p.config.anchor
    (d.nextAt w.length) p.config.incoming p.config.incomingEnabled (codeMode _ i) (codeMode _ j)
    source removed target (p.config.window.gate p.gate) (decoded C E i) (decoded C E j)

def PhysicalChain (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) :
    List Part→Fin (2*(MaskedClusterStage.dfa C E).stateCount)→
      Fin (2*(MaskedClusterStage.dfa C E).stateCount)→Prop
  | [],i,j => i=j
  | p::ps,i,j => ∃mid,partStep C E w L source removed target p i mid ∧
      PhysicalChain C E w L source removed target ps mid j

inductive Denotes (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool)
    (key : Fin (ReplayMaps.count C.stateCount E.stateCount)) :
    List (View (ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount))→List Part→Prop where
  | nil : Denotes C E w L source removed target key [] []
  | cons {v p vs ps}
      (cell : ∀i j,v key i j=true ↔ partStep C E w L source removed target p i j)
      (rest : Denotes C E w L source removed target key vs ps) :
      Denotes C E w L source removed target key (v::vs) (p::ps)
  | skip {v vs ps}
      (cell : ∀i j,v key i j=true ↔ i=j)
      (rest : Denotes C E w L source removed target key vs ps) :
      Denotes C E w L source removed target key (v::vs) ps

theorem chain_denotes (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool)
    (key : Fin (ReplayMaps.count C.stateCount E.stateCount))
    (cells : List (View (ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)))
    (parts : List Part) (hd : Denotes C E w L source removed target key cells parts)
    (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount)) :
    Chain key cells i j ↔ PhysicalChain C E w L source removed target parts i j := by
  induction hd generalizing i with
  | nil => rfl
  | cons hv ht ih => simp only [Chain,PhysicalChain,hv,ih]
  | skip hv ht ih =>
    simp only [Chain,hv,ih]
    constructor
    · rintro ⟨mid,he,hh⟩
      subst mid
      exact hh
    · intro hh
      exact ⟨i,rfl,hh⟩

theorem denotes_append (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool)
    (key : Fin (ReplayMaps.count C.stateCount E.stateCount))
    {a b : List (View (ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount))}
    {ps qs : List Part}
    (ha : Denotes C E w L source removed target key a ps)
    (hb : Denotes C E w L source removed target key b qs) :
    Denotes C E w L source removed target key (a++b) (ps++qs) := by
  induction ha with
  | nil => exact hb
  | cons hv ht ih => exact Denotes.cons hv ih
  | skip hv ht ih => exact Denotes.skip hv ih

/-- Interfaces are numerical cursor positions, with a separate position
for overshoot. Disabled incoming modes impose no artificial equality. -/
inductive Continuous (n : Nat) : List Part→(Bool→Nat)→(Bool→Nat)→Prop where
  | nil (entryAt : Bool→Nat) : Continuous n [] entryAt entryAt
  | cons (p : Part) (ps : List Part) (entryAt finish : Bool→Nat)
      (entry : ∀mode,modeAllowed p.config.incomingEnabled mode=true→p.input mode=entryAt mode)
      (rest : Continuous n ps (p.output n) finish) : Continuous n (p::ps) entryAt finish

def Safe (n L : Nat) (p : Part) : Prop :=
  L≤p.config.anchor ∧ ∀mode,modeAllowed p.config.incomingEnabled mode=true→
    p.input mode≤p.config.descriptor.nextAt n

def Marks (sourceMask : Array Bool) (removed : List Nat) (targetMask : Array Bool)
    (source target : Nat→Prop) (p : Part) : Prop :=
  (∀k,k≤p.config.descriptor.repetitions→
    (p.config.window.gate p.gate).allows (p.config.descriptor.first+k*p.config.descriptor.period)=true→
    Mutable.Batch.currentBit sourceMask removed (p.config.descriptor.first+k*p.config.descriptor.period)=true→
      source (p.config.descriptor.first+k*p.config.descriptor.period)) ∧
  (∀k,k≤p.config.descriptor.repetitions→
    MaskedProgression.readMask targetMask (p.config.descriptor.first+k*p.config.descriptor.period)=true→
      target (p.config.descriptor.first+k*p.config.descriptor.period))

theorem physical_meaning (C E : DFA α) (w : Word α) (L : Nat)
    (sourceMask : Array Bool) (removed : List Nat) (targetMask : Array Bool)
    (source target : Nat→Prop) (parts : List Part) (entryAt finish : Bool→Nat)
    (continuous : Continuous w.length parts entryAt finish)
    (safe : ∀p,p∈parts→Safe w.length L p)
    (marks : ∀p,p∈parts→Marks sourceMask removed targetMask source target p)
    (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount))
    (path : PhysicalChain C E w L sourceMask removed targetMask parts i j)
    (initial : Meaning C E w L (entryAt (codeMode _ i)) source target (decoded C E i)) :
    Meaning C E w L (finish (codeMode _ j)) source target (decoded C E j) := by
  induction continuous generalizing i with
  | nil entryAt =>
    change i=j at path
    subst j
    exact initial
  | cons p ps entryAt finish entry rest ih =>
    obtain ⟨mid,step,tail⟩:=path
    have hp:=safe p List.mem_cons_self
    have hm:=marks p List.mem_cons_self
    have enabled : modeAllowed p.config.incomingEnabled (codeMode _ i)=true := step.1
    have start : Meaning C E w L (p.input (codeMode _ i)) source target (decoded C E i) := by
      rw [entry _ enabled]
      exact initial
    have next:=meaning_cursor C E w p.config.descriptor.first p.config.descriptor.period
      p.config.descriptor.repetitions L p.config.anchor (p.config.descriptor.nextAt w.length)
      p.config.incoming p.config.incomingEnabled (codeMode _ i) (codeMode _ mid)
      sourceMask removed targetMask (p.config.window.gate p.gate) source target
      (decoded C E i) (decoded C E mid) hp.1 (hp.2 _ enabled) hm.1 hm.2 start step
    exact ih (fun q hq=>safe q (List.mem_cons_of_mem p hq))
      (fun q hq=>marks q (List.mem_cons_of_mem p hq)) mid tail next

theorem physical_final (C E : DFA α) (w : Word α) (L : Nat)
    (sourceMask : Array Bool) (removed : List Nat) (targetMask : Array Bool)
    (source target : Nat→Prop) (parts : List Part) (entryAt finish : Bool→Nat)
    (continuous : Continuous w.length parts entryAt finish) (endAt : finish false=w.length)
    (safe : ∀p,p∈parts→Safe w.length L p)
    (marks : ∀p,p∈parts→Marks sourceMask removed targetMask source target p)
    (q : Fin E.stateCount) (hf : E.final q=true)
    (path : PhysicalChain C E w L sourceMask removed targetMask parts
      (code _ false (MaskedClusterStage.encode C E .waiting))
      (code _ false (MaskedClusterStage.encode C E (.suffix q)))) :
    ∃p j,source p ∧ target j ∧ p+L≤j ∧ j+L≤w.length ∧
      C.accepts (Spec.slice w (p+L) j) ∧ E.accepts (Spec.slice w (j+L) w.length) := by
  have hm:=physical_meaning C E w L sourceMask removed targetMask source target parts entryAt finish
    continuous safe marks _ _ path (by
      simp only [decoded,codeState_code,MaskedClusterStage.decode_encode,Meaning])
  simp only [decoded,codeState_code,MaskedClusterStage.decode_encode,codeMode_code,endAt] at hm
  exact meaning_final C E w L source target (.suffix q) hm hf

theorem masked_of_final (B C E : DFA α) (w : Word α) (L : Nat)
    (source target : Nat→Prop) (mask : Nat→Bool)
    (htarget : ∀j,target j→mask j=true)
    (hcopy : ∀p j,source p→target j→Spec.slice w p (p+L)=Spec.slice w j (j+L))
    (hB : ∀p,source p→B.accepts (Spec.slice w p (p+L)))
    (hf : ∃p j,source p ∧ target j ∧ p+L≤j ∧ j+L≤w.length ∧
      C.accepts (Spec.slice w (p+L) j) ∧ E.accepts (Spec.slice w (j+L) w.length)) :
    ∃p,source p ∧ Spec.maskedStart B C E w mask p := by
  obtain ⟨p,j,hp,hj,hpj,hjn,hC,hE⟩:=hf
  exact ⟨p,hp,p+L,j,j+L,by omega,hpj,by omega,hjn,htarget j hj,
    hcopy p j hp hj,hB p hp,hC,hE⟩

/-- The actual aggregate/shared-cut answer is sound once the stored
current-bank and adjacent-cursor invariants have been established. These
remain explicit execution obligations, rather than supplied answers. -/
theorem queryBand_sound {h : Nat} (B C E : DFA α) (w : Word α) (tree : BankTree C E h)
    (hg : tree.Good) (sourceLo sourceHi representative lengthLo lengthHi old : Nat)
    (hl : lengthLo≤lengthHi) (hh : lengthHi≤old) (hn : representative+old≤w.length)
    (sourceMask : Array Bool) (removed : List Nat) (targetMask : Array Bool)
    (source target : Nat→Prop) (parts : List Part) (entryAt finish : Bool→Nat)
    (continuous : Continuous w.length parts entryAt finish) (endAt : finish false=w.length)
    (denotes : ∀L,lengthLo≤L→L≤lengthHi→Denotes C E w L sourceMask removed targetMask
      (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+L) (representative+old))))
      (regionCells tree.leaves sourceLo sourceHi) parts)
    (safe : ∀L,lengthLo≤L→L≤lengthHi→∀p,p∈parts→Safe w.length L p)
    (marks : ∀p,p∈parts→Marks sourceMask removed targetMask source target p)
    (targetPresent : ∀j,target j→MaskedProgression.readMask targetMask j=true)
    (sourceCopies : ∀L,lengthLo≤L→L≤lengthHi→∀p,source p→
      Spec.slice w p (p+L)=Spec.slice w representative (representative+L))
    (targetCopies : ∀L,lengthLo≤L→L≤lengthHi→∀j,target j→
      Spec.slice w j (j+L)=Spec.slice w representative (representative+L))
    (accepted : (queryBand B C E (Cut.build B C E w) tree sourceLo sourceHi representative lengthLo lengthHi old).answer=true) :
    ∃p,source p ∧ Spec.maskedStart B C E w (MaskedProgression.readMask targetMask) p := by
  obtain ⟨L,hlo,hhi,hB,q,hq,hpath⟩:=(queryBand_correct B C E w tree hg sourceLo sourceHi
    representative lengthLo lengthHi old hl hh hn).mp accepted
  have literal:=(chain_denotes C E w L sourceMask removed targetMask _ _ parts
    (denotes L hlo hhi) _ _).mp hpath
  have finalState:=physical_final C E w L sourceMask removed targetMask source target parts entryAt finish
    continuous endAt (safe L hlo hhi) marks q hq literal
  exact masked_of_final B C E w L source target (MaskedProgression.readMask targetMask) targetPresent
    (fun p j hp hj=>(sourceCopies L hlo hhi p hp).trans (targetCopies L hlo hhi j hj).symm)
    (fun p hp=>by rw [sourceCopies L hlo hhi p hp]; exact hB) finalState

end REWB.MaskedTraversalAggregate
