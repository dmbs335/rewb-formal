import REWB.RegularDFA
import REWB.MaskedFiniteActionMaps

/-! The finite stage machine used by cross-cluster transfer matrices.
Reading preserves the stage; a marked jump advances waiting to C, or
an accepting C state to E. Replaying a local anchor's tail is exactly
skipping the current copy, without inverse DFA transitions. -/
namespace REWB.MaskedClusterStage
open REWB.FiniteRelation REWB.Spec
variable {α : Type}

inductive State (c e : Nat) where
  | waiting : State c e
  | gap : Fin c→State c e
  | suffix : Fin e→State c e
  deriving DecidableEq, Repr

def enumeration (c e : Nat) : Enumeration (State c e) :=
  ⟨.waiting::((List.ofFn (fun q : Fin c=>State.gap q))++
      List.ofFn (fun q : Fin e=>State.suffix q)),by
    intro q
    cases q with
    | waiting => exact List.mem_cons_self
    | gap q => exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨q,rfl⟩))
    | suffix q => exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨q,rfl⟩))⟩

theorem enumeration_size (c e : Nat) : (enumeration c e).elems.length=1+c+e := by
  simp only [enumeration,List.length_cons,List.length_append,List.length_ofFn]
  omega

def read (C E : DFA α) (word : Word α) : State C.stateCount E.stateCount→State C.stateCount E.stateCount
  | .waiting => .waiting
  | .gap q => .gap (C.run q word)
  | .suffix q => .suffix (E.run q word)

theorem read_nil (C E : DFA α) (s : State C.stateCount E.stateCount) : read C E [] s=s := by
  cases s <;> rfl

theorem read_append (C E : DFA α) (u v : Word α) (s : State C.stateCount E.stateCount) :
    read C E (u++v) s=read C E v (read C E u s) := by
  cases s <;> simp only [read,DFA.run_append]

def rank {c e : Nat} : State c e→Nat
  | .waiting => 0
  | .gap _ => 1
  | .suffix _ => 2

theorem read_rank (C E : DFA α) (word : Word α) (s : State C.stateCount E.stateCount) :
    rank (read C E word s)=rank s := by cases s <;> rfl

def final (E : DFA α) {c : Nat} : State c E.stateCount→Bool
  | .suffix q => E.final q
  | _ => false

def machine (C E : DFA α) : RegularDFA.Machine α :=
  ⟨State C.stateCount E.stateCount,inferInstance,enumeration C.stateCount E.stateCount,
    .waiting,(fun q a=>read C E [a] q),final E⟩

theorem machine_run (C E : DFA α) (word : Word α) (s : State C.stateCount E.stateCount) :
    (machine C E).run s word=read C E word s := by
  induction word generalizing s with
  | nil => exact (read_nil C E s).symm
  | cons a word ih =>
    change (machine C E).run (read C E [a] s) word=read C E (a::word) s
    rw [ih]
    exact (read_append C E [a] word s).symm

def dfa (C E : DFA α) : DFA α := (machine C E).toDFA

def encode (C E : DFA α) (s : State C.stateCount E.stateCount) : Fin (dfa C E).stateCount :=
  (machine C E).encode s

def decode (C E : DFA α) (s : Fin (dfa C E).stateCount) : State C.stateCount E.stateCount :=
  (machine C E).decode s

theorem dfa_size (C E : DFA α) : (dfa C E).stateCount=1+C.stateCount+E.stateCount :=
  enumeration_size _ _

theorem decode_encode (C E : DFA α) (s : State C.stateCount E.stateCount) :
    decode C E (encode C E s)=s := RegularDFA.Machine.decode_encode _ _

theorem dfa_run (C E : DFA α) (word : Word α) (s : State C.stateCount E.stateCount) :
    (dfa C E).run (encode C E s) word=encode C E (read C E word s) := by
  change (machine C E).toDFA.run ((machine C E).encode s) word=_
  rw [RegularDFA.Machine.toDFA_run,machine_run]
  rfl

theorem dfa_decode_run (C E : DFA α) (word : Word α) (s : Fin (dfa C E).stateCount) :
    decode C E ((dfa C E).run s word)=read C E word (decode C E s) := by
  induction word generalizing s with
  | nil => exact (read_nil C E (decode C E s)).symm
  | cons a word ih =>
    change decode C E ((dfa C E).run (encode C E (read C E [a] (decode C E s))) word)=_
    rw [ih,decode_encode]
    exact (read_append C E [a] word (decode C E s)).symm

/-- Both marks are immutable inputs for this position. A target mark
does not authorize the initial jump, and a source mark cannot finish C. -/
def jump (C E : DFA α) (source target : Bool) :
    State C.stateCount E.stateCount→Option (State C.stateCount E.stateCount)
  | .waiting => if source then some (.gap C.initial) else none
  | .gap q => if target && C.final q then some (.suffix E.initial) else none
  | .suffix _ => none

theorem jump_rank (C E : DFA α) (source target : Bool)
    (s t : State C.stateCount E.stateCount) (h : jump C E source target s=some t) :
    rank t=rank s+1 := by
  cases s with
  | waiting =>
    simp only [jump] at h
    split at h
    · have hh:=Option.some.inj h
      subst t
      rfl
    · cases h
  | gap q =>
    simp only [jump] at h
    split at h
    · have hh:=Option.some.inj h
      subst t
      rfl
    · cases h
  | suffix q => cases h

def jumpVector (C E : DFA α) (source target : Bool) :
    Vector (Option (Fin (dfa C E).stateCount)) (dfa C E).stateCount :=
  Vector.ofFn fun s=>(jump C E source target (decode C E s)).map (encode C E)

theorem jumpVector_get (C E : DFA α) (source target : Bool) (s : State C.stateCount E.stateCount) :
    (jumpVector C E source target).get (encode C E s)=
      (jump C E source target s).map (encode C E) := by
  simp only [jumpVector,BoundaryIndex.Table.get_ofFn,decode_encode]

theorem jumpVector_decode (C E : DFA α) (source target : Bool) (s : Fin (dfa C E).stateCount) :
    ((jumpVector C E source target).get s).map (decode C E)=
      jump C E source target (decode C E s) := by
  simp only [jumpVector,BoundaryIndex.Table.get_ofFn,Option.map_map]
  cases jump C E source target (decode C E s) <;> simp only [Option.map,Function.comp_apply,decode_encode]

def direct (C E : DFA α) (w : Word α) (I p L O : Nat)
    (source target : Bool) (s : State C.stateCount E.stateCount) :
    Option (State C.stateCount E.stateCount) :=
  (jump C E source target (read C E (slice w I p) s)).map (read C E (slice w (p+L) O))

/-- The local anchor may use a different representative from adjacent
clusters. Its replay tail is read before the post-anchor text. -/
def anchored (C E : DFA α) (w : Word α) (base I p L H O : Nat)
    (source target : Bool) (s : State C.stateCount E.stateCount) :
    Option (State C.stateCount E.stateCount) :=
  (jump C E source target (read C E (slice w I p) s)).map
    (fun t=>read C E (slice w (p+H) O) (read C E (slice w (base+L) (base+H)) t))

theorem slice_tail (w : Word α) (base L H : Nat) :
    (slice w base (base+H)).drop L=slice w (base+L) (base+H) := by
  simp only [slice,Nat.add_sub_cancel_left,List.drop_take,List.drop_drop,Nat.add_sub_add_left]

theorem anchor_tail (w : Word α) (base p L H : Nat)
    (hcopy : slice w base (base+H)=slice w p (p+H)) :
    slice w (base+L) (base+H)=slice w (p+L) (p+H) := by
  rw [←slice_tail,←slice_tail,hcopy]

theorem anchored_exact (C E : DFA α) (w : Word α) (base I p L H O : Nat)
    (source target : Bool) (s : State C.stateCount E.stateCount)
    (hLH : L≤H) (hHO : p+H≤O)
    (hcopy : slice w base (base+H)=slice w p (p+H)) :
    anchored C E w base I p L H O source target s=direct C E w I p L O source target s := by
  have ht:=anchor_tail w base p L H hcopy
  simp only [anchored,direct,ht]
  congr 1
  funext t
  rw [←read_append,←OuterColumn.slice_split w (p+L) (p+H) O (by omega) hHO]

theorem direct_waiting (C E : DFA α) (w : Word α) (I p L O : Nat) (source target : Bool) :
    direct C E w I p L O source target .waiting=
      if source then some (.gap (C.run C.initial (slice w (p+L) O))) else none := by
  simp only [direct,read,jump]
  cases source <;> rfl

theorem direct_gap (C E : DFA α) (w : Word α) (I p L O : Nat) (source target : Bool)
    (q : Fin C.stateCount) :
    direct C E w I p L O source target (.gap q)=
      if target && C.final (C.run q (slice w I p)) then
        some (.suffix (E.run E.initial (slice w (p+L) O))) else none := by
  simp only [direct,read,jump]
  split <;> rfl

theorem direct_suffix (C E : DFA α) (w : Word α) (I p L O : Nat) (source target : Bool)
    (q : Fin E.stateCount) : direct C E w I p L O source target (.suffix q)=none := rfl

/-- Reading and then jumping twice has exactly the C-gap/E-suffix
meaning required by two copies. The first prefix is deliberately ignored
by the waiting stage; the first source position supplies its mark. -/
def twoJumps (C E : DFA α) (before gap after : Word α) (source target : Bool) : Bool :=
  ((jump C E source false (read C E before .waiting)).bind fun s=>
    (jump C E false target (read C E gap s)).map (read C E after)).any (final E)

theorem twoJumps_correct (C E : DFA α) (before gap after : Word α) (source target : Bool) :
    twoJumps C E before gap after source target=true ↔
      source=true ∧ target=true ∧ C.accepts gap ∧ E.accepts after := by
  cases source <;> cases target <;>
    simp [twoJumps,read,jump,final,DFA.accepts]
  by_cases hC : C.final (C.run C.initial gap)=true
  · simp [hC,final]
  · simp [hC,final]

end REWB.MaskedClusterStage
