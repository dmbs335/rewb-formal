import REWB.MaskedClusterLeaderShorten

/-! A complete executable insertion/shortening stream for dense-component
leader sets and their threshold queue. Invalid external operations are
ignored with a charge. This does not select the suffix-trie traversal or
repair local-anchor certificates and compiled banks. -/
namespace REWB.MaskedClusterLeaders
open REWB.MaskedOrdered
variable {h : Nat}

structure Execution (h : Nat) where
  state : State h
  length : Nat
  generated : Nat := 0
  popped : Nat := 0
  insertions : Nat := 0
  steps : Nat := 0
  work : Nat := 0
  deriving Repr

def initial (h length : Nat) : Execution h := ⟨empty h,length,0,0,0,0,h+1⟩

structure Valid (out : Execution h) : Prop where
  invariant : Invariant out.length out.state
  future : Future out.length out.state
  balance : out.generated=out.popped+MaskedThresholdQueue.count out.state.queue
  generations : out.generated≤4*out.insertions
  insertions : out.insertions≤out.steps
  measured : out.work≤h+1+(129*h+152)*out.steps+(44*h+66)*out.popped

theorem initial_valid (h length : Nat) : Valid (initial h length) := by
  exact ⟨empty_invariant h length,empty_future h length,rfl,by simp [initial],
    Nat.le_refl _,by simp [initial]⟩

def skip (out : Execution h) : Execution h :=
  {out with steps:=out.steps+1,work:=out.work+2}

theorem skip_valid (out : Execution h) (hv : Valid out) : Valid (skip out) := by
  refine ⟨hv.invariant,hv.future,hv.balance,hv.generations,?_,?_⟩
  · have hi:=hv.insertions
    change out.insertions≤out.steps+1
    omega
  · have hw:=hv.measured
    change out.work+2≤h+1+(129*h+152)*(out.steps+1)+(44*h+66)*out.popped
    rw [Nat.mul_succ]
    omega

def afterAdd (capacity p : Nat) (out : Execution h) : Execution h :=
  let next:=add capacity out.length p out.state
  ⟨next.state,out.length,out.generated+next.generated,out.popped,
    out.insertions+1,out.steps+1,out.work+next.work+3⟩

theorem afterAdd_valid (capacity p : Nat) (out : Execution h) (hv : Valid out)
    (hc : capacity=2^h) (hp : p<capacity) : Valid (afterAdd capacity p out) := by
  have hi:=add_invariant capacity out.length p out.state hv.invariant hc hp
  have hf:=add_future capacity out.length p out.state hv.invariant hv.future hc hp
  have hw:=add_work capacity out.length p out.state hv.invariant hc hp
  have hq:=MaskedThresholdEvents.add_spec h capacity p out.state.occurrences out.state.queue
    hv.invariant.occGood hv.invariant.occFits hc hp hv.invariant.queueGood
  have hb : MaskedThresholdQueue.count (add capacity out.length p out.state).state.queue=
      MaskedThresholdQueue.count out.state.queue+(add capacity out.length p out.state).generated := hq.2.2.1
  refine ⟨hi,hf,?_,?_,?_,?_⟩
  · change out.generated+(add capacity out.length p out.state).generated=
      out.popped+MaskedThresholdQueue.count (add capacity out.length p out.state).state.queue
    rw [hb]
    have hold:=hv.balance
    omega
  · change out.generated+(add capacity out.length p out.state).generated≤4*(out.insertions+1)
    have hold:=hv.generations
    omega
  · change out.insertions+1≤out.steps+1
    have hold:=hv.insertions
    omega
  · change out.work+(add capacity out.length p out.state).work+3≤
      h+1+(129*h+152)*(out.steps+1)+(44*h+66)*out.popped
    rw [Nat.mul_succ]
    have hold:=hv.measured
    omega

def afterShorten (capacity fresh : Nat) (out : Execution h) : Execution h :=
  let next:=shorten capacity fresh out.state
  ⟨next.state,fresh,out.generated,out.popped+next.popped,
    out.insertions,out.steps+1,out.work+next.work+3⟩

theorem afterShorten_valid (capacity fresh : Nat) (out : Execution h) (hv : Valid out)
    (hc : capacity=2^h) (hle : fresh≤out.length) : Valid (afterShorten capacity fresh out) := by
  have hi:=shorten_invariant capacity out.length fresh out.state hv.invariant hv.future hc hle
  have hf:=shorten_future capacity out.length fresh out.state hv.invariant hv.future hle
  have hw:=shorten_work capacity out.length fresh out.state hv.invariant
  refine ⟨hi,hf,?_,hv.generations,?_,?_⟩
  · change out.generated=out.popped+(shorten capacity fresh out.state).popped+
      MaskedThresholdQueue.count (shorten capacity fresh out.state).state.queue
    have hold:=hv.balance
    omega
  · change out.insertions≤out.steps+1
    have hold:=hv.insertions
    omega
  · change out.work+(shorten capacity fresh out.state).work+3≤
      h+1+(129*h+152)*(out.steps+1)+(44*h+66)*(out.popped+(shorten capacity fresh out.state).popped)
    have hold:=hv.measured
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc] at hw hold ⊢
    omega

inductive Operation where
  | insert (position : Nat)
  | lower (length : Nat)
  deriving Repr

def step (capacity : Nat) (op : Operation) (out : Execution h) : Execution h :=
  match op with
  | .insert p => if p<capacity then afterAdd capacity p out else skip out
  | .lower fresh => if fresh≤out.length then afterShorten capacity fresh out else skip out

theorem step_valid (capacity : Nat) (op : Operation) (out : Execution h)
    (hv : Valid out) (hc : capacity=2^h) : Valid (step capacity op out) := by
  cases op with
  | insert p =>
    simp only [step]
    split
    · exact afterAdd_valid capacity p out hv hc ‹_›
    · exact skip_valid out hv
  | lower fresh =>
    simp only [step]
    split
    · exact afterShorten_valid capacity fresh out hv hc ‹_›
    · exact skip_valid out hv

theorem step_steps (capacity : Nat) (op : Operation) (out : Execution h) :
    (step capacity op out).steps=out.steps+1 := by
  cases op <;> simp only [step] <;> split <;> rfl

def executeLoop (capacity : Nat) : List Operation→Execution h→Execution h
  | [],out => out
  | op::ops,out => executeLoop capacity ops (step capacity op out)

theorem executeLoop_valid (capacity : Nat) (ops : List Operation) (out : Execution h)
    (hv : Valid out) (hc : capacity=2^h) : Valid (executeLoop capacity ops out) := by
  induction ops generalizing out with
  | nil => exact hv
  | cons op ops ih => rw [executeLoop]; exact ih _ (step_valid _ _ _ hv hc)

theorem executeLoop_steps (capacity : Nat) (ops : List Operation) (out : Execution h) :
    (executeLoop capacity ops out).steps=out.steps+ops.length := by
  induction ops generalizing out with
  | nil => simp [executeLoop]
  | cons op ops ih => rw [executeLoop,ih,step_steps,List.length_cons]; omega

def execute (h length : Nat) (ops : List Operation) : Execution h :=
  executeLoop (2^h) ops (initial h length)

theorem execute_valid (h length : Nat) (ops : List Operation) : Valid (execute h length ops) :=
  executeLoop_valid _ _ _ (initial_valid h length) rfl

theorem execute_leaders (h length : Nat) (ops : List Operation) (p : Nat) :
    p∈(execute h length ops).state.leaders.entries ↔
      Leader (execute h length ops).state.occurrences.entries (execute h length ops).length p :=
  (execute_valid h length ops).invariant.represented p

theorem execute_work (h length : Nat) (ops : List Operation) :
    (execute h length ops).popped≤4*(execute h length ops).insertions ∧
    (execute h length ops).work≤h+1+(305*h+416)*ops.length := by
  have hv:=execute_valid h length ops
  have hs : (execute h length ops).steps=ops.length := by
    simp only [execute,executeLoop_steps,initial,Nat.zero_add]
  have hp : (execute h length ops).popped≤4*(execute h length ops).insertions := by
    have hbal:=hv.balance
    have hgen:=hv.generations
    omega
  refine ⟨hp,?_⟩
  have hi:=hv.insertions
  rw [hs] at hi
  have hp' : (execute h length ops).popped≤4*ops.length := by omega
  have hm:=Nat.mul_le_mul_left (44*h+66) hp'
  have hw:=hv.measured
  rw [hs] at hw
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm h 4] at hm hw ⊢
  omega

end REWB.MaskedClusterLeaders
