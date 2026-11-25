import REWB.MaskedClusterLeaderShorten

/-!
Actual event-driven scheduling on one compressed suffix-trie edge.

The occurrence tree is retained throughout the edge.  At a query band
`[lo,hi]` all queued thresholds are strictly below `lo`.  Only after that
band is emitted does the implementation drain the next threshold level.
The final drain is at the parent depth, before any parent occurrence merge.
Equal-depth binary refinements emit no band and perform no drain.

This module constructs and measures the scheduler.  A band is not an
assumed answer to a masked query: executing bank/query callbacks and
establishing their geometry remain separate obligations.  In particular,
the final threshold batch must be carried to the complete parent before
performing any local-anchor reset charged to a complete occurrence class.
-/
namespace REWB.MaskedTraversalEdge
open REWB.MaskedClusterLeaders
variable {h : Nat}

def Clean (length : Nat) (s : MaskedClusterLeaders.State h) : Prop :=
  ∀ e,e∈MaskedThresholdQueue.entries s.queue → e.key<length

@[simp] theorem shorten_occurrences (capacity length : Nat)
    (s : MaskedClusterLeaders.State h) :
    (shorten capacity length s).state.occurrences=s.occurrences := rfl

theorem shorten_clean (capacity old fresh : Nat)
    (s : MaskedClusterLeaders.State h) (hi : Invariant old s) :
    Clean fresh (shorten capacity fresh s).state := by
  exact (MaskedThresholdQueue.drain_spec (h+1) fresh 0 s.queue hi.queueGood).2.2.2.1

structure Boundary where
  length : Nat
  work : Nat
  deriving Repr

/-- One real priority-queue peek.  The clamp makes the recursion terminate
even on malformed external inputs; it is inactive under `Clean`. -/
def next (floor high : Nat) (s : MaskedClusterLeaders.State h) : Boundary :=
  let peek:=MaskedThresholdQueue.takeMax (h+1) s.queue
  ⟨min (high-1) (max floor ((peek.item.map MaskedThresholdQueue.Entry.key).getD floor)),peek.work+8⟩

theorem next_lt (floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hh : floor<high) : (next floor high s).length<high := by
  have hm:=Nat.min_le_left (high-1)
    (max floor (((MaskedThresholdQueue.takeMax (h+1) s.queue).item.map MaskedThresholdQueue.Entry.key).getD floor))
  change min (high-1) _<high
  omega

theorem next_ge (floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hh : floor<high) : floor≤(next floor high s).length := by
  change floor≤min (high-1) (max floor _)
  exact Nat.le_min.mpr ⟨by omega,Nat.le_max_left _ _⟩

theorem next_spec (capacity floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hh : floor<high) (hi : Invariant high s) (hc : Clean high s) :
    (∀ e,e∈MaskedThresholdQueue.entries s.queue → e.key≤(next floor high s).length) ∧
    (floor<(next floor high s).length → 0<(shorten capacity (next floor high s).length s).popped) ∧
    (next floor high s).work≤10*h+24 := by
  have hp:=MaskedThresholdQueue.takeMax_spec (h+1) 0 s.queue hi.queueGood
  have hw : (next floor high s).work≤10*h+24 := by
    change (MaskedThresholdQueue.takeMax (h+1) s.queue).work+8≤10*h+24
    omega
  have hr:=hp.2.1
  cases he : (MaskedThresholdQueue.takeMax (h+1) s.queue).item with
  | none =>
    simp only [MaskedThresholdQueue.Removal,he] at hr
    have hn : (next floor high s).length=floor := by
      simp only [next,he]
      change min (high-1) (max floor floor)=floor
      omega
    refine ⟨?_,?_,hw⟩
    · intro e hm
      rw [hr.1] at hm
      exact False.elim (List.not_mem_nil hm)
    · rw [hn]
      omega
  | some e =>
    simp only [MaskedThresholdQueue.Removal,he] at hr
    have hem : e∈MaskedThresholdQueue.entries s.queue := hr.1.mem_iff.mp List.mem_cons_self
    have hek:=hc e hem
    have hn : (next floor high s).length=max floor e.key := by
      simp only [next,he]
      change min (high-1) (max floor e.key)=max floor e.key
      omega
    refine ⟨?_,?_,hw⟩
    · intro a ha
      rw [hn]
      exact Nat.le_trans (hr.2.2 a ha) (Nat.le_max_right _ _)
    · intro hb
      have hfe : floor<e.key := by rw [hn] at hb; omega
      have hne : (next floor high s).length=e.key := by rw [hn]; omega
      have hd : e∈(MaskedThresholdQueue.drain (h+1) (next floor high s).length s.queue).due :=
        (MaskedThresholdQueue.drain_due_iff (h+1) (next floor high s).length 0 s.queue hi.queueGood e).mpr
          ⟨hem,by omega⟩
      have hl:=List.length_pos_of_mem hd
      have hs:=MaskedThresholdQueue.drain_spec (h+1) (next floor high s).length 0 s.queue hi.queueGood
      rw [hs.2.2.2.2.2] at hl
      exact hl

/-- `crossing` is the actual drain after querying this band.  Its occurrence
tree is identical to `snapshot.occurrences`; its live events are validated
against that same immutable occurrence snapshot. -/
structure Band (h : Nat) where
  lo : Nat
  hi : Nat
  snapshot : MaskedClusterLeaders.State h
  crossing : Shortened h
  deriving Repr

structure Path (h : Nat) where
  state : MaskedClusterLeaders.State h
  bands : List (Band h)
  popped : Nat
  work : Nat
  deriving Repr

/-- Constant-time list cons records chronological bands.  No prefix of the
already produced log, occurrence list, or list of lengths is rescanned. -/
def walk (capacity floor high : Nat) (s : MaskedClusterLeaders.State h) : Path h :=
  if hh : floor<high then
    let boundary:=next floor high s
    let crossing:=shorten capacity boundary.length s
    let tail:=walk capacity floor boundary.length crossing.state
    ⟨tail.state,⟨boundary.length+1,high,s,crossing⟩::tail.bands,
      crossing.popped+tail.popped,boundary.work+crossing.work+tail.work+8⟩
  else ⟨s,[],0,1⟩
termination_by high
decreasing_by exact next_lt floor high s hh

structure Scheduled (h : Nat) where
  initial : Option (Shortened h)
  path : Path h
  deriving Repr

/-- Flush born-due records at the complete child, then process every
positive-width band before returning the parent-depth state.  A refinement
at the same depth is intentionally untouched. -/
def run (capacity floor high : Nat) (s : MaskedClusterLeaders.State h) : Scheduled h :=
  if floor<high then
    let first:=shorten capacity high s
    let rest:=walk capacity floor high first.state
    ⟨some first,{rest with popped:=first.popped+rest.popped,work:=first.work+rest.work+3}⟩
  else ⟨none,⟨s,[],0,1⟩⟩

theorem run_equal (capacity length : Nat) (s : MaskedClusterLeaders.State h) :
    run capacity length length s=⟨none,⟨s,[],0,1⟩⟩ := by
  simp [run]

end REWB.MaskedTraversalEdge
