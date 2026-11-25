import REWB.MaskedTraversalEdgeCost
import REWB.MaskedClusterLeaderTrace

namespace REWB.MaskedTraversalEdge.Regression
open REWB.MaskedClusterLeaders

/-- A structurally recursive evaluator for kernel regression checks of
the well-founded scheduler.  Fuel is consumed per band, never scanned. -/
def evalWalk (capacity floor : Nat) : Nat→Nat→MaskedClusterLeaders.State h→Path h
  | 0,_,s => ⟨s,[],0,1⟩
  | fuel+1,high,s =>
    if floor<high then
      let boundary:=next floor high s
      let crossing:=shorten capacity boundary.length s
      let tail:=evalWalk capacity floor fuel boundary.length crossing.state
      ⟨tail.state,⟨boundary.length+1,high,s,crossing⟩::tail.bands,
        crossing.popped+tail.popped,boundary.work+crossing.work+tail.work+8⟩
    else ⟨s,[],0,1⟩

theorem evalWalk_eq (capacity floor fuel high : Nat) (s : MaskedClusterLeaders.State h)
    (hf : high≤fuel) : evalWalk capacity floor fuel high s=walk capacity floor high s := by
  induction fuel generalizing high s with
  | zero => rw [walk_stop _ _ _ _ (by omega)]; rfl
  | succ fuel ih =>
    by_cases hh : floor<high
    · rw [evalWalk,if_pos hh,walk,dif_pos hh]
      dsimp only
      rw [ih (next floor high s).length _ (by have ht:=next_lt floor high s hh; omega)]
    · rw [evalWalk,if_neg hh,walk_stop _ _ _ _ hh]

theorem walk_eval (capacity floor high : Nat) (s : MaskedClusterLeaders.State h) :
    walk capacity floor high s=evalWalk capacity floor high high s :=
  (evalWalk_eq capacity floor high high s (Nat.le_refl _)).symm

def state : MaskedClusterLeaders.State 4 :=
  (execute 4 12 [.insert 0,.insert 2,.insert 5,.insert 9]).state

def intervals (bs : List (Band h)) : List (Nat×Nat) :=
  bs.map (fun b=>(b.lo,b.hi))

theorem actual_bands : intervals (run 16 0 12 state).path.bands=
    [(8,12),(6,7),(5,5),(4,4),(3,3),(1,2)] := by
  simp only [run,walk_eval]
  decide

/-- The length-4 event is consumed only after the final child query [5,5].
It stays in the final band's crossing batch for complete-parent repair. -/
theorem parent_event_order :
    intervals (run 16 4 12 state).path.bands=[(8,12),(6,7),(5,5)] ∧
    (run 16 4 12 state).path.state.leaders.entries=[0,5,9] ∧
    ((run 16 4 12 state).path.bands.getLast?).map
      (fun b=>b.crossing.live.map (fun e=>e.key))=some [4] := by
  simp only [run,walk_eval]
  decide

theorem equal_depth_untouched :
    (run 16 12 12 state).path.bands=[] ∧
    (run 16 12 12 state).path.popped=0 ∧
    (run 16 12 12 state).initial=none := by
  rw [run_equal]
  exact ⟨rfl,rfl,rfl⟩

def stale : MaskedClusterLeaders.State 4 :=
  (execute 4 20 [.insert 0,.insert 8,.insert 4]).state

/-- Retired high-key records still cost pops, but produce no false live
repair.  The implementation does not obtain its cuts from live-edge scans. -/
theorem stale_threshold_charged :
    intervals (run 16 0 20 stale).path.bands=[(16,20),(9,15),(8,8),(5,7),(1,4)] ∧
    (run 16 0 20 stale).path.popped=6 ∧
    ((run 16 0 20 stale).path.bands.head?).map
      (fun b=>b.crossing.live.length)=some 0 := by
  simp only [run,walk_eval]
  decide

def bornDue : MaskedClusterLeaders.State 4 :=
  (execute 4 3 [.insert 0,.insert 8,.insert 4]).state

theorem born_due_before_first_band :
    ((run 16 0 3 bornDue).initial.map (fun s=>s.popped))=some 6 ∧
    intervals (run 16 0 3 bornDue).path.bands=[(1,3)] := by
  simp only [run,walk_eval]
  decide

/-- A billion-long singleton edge takes one band and no threshold pop. -/
def singleton : MaskedClusterLeaders.State 1 :=
  (execute 1 1000000000 [.insert 0]).state

theorem long_singleton :
    intervals (run 2 0 1000000000 singleton).path.bands=[(1,1000000000)] ∧
    (run 2 0 1000000000 singleton).path.popped=0 ∧
    (run 2 0 1000000000 singleton).path.work=42 := by
  simp only [run,walk_eval]
  decide

end REWB.MaskedTraversalEdge.Regression
