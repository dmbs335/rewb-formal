import REWB.MaskedTraversalEdgeCorrect

/-! Every nonterminal band consumes an actual queued record.  The final
band may consume none.  All priority peeks, drains, leader updates and log
cells are counted; semantic bank/query callback work is not hidden here. -/
namespace REWB.MaskedTraversalEdge
open REWB.MaskedClusterLeaders
variable {h : Nat}

theorem walk_stop (capacity floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hh : ¬floor<high) : walk capacity floor high s=⟨s,[],0,1⟩ := by
  rw [walk,dif_neg hh]

theorem walk_measured (capacity floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hi : Invariant high s) (hf : Future high s) (hc : capacity=2^h)
    (hclean : Clean high s) :
    (walk capacity floor high s).popped+
      MaskedThresholdQueue.count (walk capacity floor high s).state.queue=
        MaskedThresholdQueue.count s.queue ∧
    (walk capacity floor high s).bands.length≤(walk capacity floor high s).popped+1 ∧
    (walk capacity floor high s).work≤
      (44*h+63)*(walk capacity floor high s).popped+
      (54*h+95)*(walk capacity floor high s).bands.length+1 := by
  induction high using Nat.strongRecOn generalizing s with
  | ind high ih =>
    by_cases hh : floor<high
    · let boundary:=next floor high s
      let crossing:=shorten capacity boundary.length s
      let tail:=walk capacity floor boundary.length crossing.state
      have hlt : boundary.length<high := next_lt floor high s hh
      have hge : floor≤boundary.length := next_ge floor high s hh
      have hsi:=shorten_invariant capacity high boundary.length s hi hf hc (by omega)
      have hsf:=shorten_future capacity high boundary.length s hi hf (by omega)
      have hsc:=shorten_clean capacity high boundary.length s hi
      have ht:=ih boundary.length hlt crossing.state hsi hsf hsc
      have hs:=shorten_work capacity high boundary.length s hi
      have hn:=next_spec capacity floor high s hh hi hclean
      have hb : tail.bands.length+1≤crossing.popped+tail.popped+1 := by
        by_cases hinner : floor<boundary.length
        · have hp:=hn.2.1 hinner
          change 0<crossing.popped at hp
          have htband : tail.bands.length≤tail.popped+1 := ht.2.1
          omega
        · have hstop : tail=⟨crossing.state,[],0,1⟩ := walk_stop _ _ _ _ hinner
          rw [hstop]
          simp
      rw [walk,dif_pos hh]
      change crossing.popped+tail.popped+MaskedThresholdQueue.count tail.state.queue=
          MaskedThresholdQueue.count s.queue ∧
        tail.bands.length+1≤crossing.popped+tail.popped+1 ∧
        boundary.work+crossing.work+tail.work+8≤
          (44*h+63)*(crossing.popped+tail.popped)+(54*h+95)*(tail.bands.length+1)+1
      refine ⟨?_,hb,?_⟩
      · have htb : tail.popped+MaskedThresholdQueue.count tail.state.queue=
            MaskedThresholdQueue.count crossing.state.queue := ht.1
        have hsb : crossing.popped+MaskedThresholdQueue.count crossing.state.queue=
            MaskedThresholdQueue.count s.queue := hs.2
        omega
      · have htw : tail.work≤(44*h+63)*tail.popped+(54*h+95)*tail.bands.length+1 := ht.2.2
        have hsw : crossing.work≤(44*h+63)*(crossing.popped+1) := hs.1
        have hnw : boundary.work≤10*h+24 := hn.2.2
        simp only [Nat.mul_add,Nat.mul_one] at hsw ⊢
        omega
    · rw [walk_stop capacity floor high s hh]
      simp

theorem walk_work (capacity floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hi : Invariant high s) (hf : Future high s) (hc : capacity=2^h)
    (hclean : Clean high s) :
    (walk capacity floor high s).work≤
      (98*h+159)*((walk capacity floor high s).popped+1) := by
  have hm:=walk_measured capacity floor high s hi hf hc hclean
  have hb:=Nat.mul_le_mul_left (54*h+95) hm.2.1
  have hw:=hm.2.2
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at hb hw ⊢
  omega

theorem run_measured (capacity floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hi : Invariant high s) (hf : Future high s) (hc : capacity=2^h) :
    (run capacity floor high s).path.popped+
      MaskedThresholdQueue.count (run capacity floor high s).path.state.queue=
        MaskedThresholdQueue.count s.queue ∧
    (run capacity floor high s).path.bands.length≤(run capacity floor high s).path.popped+1 ∧
    (run capacity floor high s).path.work≤
      (98*h+162)*((run capacity floor high s).path.popped+1) := by
  by_cases hh : floor<high
  · let first:=shorten capacity high s
    let rest:=walk capacity floor high first.state
    have hi1:=shorten_invariant capacity high high s hi hf hc (Nat.le_refl _)
    have hf1:=shorten_future capacity high high s hi hf (Nat.le_refl _)
    have hc1:=shorten_clean capacity high high s hi
    have hm:=walk_measured capacity floor high first.state hi1 hf1 hc hc1
    have hs:=shorten_work capacity high high s hi
    rw [run,if_pos hh]
    change first.popped+rest.popped+MaskedThresholdQueue.count rest.state.queue=
        MaskedThresholdQueue.count s.queue ∧
      rest.bands.length≤first.popped+rest.popped+1 ∧
      first.work+rest.work+3≤(98*h+162)*(first.popped+rest.popped+1)
    have hb : rest.bands.length≤rest.popped+1 := hm.2.1
    have htb : rest.popped+MaskedThresholdQueue.count rest.state.queue=
        MaskedThresholdQueue.count first.state.queue := hm.1
    have hsb : first.popped+MaskedThresholdQueue.count first.state.queue=
        MaskedThresholdQueue.count s.queue := hs.2
    refine ⟨by omega,by omega,?_⟩
    have htw : rest.work≤(44*h+63)*rest.popped+(54*h+95)*rest.bands.length+1 := hm.2.2
    have hsw : first.work≤(44*h+63)*(first.popped+1) := hs.1
    have hbm:=Nat.mul_le_mul_left (54*h+95) hb
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at hsw htw hbm ⊢
    omega
  · rw [run,if_neg hh]
    simp

/-- This bound is independent of the numeric width of the edge. -/
theorem run_work_queue (capacity floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hi : Invariant high s) (hf : Future high s) (hc : capacity=2^h) :
    (run capacity floor high s).path.work≤
      (98*h+162)*(MaskedThresholdQueue.count s.queue+1) := by
  have hm:=run_measured capacity floor high s hi hf hc
  exact Nat.le_trans hm.2.2 (Nat.mul_le_mul_left _ (by omega))

end REWB.MaskedTraversalEdge
