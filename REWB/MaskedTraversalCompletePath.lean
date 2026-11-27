import REWB.MaskedTraversalCompletePass

/-! Two selected jumps in different chronological banks generate a
literal finite-coded path. Every intervening bank is passed once.
The proof constructs the path; it assumes no matrix entry or answer. -/
namespace REWB.MaskedTraversalComplete
open REWB.Spec REWB.MaskedCluster REWB.MaskedTraversalAggregate
variable {α : Type}

def position (p : Part) (k : Nat) : Nat :=
  p.config.descriptor.first+k*p.config.descriptor.period

theorem final_mode (n L : Nat) (p : Part) (ps : List Part) (k : Nat)
    (finish : Bool→Nat) (hc : Continuous n ps (p.output n) finish)
    (hn : finish false=n) (hbound : position p k+L≤n) :
    finishMode ps (jumpMode n L p k)=false := by
  cases ps with
  | nil =>
    cases hc
    have hnext : p.config.descriptor.nextAt n=n := hn
    simp only [finishMode,jumpMode,hnext]
    exact decide_eq_false (by simpa only [position] using Nat.not_lt.mpr hbound)
  | cons q qs => rfl

theorem finish_pass (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool)
    (p : Part) (ps : List Part) (k : Nat) (finish : Bool→Nat)
    (hc : Continuous w.length ps (p.output w.length) finish) (hn : finish false=w.length)
    (safe : ∀q,q∈ps→Safe w.length L q) (enabled : Enabled w.length (p::ps))
    (hk : k≤p.config.descriptor.repetitions) (hL : L≤p.config.anchor)
    (hbound : position p k+L≤w.length)
    (state : MaskedClusterStage.State C.stateCount E.stateCount) :
    PhysicalChain C E w L source removed target ps
      (stageCode C E (jumpMode w.length L p k)
        (MaskedClusterStage.read C E (slice w (position p k+L) (p.output w.length (jumpMode w.length L p k))) state))
      (stageCode C E false (MaskedClusterStage.read C E (slice w (position p k+L) w.length) state)) := by
  have hm:=final_mode w.length L p ps k finish hc hn hbound
  have hp:=pass_chain C E w L source removed target ps (p.output w.length) finish hc safe
    (jumpMode w.length L p k) (admitted_jump w.length L p ps k enabled hk hL)
    (MaskedClusterStage.read C E (slice w (position p k+L) (p.output w.length (jumpMode w.length L p k))) state)
  rw [hm,hn] at hp
  have hleft:=jump_after w.length L p k hk hL
  rw [←MaskedClusterStage.read_append,←OuterColumn.slice_split w (position p k+L)
    (p.output w.length (jumpMode w.length L p k)) w.length hleft hp.1] at hp
  exact hp.2

theorem arrive_target (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool)
    (p q : Part) (between after : List Part) (k l : Nat) (finish : Bool→Nat)
    (hc : Continuous w.length (between++q::after) (p.output w.length) finish)
    (safe : ∀r,r∈between→Safe w.length L r)
    (enabled : Enabled w.length (p::(between++q::after)))
    (incoming : Incoming w.length q)
    (hk : k≤p.config.descriptor.repetitions) (hL : L≤p.config.anchor)
    (hl : l≤q.config.descriptor.repetitions) (horder : position p k+L≤position q l) :
    ∃mode,modeAllowed q.config.incomingEnabled mode=true ∧
      position p k+L≤q.input mode ∧ q.input mode≤position q l ∧
      PhysicalChain C E w L source removed target between
        (stageCode C E (jumpMode w.length L p k)
          (.gap (C.run C.initial (slice w (position p k+L) (p.output w.length (jumpMode w.length L p k))))))
        (stageCode C E mode (.gap (C.run C.initial (slice w (position p k+L) (q.input mode))))) := by
  have hadmit:=admitted_jump w.length L p (between++q::after) k enabled hk hL
  have hend:=jump_after w.length L p k hk hL
  cases between with
  | nil =>
    cases hc with
    | cons _ _ _ _ entry rest =>
      have ha : modeAllowed q.config.incomingEnabled (jumpMode w.length L p k)=true := hadmit
      have he:=entry _ ha
      have hf:=entry false (by simp only [modeAllowed,Bool.not_false,Bool.true_or])
      have henter:=target_entry w.length L p q k l hl hf incoming ha horder
      refine ⟨jumpMode w.length L p k,ha,?_,henter,?_⟩
      · rw [he]; exact hend
      · rw [he]; rfl
  | cons r rs =>
    obtain ⟨middle,hbefore,hafter⟩:=continuous_split w.length (r::rs) (q::after)
      (p.output w.length) finish hc
    have hh:=pass_chain C E w L source removed target (r::rs) (p.output w.length) middle hbefore safe
      (jumpMode w.length L p k) hadmit
      (.gap (C.run C.initial (slice w (position p k+L) (p.output w.length (jumpMode w.length L p k)))))
    simp only [finishMode,MaskedClusterStage.read] at hh
    cases hafter with
    | cons _ _ _ _ entry rest =>
      have hf:=entry false (by simp only [modeAllowed,Bool.not_false,Bool.true_or])
      have hread : C.run (C.run C.initial (slice w (position p k+L) (p.output w.length (jumpMode w.length L p k))))
          (slice w (p.output w.length (jumpMode w.length L p k)) (middle false))=
          C.run C.initial (slice w (position p k+L) (q.input false)) := by
        rw [←DFA.run_append,←OuterColumn.slice_split w (position p k+L)
          (p.output w.length (jumpMode w.length L p k)) (middle false) hend hh.1,←hf]
      rw [hread] at hh
      refine ⟨false,by simp only [modeAllowed,Bool.not_false,Bool.true_or],?_,?_,hh.2⟩
      · rw [hf]; exact Nat.le_trans hend hh.1
      · simp only [Part.input,cursor,Bool.false_eq_true,if_false,position]
        omega

theorem two_jumps (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool)
    (before between after : List Part) (p q : Part) (k l : Nat) (entryAt finish : Bool→Nat)
    (continuous : Continuous w.length (before++p::(between++q::after)) entryAt finish)
    (endAt : finish false=w.length)
    (safe : ∀r,r∈before++p::(between++q::after)→Safe w.length L r)
    (enabled : Enabled w.length (before++p::(between++q::after)))
    (incoming : Incoming w.length q)
    (hk : k≤p.config.descriptor.repetitions) (hl : l≤q.config.descriptor.repetitions)
    (hsource : ((p.config.window.gate p.gate).allows (position p k) && Mutable.Batch.currentBit source removed (position p k))=true)
    (htarget : MaskedProgression.readMask target (position q l)=true)
    (horder : position p k+L≤position q l) (hbound : position q l+L≤w.length)
    (hC : C.accepts (slice w (position p k+L) (position q l))) :
    PhysicalChain C E w L source removed target (before++p::(between++q::after))
      (stageCode C E false .waiting)
      (stageCode C E false (.suffix (E.run E.initial (slice w (position q l+L) w.length)))) := by
  have hp : Safe w.length L p := safe p (List.mem_append_right before List.mem_cons_self)
  have hq : Safe w.length L q := safe q (List.mem_append_right before (List.mem_cons_of_mem p
    (List.mem_append_right between List.mem_cons_self)))
  have hsafeBetween : ∀r,r∈between→Safe w.length L r := by
    intro r hr
    exact safe r (List.mem_append_right before (List.mem_cons_of_mem p (List.mem_append_left _ hr)))
  have hsafeAfter : ∀r,r∈after→Safe w.length L r := by
    intro r hr
    exact safe r (List.mem_append_right before (List.mem_cons_of_mem p
      (List.mem_append_right between (List.mem_cons_of_mem q hr))))
  have henabled:=enabled_append_right w.length before (p::(between++q::after)) enabled
  have htargetEnabled:=enabled_append_right w.length (p::between) (q::after) henabled
  obtain ⟨start,_,hc⟩:=continuous_split w.length before (p::(between++q::after)) entryAt finish continuous
  cases hc with
  | cons _ _ _ _ entry rest =>
    obtain ⟨mode,ha,hI,hIp,hbetween⟩:=arrive_target C E w L source removed target p q between after k l finish
      rest hsafeBetween henabled incoming hk hp.1 hl horder
    have hsourceStep:=jump_step C E w L source removed target p false .waiting
      (.gap (C.run C.initial (slice w (position p k+L) (p.output w.length (jumpMode w.length L p k))))) k
      (by simp only [modeAllowed,Bool.not_false,Bool.true_or]) hk
      (by simp only [Part.input,cursor,Bool.false_eq_true,if_false]; omega)
      (source_direct C E w (p.input false) (position p k) L
        (p.output w.length (jumpMode w.length L p k)) _ _ hsource)
    have htargetStep:=jump_step C E w L source removed target q mode
      (.gap (C.run C.initial (slice w (position p k+L) (q.input mode))))
      (.suffix (E.run E.initial (slice w (position q l+L) (q.output w.length (jumpMode w.length L q l))))) l
      ha hl hIp (target_direct C E w (position p k+L) (q.input mode) (position q l) L
        (q.output w.length (jumpMode w.length L q l)) _ _ hI hIp htarget hC)
    obtain ⟨middle,_,hrest⟩:=continuous_split w.length between (q::after) (p.output w.length) finish rest
    cases hrest with
    | cons _ _ _ _ targetEntry targetRest =>
      have hafter:=finish_pass C E w L source removed target q after l finish targetRest endAt hsafeAfter
        htargetEnabled hl hq.1 hbound (.suffix E.initial)
      have htail : PhysicalChain C E w L source removed target (q::after)
          (stageCode C E mode (.gap (C.run C.initial (slice w (position p k+L) (q.input mode)))))
          (stageCode C E false (.suffix (E.run E.initial (slice w (position q l+L) w.length)))) :=
        ⟨_,htargetStep,hafter⟩
      have hm:=chain_append C E w L source removed target between (q::after) _ _ _ hbetween htail
      have hs : PhysicalChain C E w L source removed target (p::(between++q::after))
          (stageCode C E false .waiting)
          (stageCode C E false (.suffix (E.run E.initial (slice w (position q l+L) w.length)))) :=
        ⟨_,hsourceStep,hm⟩
      exact chain_append C E w L source removed target before (p::(between++q::after)) _ _ _
        (waiting_chain C E w L source removed target before) hs

end REWB.MaskedTraversalComplete
