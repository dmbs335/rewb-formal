import REWB.ResidualActualFullCostInputs
import REWB.MaskedAllStartFullCostRowsCost
import REWB.ResidualActualCostRows

/-! The finite variant bank includes the full construction costs of
its actual measured row producers. All coefficients depend only on the seven fixed automata and
the fixed construction charge. The outer grid factor is paid once at
construction, not once per residual query. -/
namespace REWB.ResidualActual.FullCost.Cost
open REWB.BoundaryRange REWB.ResidualCached REWB.ResidualCached.Growth
variable {σ : Nat}

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

export REWB.ResidualActual.Cost (rowVolume rowVolume_positive sum_uniform)

noncomputable def p1Maximum (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  (List.ofFn fun g : Fin P.G.stateCount=>
    MaskedAllStart.FullCost.Rows.Cost.boundaryCoefficient P.A P.B P.C (gap P g) P.D charge).sum

noncomputable def p1Coefficient (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  P.G.stateCount*(p1Maximum P charge+6)+22*P.G.stateCount+11

theorem p1_inputs_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (ResidualActual.FullCost.P1.inputs P w fallback width).2+
      charge*(ResidualActual.FullCost.P1.inputs P w fallback width).1.fixedPatternBuilds≤
        p1Coefficient P charge*rowVolume w.length width := by
  let vol:=rowVolume w.length width
  let make:=fun g : Fin P.G.stateCount=>MaskedAllStart.FullCost.Rows.boundary P.A P.B P.C (gap P g) P.D w fallback width
  have each : ∀g,(make g).2+charge*(make g).1.fixedPatternBuilds≤p1Maximum P charge*vol := by
    intro g
    have hh:=MaskedAllStart.FullCost.Rows.Cost.boundary_work P.A P.B P.C (gap P g) P.D w fallback width charge
    have hm:=Nat.mul_le_mul_right vol (MaskedAllStart.FullCost.Rows.Cost.coefficient_le
      (fun g : Fin P.G.stateCount=>MaskedAllStart.FullCost.Rows.Cost.boundaryCoefficient P.A P.B P.C (gap P g) P.D charge) g)
    change _≤p1Maximum P charge*vol at hm
    have hh' : (make g).2+charge*(make g).1.fixedPatternBuilds≤
        MaskedAllStart.FullCost.Rows.Cost.boundaryCoefficient P.A P.B P.C (gap P g) P.D charge*vol := by
      simpa only [vol,rowVolume,Nat.mul_assoc] using hh
    exact Nat.le_trans hh' hm
  have hv:=rowVolume_positive w.length width
  have hh:=sum_uniform (fun g=>(make g).2) (fun g=>(make g).1.fixedPatternBuilds) charge
    (p1Maximum P charge) vol 6 hv each
  have ho:=Nat.mul_le_mul_left (22*P.G.stateCount+11) hv
  rw [ResidualActual.FullCost.P1.inputs_work,ResidualActual.FullCost.P1.inputs_builds]
  unfold p1Coefficient
  dsimp only [make,vol] at hh
  simp only [Nat.mul_one,Nat.add_mul] at ho ⊢
  omega

noncomputable def p2ForwardMaximum (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  (List.ofFn fun q : Fin P.G.stateCount=>
    (List.ofFn fun c : TableColor.Key P.H=>
      MaskedAllStart.FullCost.Rows.Cost.forwardCoefficient P.C P.D (suffix P q c) charge).sum).sum

noncomputable def p2BackwardMaximum (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  (List.ofFn fun a : Fin P.A.stateCount=>
    (List.ofFn fun g : Fin P.G.stateCount=>
      MaskedAllStart.FullCost.Rows.Cost.backwardCoefficient (front P a g) P.C P.D charge).sum).sum

noncomputable def p2ForwardCoefficient (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  P.G.stateCount*(TableColor.count P.H*(p2ForwardMaximum P charge+6)+(10*TableColor.count P.H+12))+(10*P.G.stateCount+6)

noncomputable def p2BackwardCoefficient (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  P.A.stateCount*(P.G.stateCount*(p2BackwardMaximum P charge+6)+(10*P.G.stateCount+12))+(10*P.A.stateCount+6)

def p2Overhead (P : SevenDFA (Fin σ)) : Nat :=
  4*P.G.stateCount+1+4*P.A.stateCount+1+
    P.G.stateCount*(4*TableColor.count P.H+1)+P.A.stateCount*(4*P.G.stateCount+1)+
    12*(P.G.stateCount*TableColor.count P.H+P.A.stateCount*P.G.stateCount)+7

noncomputable def p2Coefficient (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  p2ForwardCoefficient P charge+p2BackwardCoefficient P charge+p2Overhead P

theorem p2_forward_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (ResidualActual.FullCost.P2.forwardRows P w fallback width).2+
      charge*(List.ofFn fun q : Fin P.G.stateCount=>(List.ofFn fun c : TableColor.Key P.H=>
        (MaskedAllStart.FullCost.Rows.forward P.C P.D (suffix P q c) w fallback width).1.fixedPatternBuilds).sum).sum≤
          p2ForwardCoefficient P charge*rowVolume w.length width := by
  let vol:=rowVolume w.length width
  let work:=fun (q : Fin P.G.stateCount) (c : TableColor.Key P.H)=>
    (MaskedAllStart.FullCost.Rows.forward P.C P.D (suffix P q c) w fallback width).2
  let calls:=fun (q : Fin P.G.stateCount) (c : TableColor.Key P.H)=>
    (MaskedAllStart.FullCost.Rows.forward P.C P.D (suffix P q c) w fallback width).1.fixedPatternBuilds
  have each : ∀q c,work q c+charge*calls q c≤p2ForwardMaximum P charge*vol := by
    intro q c
    have hh:=MaskedAllStart.FullCost.Rows.Cost.forward_work P.C P.D (suffix P q c) w fallback width charge
    have hc:=MaskedAllStart.FullCost.Rows.Cost.coefficient_le
      (fun c : TableColor.Key P.H=>MaskedAllStart.FullCost.Rows.Cost.forwardCoefficient P.C P.D (suffix P q c) charge) c
    have hq:=MaskedAllStart.FullCost.Rows.Cost.coefficient_le
      (fun q : Fin P.G.stateCount=>(List.ofFn fun c : TableColor.Key P.H=>
        MaskedAllStart.FullCost.Rows.Cost.forwardCoefficient P.C P.D (suffix P q c) charge).sum) q
    have hm:=Nat.mul_le_mul_right vol (Nat.le_trans hc hq)
    change _≤p2ForwardMaximum P charge*vol at hm
    exact Nat.le_trans (by simpa only [vol,rowVolume,Nat.mul_assoc] using hh) hm
  have hv:=rowVolume_positive w.length width
  have inner (q : Fin P.G.stateCount) := sum_uniform (work q) (calls q) charge
    (p2ForwardMaximum P charge) vol 6 hv (each q)
  have outer:=sum_uniform (fun q=>(List.ofFn fun c=>work q c+6).sum)
    (fun q=>(List.ofFn (calls q)).sum) charge
    (TableColor.count P.H*(p2ForwardMaximum P charge+6)) vol (10*TableColor.count P.H+12) hv inner
  have ho:=Nat.mul_le_mul_left (10*P.G.stateCount+6) hv
  have collapse (x m : Nat) : x+1+10*m+5+6=x+(10*m+12) := by omega
  have collapseOuter (x m : Nat) : x+1+10*m+5=x+(10*m+6) := by omega
  rw [ResidualActual.FullCost.P2.forwardRows_work]
  simp only [collapse]
  rw [collapseOuter]
  have combined:=Nat.add_le_add outer ho
  simpa only [work,calls,vol,p2ForwardCoefficient,Nat.mul_one,Nat.add_mul,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.reduceAdd] using combined

theorem p2_backward_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (ResidualActual.FullCost.P2.backwardRows P w fallback width).2+
      charge*(List.ofFn fun a : Fin P.A.stateCount=>(List.ofFn fun g : Fin P.G.stateCount=>
        (MaskedAllStart.FullCost.Rows.backward (front P a g) P.C P.D w fallback width).1.fixedPatternBuilds).sum).sum≤
          p2BackwardCoefficient P charge*rowVolume w.length width := by
  let vol:=rowVolume w.length width
  let work:=fun (a : Fin P.A.stateCount) (g : Fin P.G.stateCount)=>
    (MaskedAllStart.FullCost.Rows.backward (front P a g) P.C P.D w fallback width).2
  let calls:=fun (a : Fin P.A.stateCount) (g : Fin P.G.stateCount)=>
    (MaskedAllStart.FullCost.Rows.backward (front P a g) P.C P.D w fallback width).1.fixedPatternBuilds
  have each : ∀a g,work a g+charge*calls a g≤p2BackwardMaximum P charge*vol := by
    intro a g
    have hh:=MaskedAllStart.FullCost.Rows.Cost.backward_work (front P a g) P.C P.D w fallback width charge
    have hg:=MaskedAllStart.FullCost.Rows.Cost.coefficient_le
      (fun g : Fin P.G.stateCount=>MaskedAllStart.FullCost.Rows.Cost.backwardCoefficient (front P a g) P.C P.D charge) g
    have ha:=MaskedAllStart.FullCost.Rows.Cost.coefficient_le
      (fun a : Fin P.A.stateCount=>(List.ofFn fun g : Fin P.G.stateCount=>
        MaskedAllStart.FullCost.Rows.Cost.backwardCoefficient (front P a g) P.C P.D charge).sum) a
    have hm:=Nat.mul_le_mul_right vol (Nat.le_trans hg ha)
    change _≤p2BackwardMaximum P charge*vol at hm
    exact Nat.le_trans (by simpa only [vol,rowVolume,Nat.mul_assoc] using hh) hm
  have hv:=rowVolume_positive w.length width
  have inner (a : Fin P.A.stateCount) := sum_uniform (work a) (calls a) charge
    (p2BackwardMaximum P charge) vol 6 hv (each a)
  have outer:=sum_uniform (fun a=>(List.ofFn fun g=>work a g+6).sum)
    (fun a=>(List.ofFn (calls a)).sum) charge
    (P.G.stateCount*(p2BackwardMaximum P charge+6)) vol (10*P.G.stateCount+12) hv inner
  have ho:=Nat.mul_le_mul_left (10*P.A.stateCount+6) hv
  have collapse (x m : Nat) : x+1+10*m+5+6=x+(10*m+12) := by omega
  rw [ResidualActual.FullCost.P2.backwardRows_work]
  simp only [collapse]
  unfold p2BackwardCoefficient
  dsimp only [work,calls,vol] at outer
  simp only [Nat.mul_one,Nat.add_mul] at ho ⊢
  simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.reduceAdd] at outer ⊢
  omega

theorem p2_inputs_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (ResidualActual.FullCost.P2.inputs P w fallback width).2+
      charge*(ResidualActual.FullCost.P2.inputs P w fallback width).1.fixedPatternBuilds≤
        p2Coefficient P charge*rowVolume w.length width := by
  have hf:=p2_forward_work P w fallback width charge
  have hb:=p2_backward_work P w fallback width charge
  have hv:=rowVolume_positive w.length width
  have ho:=Nat.mul_le_mul_left (p2Overhead P) hv
  rw [ResidualActual.FullCost.P2.inputs_work,ResidualActual.FullCost.P2.inputs_builds]
  unfold p2Coefficient p2Overhead at *
  simp only [Nat.mul_one,Nat.mul_add,Nat.add_mul] at ho ⊢
  omega

theorem p1_inputs_profile (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (width : Nat),
      Bound w.length width ((ResidualActual.FullCost.P1.inputs P w fallback width).2+
        charge*(ResidualActual.FullCost.P1.inputs P w fallback width).1.fixedPatternBuilds) 1 0 1 3 coefficient := by
  refine ⟨p1Coefficient P charge,?_⟩
  intro w fallback width
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,MaskedAllStart.FullCost.Rows.Cost.volume,
    rowVolume,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using p1_inputs_work P w fallback width charge

theorem p2_inputs_profile (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (width : Nat),
      Bound w.length width ((ResidualActual.FullCost.P2.inputs P w fallback width).2+
        charge*(ResidualActual.FullCost.P2.inputs P w fallback width).1.fixedPatternBuilds) 1 0 1 3 coefficient := by
  refine ⟨p2Coefficient P charge,?_⟩
  intro w fallback width
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,MaskedAllStart.FullCost.Rows.Cost.volume,
    rowVolume,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using p2_inputs_work P w fallback width charge

end REWB.ResidualActual.FullCost.Cost
