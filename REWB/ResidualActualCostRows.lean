import REWB.ResidualActualDispatch
import REWB.MaskedAllStartRowsCost

/-! The finite variant bank now includes the cost of its actual row
producers. All coefficients depend only on the seven fixed automata and
the fixed construction charge. The outer grid factor is paid once at
construction, not once per residual query. -/
namespace REWB.ResidualActual.Cost
open REWB.BoundaryRange REWB.ResidualCached REWB.ResidualCached.Growth
variable {σ : Nat}

def rowVolume (n s : Nat) : Nat := MaskedAllStart.Rows.Cost.volume n*(n/s+2)

theorem rowVolume_positive (n s : Nat) : 1≤rowVolume n s :=
  Nat.mul_le_mul (MaskedAllStart.Rows.Cost.volume_positive n)
    (Nat.succ_le_succ (Nat.zero_le (n/s+1)))

theorem sum_uniform {m : Nat} (f g : Fin m→Nat) (charge coefficient vol extra : Nat)
    (hv : 1≤vol) (hf : ∀i,f i+charge*g i≤coefficient*vol) :
    (List.ofFn fun i=>f i+extra).sum+charge*(List.ofFn g).sum≤m*(coefficient+extra)*vol := by
  rw [MaskedAllStart.Rows.Cost.sum_charge]
  have he:=Nat.mul_le_mul_left extra hv
  have each : ∀i,(f i+extra)+charge*g i≤(coefficient+extra)*vol := by
    intro i
    have hi:=hf i
    rw [Nat.add_mul]
    simp only [Nat.mul_one] at he
    omega
  simpa only [Nat.mul_assoc] using Table.sum_ofFn_le _ _ each

noncomputable def p1Maximum (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  (List.ofFn fun g : Fin P.G.stateCount=>
    MaskedAllStart.Rows.Cost.boundaryCoefficient P.A P.B P.C (gap P g) P.D charge).sum

noncomputable def p1Coefficient (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  P.G.stateCount*(p1Maximum P charge+6)+12*P.G.stateCount+6

theorem p1_inputs_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (ResidualActual.P1.inputs P w fallback width).work+
      charge*(ResidualActual.P1.inputs P w fallback width).fixedPatternBuilds≤
        p1Coefficient P charge*rowVolume w.length width := by
  let vol:=rowVolume w.length width
  let make:=fun g : Fin P.G.stateCount=>MaskedAllStart.Rows.boundary P.A P.B P.C (gap P g) P.D w fallback width
  have each : ∀g,(make g).work+charge*(make g).fixedPatternBuilds≤p1Maximum P charge*vol := by
    intro g
    have hh:=MaskedAllStart.Rows.Cost.boundary_work P.A P.B P.C (gap P g) P.D w fallback width charge
    have hm:=Nat.mul_le_mul_right vol (MaskedAllStart.Rows.Cost.coefficient_le
      (fun g : Fin P.G.stateCount=>MaskedAllStart.Rows.Cost.boundaryCoefficient P.A P.B P.C (gap P g) P.D charge) g)
    change _≤p1Maximum P charge*vol at hm
    have hh' : (make g).work+charge*(make g).fixedPatternBuilds≤
        MaskedAllStart.Rows.Cost.boundaryCoefficient P.A P.B P.C (gap P g) P.D charge*vol := by
      simpa only [vol,rowVolume,Nat.mul_assoc] using hh
    exact Nat.le_trans hh' hm
  have hv:=rowVolume_positive w.length width
  have hh:=sum_uniform (fun g=>(make g).work) (fun g=>(make g).fixedPatternBuilds) charge
    (p1Maximum P charge) vol 6 hv each
  have ho:=Nat.mul_le_mul_left (12*P.G.stateCount+6) hv
  rw [ResidualActual.P1.inputs_work,ResidualActual.P1.inputs_builds]
  unfold p1Coefficient
  dsimp only [make,vol] at hh
  simp only [Nat.mul_one,Nat.add_mul] at ho ⊢
  omega

noncomputable def p2ForwardMaximum (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  (List.ofFn fun q : Fin P.G.stateCount=>
    (List.ofFn fun c : TableColor.Key P.H=>
      MaskedAllStart.Rows.Cost.forwardCoefficient P.C P.D (suffix P q c) charge).sum).sum

noncomputable def p2BackwardMaximum (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  (List.ofFn fun a : Fin P.A.stateCount=>
    (List.ofFn fun g : Fin P.G.stateCount=>
      MaskedAllStart.Rows.Cost.backwardCoefficient (front P a g) P.C P.D charge).sum).sum

noncomputable def p2ForwardCoefficient (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  P.G.stateCount*(TableColor.count P.H*(p2ForwardMaximum P charge+6)+7)+1

noncomputable def p2BackwardCoefficient (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  P.A.stateCount*(P.G.stateCount*(p2BackwardMaximum P charge+6)+7)+1

def p2Overhead (P : SevenDFA (Fin σ)) : Nat :=
  4*P.G.stateCount+1+4*P.A.stateCount+1+
    P.G.stateCount*(4*TableColor.count P.H+1)+P.A.stateCount*(4*P.G.stateCount+1)+
    12*(P.G.stateCount*TableColor.count P.H+P.A.stateCount*P.G.stateCount)+7

noncomputable def p2Coefficient (P : SevenDFA (Fin σ)) (charge : Nat) : Nat :=
  p2ForwardCoefficient P charge+p2BackwardCoefficient P charge+p2Overhead P

theorem p2_forward_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (ResidualActual.P2.forwardRows P w fallback width).work+
      charge*(List.ofFn fun q : Fin P.G.stateCount=>(List.ofFn fun c : TableColor.Key P.H=>
        (MaskedAllStart.Rows.forward P.C P.D (suffix P q c) w fallback width).fixedPatternBuilds).sum).sum≤
          p2ForwardCoefficient P charge*rowVolume w.length width := by
  let vol:=rowVolume w.length width
  let work:=fun (q : Fin P.G.stateCount) (c : TableColor.Key P.H)=>
    (MaskedAllStart.Rows.forward P.C P.D (suffix P q c) w fallback width).work
  let calls:=fun (q : Fin P.G.stateCount) (c : TableColor.Key P.H)=>
    (MaskedAllStart.Rows.forward P.C P.D (suffix P q c) w fallback width).fixedPatternBuilds
  have each : ∀q c,work q c+charge*calls q c≤p2ForwardMaximum P charge*vol := by
    intro q c
    have hh:=MaskedAllStart.Rows.Cost.forward_work P.C P.D (suffix P q c) w fallback width charge
    have hc:=MaskedAllStart.Rows.Cost.coefficient_le
      (fun c : TableColor.Key P.H=>MaskedAllStart.Rows.Cost.forwardCoefficient P.C P.D (suffix P q c) charge) c
    have hq:=MaskedAllStart.Rows.Cost.coefficient_le
      (fun q : Fin P.G.stateCount=>(List.ofFn fun c : TableColor.Key P.H=>
        MaskedAllStart.Rows.Cost.forwardCoefficient P.C P.D (suffix P q c) charge).sum) q
    have hm:=Nat.mul_le_mul_right vol (Nat.le_trans hc hq)
    change _≤p2ForwardMaximum P charge*vol at hm
    exact Nat.le_trans (by simpa only [vol,rowVolume,Nat.mul_assoc] using hh) hm
  have hv:=rowVolume_positive w.length width
  have inner (q : Fin P.G.stateCount) := sum_uniform (work q) (calls q) charge
    (p2ForwardMaximum P charge) vol 6 hv (each q)
  have outer:=sum_uniform (fun q=>(List.ofFn fun c=>work q c+6).sum)
    (fun q=>(List.ofFn (calls q)).sum) charge
    (TableColor.count P.H*(p2ForwardMaximum P charge+6)) vol 7 hv inner
  rw [ResidualActual.P2.forwardRows_work]
  unfold p2ForwardCoefficient
  dsimp only [work,calls,vol] at outer
  rw [Nat.add_mul,Nat.one_mul]
  have hs : (List.ofFn fun q : Fin P.G.stateCount=>
      (List.ofFn fun c : TableColor.Key P.H=>
        (MaskedAllStart.Rows.forward P.C P.D (suffix P q c) w fallback width).work+6).sum+7).sum+
      charge*(List.ofFn fun q : Fin P.G.stateCount=>(List.ofFn fun c : TableColor.Key P.H=>
        (MaskedAllStart.Rows.forward P.C P.D (suffix P q c) w fallback width).fixedPatternBuilds).sum).sum≤
      P.G.stateCount*(TableColor.count P.H*(p2ForwardMaximum P charge+6)+7)*rowVolume w.length width := outer
  clear outer
  omega

theorem p2_backward_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (ResidualActual.P2.backwardRows P w fallback width).work+
      charge*(List.ofFn fun a : Fin P.A.stateCount=>(List.ofFn fun g : Fin P.G.stateCount=>
        (MaskedAllStart.Rows.backward (front P a g) P.C P.D w fallback width).fixedPatternBuilds).sum).sum≤
          p2BackwardCoefficient P charge*rowVolume w.length width := by
  let vol:=rowVolume w.length width
  let work:=fun (a : Fin P.A.stateCount) (g : Fin P.G.stateCount)=>
    (MaskedAllStart.Rows.backward (front P a g) P.C P.D w fallback width).work
  let calls:=fun (a : Fin P.A.stateCount) (g : Fin P.G.stateCount)=>
    (MaskedAllStart.Rows.backward (front P a g) P.C P.D w fallback width).fixedPatternBuilds
  have each : ∀a g,work a g+charge*calls a g≤p2BackwardMaximum P charge*vol := by
    intro a g
    have hh:=MaskedAllStart.Rows.Cost.backward_work (front P a g) P.C P.D w fallback width charge
    have hg:=MaskedAllStart.Rows.Cost.coefficient_le
      (fun g : Fin P.G.stateCount=>MaskedAllStart.Rows.Cost.backwardCoefficient (front P a g) P.C P.D charge) g
    have ha:=MaskedAllStart.Rows.Cost.coefficient_le
      (fun a : Fin P.A.stateCount=>(List.ofFn fun g : Fin P.G.stateCount=>
        MaskedAllStart.Rows.Cost.backwardCoefficient (front P a g) P.C P.D charge).sum) a
    have hm:=Nat.mul_le_mul_right vol (Nat.le_trans hg ha)
    change _≤p2BackwardMaximum P charge*vol at hm
    exact Nat.le_trans (by simpa only [vol,rowVolume,Nat.mul_assoc] using hh) hm
  have hv:=rowVolume_positive w.length width
  have inner (a : Fin P.A.stateCount) := sum_uniform (work a) (calls a) charge
    (p2BackwardMaximum P charge) vol 6 hv (each a)
  have outer:=sum_uniform (fun a=>(List.ofFn fun g=>work a g+6).sum)
    (fun a=>(List.ofFn (calls a)).sum) charge
    (P.G.stateCount*(p2BackwardMaximum P charge+6)) vol 7 hv inner
  rw [ResidualActual.P2.backwardRows_work]
  unfold p2BackwardCoefficient
  dsimp only [work,calls,vol] at outer
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem p2_inputs_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (ResidualActual.P2.inputs P w fallback width).work+
      charge*(ResidualActual.P2.inputs P w fallback width).fixedPatternBuilds≤
        p2Coefficient P charge*rowVolume w.length width := by
  have hf:=p2_forward_work P w fallback width charge
  have hb:=p2_backward_work P w fallback width charge
  have hv:=rowVolume_positive w.length width
  have ho:=Nat.mul_le_mul_left (p2Overhead P) hv
  rw [ResidualActual.P2.inputs_work,ResidualActual.P2.inputs_builds]
  unfold p2Coefficient p2Overhead at *
  simp only [Nat.mul_one,Nat.mul_add,Nat.add_mul] at ho ⊢
  omega

theorem p1_inputs_profile (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (width : Nat),
      Bound w.length width ((ResidualActual.P1.inputs P w fallback width).work+
        charge*(ResidualActual.P1.inputs P w fallback width).fixedPatternBuilds) 1 0 1 3 coefficient := by
  refine ⟨p1Coefficient P charge,?_⟩
  intro w fallback width
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,MaskedAllStart.Rows.Cost.volume,
    rowVolume,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using p1_inputs_work P w fallback width charge

theorem p2_inputs_profile (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (width : Nat),
      Bound w.length width ((ResidualActual.P2.inputs P w fallback width).work+
        charge*(ResidualActual.P2.inputs P w fallback width).fixedPatternBuilds) 1 0 1 3 coefficient := by
  refine ⟨p2Coefficient P charge,?_⟩
  intro w fallback width
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,MaskedAllStart.Rows.Cost.volume,
    rowVolume,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using p2_inputs_work P w fallback width charge

end REWB.ResidualActual.Cost
