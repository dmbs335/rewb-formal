import REWB.PeriodicConstructionSystems
import REWB.P1Events

/-! Actual counted schedules for the external periodic P1/P2 branches.
The list constructors below enumerate only the existing phase layouts;
there is no loop over possible exponent values. Each nested range,
map, flattening append and result record is charged where it is built.
The counters use the same unit arithmetic/list model as
`PeriodicConstruction`, rather than a machine bit-cost model. -/
namespace REWB.PeriodicActual.Choices
open REWB.PeriodicConstruction

def mapRange (n : Nat) (f : Nat → α) : Result (List α) :=
  let xs := CountedProjection.range n
  let ys := CountedProjection.map (fun i => (f i, 1)) xs.1
  (ys.1, xs.2 + ys.2 + 1)

theorem mapRange_value (n : Nat) (f : Nat → α) :
    (mapRange n f).1 = (List.range n).map f := by
  simp only [mapRange, CountedProjection.map_value, CountedProjection.range_value]

theorem mapRange_work (n : Nat) (f : Nat → α) :
    (mapRange n f).2 = 4*n+3 := by
  simp only [mapRange, CountedProjection.range_value,
    CountedProjection.map_plain_steps, List.length_range]
  have hr := CountedProjection.rangeFrom_steps 0 n
  change (CountedProjection.range n).2 + (n*(1+1)+1) + 1 = _
  change (CountedProjection.rangeFrom 0 n).2 + (n*(1+1)+1) + 1 = _
  rw [hr]
  omega

def flatRange (n : Nat) (f : Nat → Result (List α)) : Result (List α) :=
  let xs := CountedProjection.range n
  let ys := CountedProjection.flatMap f xs.1
  (ys.1, xs.2 + ys.2 + 1)

theorem flatRange_value (n : Nat) (f : Nat → Result (List α)) :
    (flatRange n f).1 = (List.range n).flatMap (fun i => (f i).1) := by
  simp only [flatRange, CountedProjection.flatMap_value, CountedProjection.range_value]

theorem flat_length (xs : List α) (f : α → List β) (k : Nat)
    (h : ∀ x, x ∈ xs → (f x).length = k) :
    (xs.flatMap f).length = xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem flatRange_length (n k : Nat) (f : Nat → Result (List α))
    (h : ∀ i, i<n → (f i).1.length=k) :
    (flatRange n f).1.length=n*k := by
  rw [flatRange_value, flat_length _ _ k
    (fun i hi => h i (List.mem_range.mp hi)), List.length_range]

theorem flatRange_work (n C L : Nat) (f : Nat → Result (List α))
    (hc : ∀ i, i<n → (f i).2≤C) (hl : ∀ i, i<n → (f i).1.length≤L) :
    (flatRange n f).2≤n*(C+L+4)+3 := by
  have hh := PeriodicConstruction.flatMap_bound f (List.range n) C L
    (fun i hi => hc i (List.mem_range.mp hi))
    (fun i hi => hl i (List.mem_range.mp hi))
  simp only [List.length_range] at hh
  unfold flatRange
  dsimp only
  rw [CountedProjection.range_value]
  have hr := CountedProjection.rangeFrom_steps 0 n
  change (CountedProjection.rangeFrom 0 n).2 + _ + 1 ≤ _
  rw [hr]
  simp only [Nat.mul_add] at hh ⊢
  omega

def Sized (q d C : Nat) (r : Result (List α)) : Prop :=
  r.1.length=q^d ∧ r.2≤C*q^d

theorem mapRange_sized (q : Nat) (hq : 0<q) (f : Nat → α) :
    Sized q 1 7 (mapRange q f) := by
  constructor
  · simp only [mapRange_value, List.length_map, List.length_range, Nat.pow_one]
  · rw [mapRange_work, Nat.pow_one]
    omega

theorem flatRange_sized (q d C : Nat) (hq : 0<q)
    (f : Nat → Result (List α))
    (hf : ∀ i, i<q → Sized q d C (f i)) :
    Sized q (d+1) (C+8) (flatRange q f) := by
  constructor
  · rw [flatRange_length q (q^d) f (fun i hi => (hf i hi).1), Nat.pow_succ]
    exact Nat.mul_comm _ _
  · have hh := flatRange_work q (C*q^d) (q^d) f
      (fun i hi => (hf i hi).2) (fun i hi => Nat.le_of_eq (hf i hi).1)
    have hp : 1≤q^d := Nat.pow_pos hq
    have hqpow : q≤q*q^d := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left q hp
    have hpos : 1≤q*q^d := Nat.mul_pos hq (Nat.pow_pos hq)
    have he : (C+8)*q^(d+1)=q*(C*q^d)+8*(q*q^d) := by
      rw [Nat.pow_succ, Nat.add_mul]
      ac_rfl
    rw [he]
    simp only [Nat.mul_add] at hh
    omega

def p2 (q : Nat) : Result (List P2Periodic.Five) :=
  flatRange q fun p =>
    flatRange q fun i =>
      flatRange q fun a =>
        flatRange q fun j =>
          mapRange q fun e => ⟨p,i,a,j,e⟩

theorem p2_value (q : Nat) : (p2 q).1=P2Periodic.choices q := by
  simp only [p2, flatRange_value, mapRange_value, P2Periodic.choices]

theorem p2_sized (q : Nat) (hq : 0<q) : Sized q 5 39 (p2 q) := by
  apply flatRange_sized q 4 31 hq
  intro p _
  apply flatRange_sized q 3 23 hq
  intro i _
  apply flatRange_sized q 2 15 hq
  intro a _
  apply flatRange_sized q 1 7 hq
  intro j _
  exact mapRange_sized q hq _

def p1 (q : Nat) : Result (List P1PhaseFamily.Three) :=
  flatRange q fun j => flatRange q fun e => mapRange q fun rho => ⟨j,e,rho⟩

theorem p1_value (q : Nat) : (p1 q).1=P1PhaseFamily.choices q := by
  simp only [p1, flatRange_value, mapRange_value, P1PhaseFamily.choices]

theorem p1_sized (q : Nat) (hq : 0<q) : Sized q 3 23 (p1 q) := by
  apply flatRange_sized q 2 15 hq
  intro j _
  apply flatRange_sized q 1 7 hq
  intro e _
  exact mapRange_sized q hq _

def sources (q n : Nat) : Result (List (Nat×Nat)) :=
  flatRange (n+1) fun a => mapRange q fun phase => (a,phase)

theorem sources_value (q n : Nat) : (sources q n).1=P1SourceFamily.choices q n := by
  simp only [sources, flatRange_value, mapRange_value, P1SourceFamily.choices]

theorem sources_work (q n : Nat) (hq : 0<q) :
    (sources q n).2≤15*((n+1)*q) := by
  have hh := flatRange_work (n+1) (7*q) q (fun a => mapRange q (fun phase => (a,phase)))
    (fun a _ => by simpa only [Nat.pow_one] using (mapRange_sized q hq (fun p => (a,p))).2)
    (fun a _ => by simp only [mapRange_value, List.length_map, List.length_range]; exact Nat.le_refl _)
  have hn : n+1≤(n+1)*q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n+1) hq
  have hp : 1≤(n+1)*q := Nat.mul_pos (by omega) hq
  change (sources q n).2≤_ at hh
  simp only [Nat.mul_add] at hh
  have he : (n+1)*(7*q)=7*((n+1)*q) := by ac_rfl
  rw [he] at hh
  omega

def targets (q n : Nat) : Result (List (Nat×P1PhaseFamily.Three)) :=
  let phases := p1 q
  let out := flatRange (n+1) fun p =>
    CountedProjection.map (fun v => ((p,v),1)) phases.1
  (out.1,phases.2+out.2+1)

theorem targets_value (q n : Nat) : (targets q n).1=P1PhaseFamily.targets q n := by
  simp only [targets, flatRange_value, CountedProjection.map_value,
    p1_value, P1PhaseFamily.targets]

theorem targets_work (q n : Nat) (hq : 0<q) :
    (targets q n).2≤35*((n+1)*q^3) := by
  have hp := p1_sized q hq
  have hh := flatRange_work (n+1) (2*q^3+1) (q^3)
    (fun p => CountedProjection.map (fun v => ((p,v),1)) (p1 q).1)
    (fun p _ => by rw [CountedProjection.map_plain_steps, hp.1]; omega)
    (fun p _ => by rw [CountedProjection.map_value, List.length_map, hp.1]; exact Nat.le_refl _)
  have hw := hp.2
  have hq3 : 1≤q^3 := Nat.pow_pos hq
  have hn : n+1≤(n+1)*q^3 := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n+1) hq3
  have hqle : q^3≤(n+1)*q^3 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (q^3) (show 1≤n+1 by omega)
  have hpos : 1≤(n+1)*q^3 := Nat.mul_pos (by omega) hq3
  unfold targets
  dsimp only
  simp only [Nat.mul_add] at hh
  have he : (n+1)*(2*q^3)=2*((n+1)*q^3) := by ac_rfl
  rw [he] at hh
  omega

end REWB.PeriodicActual.Choices
