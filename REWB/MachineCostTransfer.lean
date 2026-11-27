import REWB.Specifications
import REWB.MachineWordBounds

/-! Arithmetic closure needed to transfer an existing operation-ledger
bound to an independently established machine-step bound.

The simulation inequality in `of_simulation_bound` is an explicit proof
premise. This module does not define a matcher machine or discharge that
premise. In particular, a bound on a returned counter is not silently
identified with a bound on machine execution. -/
namespace REWB.MachineCostTransfer

abbrev height := MachineWordBounds.height

theorem of_le {small large : Nat→Nat} (hlarge : Spec.Target25Over13 large)
    (h : ∀n,small n≤large n) : Spec.Target25Over13 small := by
  obtain ⟨coefficient,degree,hcoefficient,hlarge⟩ := hlarge
  exact ⟨coefficient,degree,hcoefficient,
    fun n=>Nat.le_trans (Nat.pow_le_pow_left (h n) 13) (hlarge n)⟩

theorem constant (fixed : Nat) : Spec.Target25Over13 (fun _=>fixed) := by
  refine ⟨(fixed+1)^13,0,Nat.pow_pos (by omega),?_⟩
  intro n
  simp only [Nat.pow_zero,Nat.mul_one]
  have hn : 1≤(n+2)^25 := Nat.pow_pos (by omega)
  have hfixed := Nat.pow_le_pow_left (Nat.le_succ fixed) 13
  exact Nat.le_trans hfixed (by simpa using Nat.mul_le_mul_left ((fixed+1)^13) hn)

theorem linear_input : Spec.Target25Over13 (fun n=>n+1) := by
  refine ⟨1,0,by decide,?_⟩
  intro n
  simp only [Nat.one_mul,Nat.pow_zero,Nat.mul_one]
  exact Nat.le_trans (Nat.pow_le_pow_left (show n+1≤n+2 by omega) 13)
    (Nat.pow_le_pow_right (show 0<n+2 by omega) (by decide : 13≤25))

theorem scale {work : Nat→Nat} (hwork : Spec.Target25Over13 work) (factor : Nat) :
    Spec.Target25Over13 (fun n=>factor*work n) := by
  obtain ⟨coefficient,degree,hcoefficient,hwork⟩ := hwork
  refine ⟨(factor+1)^13*coefficient,degree,
    Nat.mul_pos (Nat.pow_pos (by omega)) hcoefficient,?_⟩
  intro n
  have hfactor := Nat.mul_le_mul_right (work n) (Nat.le_succ factor)
  calc
    (factor*work n)^13≤((factor+1)*work n)^13 := Nat.pow_le_pow_left hfactor 13
    _=(factor+1)^13*(work n)^13 := Nat.mul_pow _ _ _
    _≤(factor+1)^13*(coefficient*(n+2)^25*((n+2).log2+1)^degree) :=
      Nat.mul_le_mul_left _ (hwork n)
    _=((factor+1)^13*coefficient)*(n+2)^25*((n+2).log2+1)^degree := by
      simp only [Nat.mul_assoc]

theorem polylog {work : Nat→Nat} (hwork : Spec.Target25Over13 work) (overhead : Nat) :
    Spec.Target25Over13 (fun n=>work n*(height n)^overhead) := by
  obtain ⟨coefficient,degree,hcoefficient,hwork⟩ := hwork
  refine ⟨coefficient,degree+overhead*13,hcoefficient,?_⟩
  intro n
  change (work n*(height n)^overhead)^13≤
    coefficient*(n+2)^25*(height n)^(degree+overhead*13)
  calc
    (work n*(height n)^overhead)^13=(work n)^13*(height n)^(overhead*13) := by
      rw [Nat.mul_pow,←Nat.pow_mul]
    _≤(coefficient*(n+2)^25*(height n)^degree)*(height n)^(overhead*13) :=
      Nat.mul_le_mul_right _ (hwork n)
    _=coefficient*(n+2)^25*(height n)^(degree+overhead*13) := by
      rw [Nat.pow_add,Nat.mul_assoc]

theorem maximum {first second : Nat→Nat}
    (hfirst : Spec.Target25Over13 first) (hsecond : Spec.Target25Over13 second) :
    Spec.Target25Over13 (fun n=>max (first n) (second n)) := by
  obtain ⟨a,d,ha,hfirst⟩ := hfirst
  obtain ⟨b,e,hb,hsecond⟩ := hsecond
  refine ⟨a+b,d+e,by omega,?_⟩
  intro n
  change (max (first n) (second n))^13≤(a+b)*(n+2)^25*(height n)^(d+e)
  have hheight : 0<height n := MachineWordBounds.height_positive n
  have hleft : (first n)^13≤(a+b)*(n+2)^25*(height n)^(d+e) := by
    apply Nat.le_trans (hfirst n)
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_right ((n+2)^25) (show a≤a+b by omega))
      (Nat.pow_le_pow_right hheight (show d≤d+e by omega))
  have hright : (second n)^13≤(a+b)*(n+2)^25*(height n)^(d+e) := by
    apply Nat.le_trans (hsecond n)
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_right ((n+2)^25) (show b≤a+b by omega))
      (Nat.pow_le_pow_right hheight (show e≤d+e by omega))
  by_cases h : first n≤second n
  · rw [Nat.max_eq_right h]
    exact hright
  · rw [Nat.max_eq_left (show second n≤first n by omega)]
    exact hleft

theorem add {first second : Nat→Nat}
    (hfirst : Spec.Target25Over13 first) (hsecond : Spec.Target25Over13 second) :
    Spec.Target25Over13 (fun n=>first n+second n) := by
  apply of_le (scale (maximum hfirst hsecond) 2)
  intro n
  have ha := Nat.le_max_left (first n) (second n)
  have hb := Nat.le_max_right (first n) (second n)
  omega

theorem fixed_preprocessing {work : Nat→Nat} (hwork : Spec.Target25Over13 work)
    (preprocessing : Nat) : Spec.Target25Over13 (fun n=>preprocessing+work n) :=
  add (constant preprocessing) hwork

theorem affine {work : Nat→Nat} (hwork : Spec.Target25Over13 work)
    (preprocessing factor : Nat) :
    Spec.Target25Over13 (fun n=>preprocessing+factor*work n) :=
  fixed_preprocessing (scale hwork factor) preprocessing

theorem with_linear_input {work : Nat→Nat} (hwork : Spec.Target25Over13 work) :
    Spec.Target25Over13 (fun n=>work n+n+1) := by
  simpa only [Nat.add_assoc] using add hwork linear_input

theorem simulation_envelope {work : Nat→Nat} (hwork : Spec.Target25Over13 work)
    (preprocessing factor overhead : Nat) :
    Spec.Target25Over13
      (fun n=>preprocessing+factor*(work n+n+1)*(height n)^overhead) :=
  fixed_preprocessing (polylog (scale (with_linear_input hwork) factor) overhead) preprocessing

/-- The premise must be established from an independently defined
execution semantics; it is not discharged by this closure theorem. -/
theorem of_simulation_bound {work steps : Nat→Nat} (hwork : Spec.Target25Over13 work)
    (preprocessing factor overhead : Nat)
    (simulation : ∀n,steps n≤preprocessing+factor*(work n+n+1)*(height n)^overhead) :
    Spec.Target25Over13 steps :=
  of_le (simulation_envelope hwork preprocessing factor overhead) simulation

end REWB.MachineCostTransfer
