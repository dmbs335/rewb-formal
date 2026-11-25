import REWB.MaskedPeriodicAP
import REWB.MaskedClusterStage

/-! The arithmetic core of a one-jump cluster cell. Both finite orbits
    are discovered by the actual fixed-state compressor. Their exponents
    are k-lo and hi-k. No occurrence, text period, or capture-length loop
    is used to construct the formula. The common modulus is an actual
    pattern-only LCM and is independent of all text endpoints.
-/
namespace REWB.MaskedCluster
open REWB.MaskedPeriodic REWB.AffineProjection REWB.ExponentIntervals REWB.PhaseSolver
variable {m n : Nat}

def common : Nat→Nat
  | 0 => 1
  | k+1 => Nat.lcm (k+1) (common k)

theorem common_pos (s : Nat) : 0<common s := by
  induction s with
  | zero => exact Nat.zero_lt_one
  | succ s ih =>
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Nat.ne_of_gt (Nat.zero_lt_succ s)) (Nat.ne_of_gt ih))

theorem common_dvd (s p : Nat) (hp : 0<p) (hs : p≤s) : p∣common s := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases he : p=s+1
    · subst p
      exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_lcm_right _ _)

def modulus (m n : Nat) : Nat := common (max m n)

theorem modulus_pos (m n : Nat) : 0<modulus m n := common_pos _

structure Prepared (m n : Nat) where
  K : Nat
  exact : K=modulus m n

def prepare (m n : Nat) : Prepared m n := ⟨modulus m n,rfl⟩

def leftExpr (lo : Nat) : Aff := (Aff.var 0).sub (.lit lo)
def rightExpr (hi : Nat) : Aff := (Aff.lit hi).sub (.var 0)
def bounds (lo hi : Nat) : Formula := both (le (.lit lo) (.var 0)) (le (.var 0) (.lit hi))

def PairAccepts (before : OrbitData m) (after : OrbitData n) (lo hi k : Nat) : Prop :=
  lo≤k ∧ k≤hi ∧ before.test (k-lo)=true ∧ after.test (hi-k)=true

def pairFormula (before : OrbitData m) (after : OrbitData n) (lo hi : Nat) : Formula :=
  both (bounds lo hi) (both (before.formula (leftExpr lo)) (after.formula (rightExpr hi)))

theorem bounds_correct (lo hi k : Nat) :
    Satisfies (bounds lo hi) [(k:Int)] ↔ lo≤k ∧ k≤hi := by
  simp only [bounds,both_correct,le_correct,Aff.eval,List.getElem?_cons_zero,Option.getD_some]
  omega

theorem leftExpr_eval (lo k : Nat) (h : lo≤k) :
    (leftExpr lo).eval [(k:Int)]=((k-lo:Nat):Int) := by
  simp only [leftExpr,Aff.eval_sub,Aff.eval,List.getElem?_cons_zero,Option.getD_some]
  omega

theorem rightExpr_eval (hi k : Nat) (h : k≤hi) :
    (rightExpr hi).eval [(k:Int)]=((hi-k:Nat):Int) := by
  simp only [rightExpr,Aff.eval_sub,Aff.eval,List.getElem?_cons_zero,Option.getD_some]
  omega

theorem pairFormula_correct (before : OrbitData m) (after : OrbitData n) (lo hi k : Nat) :
    Satisfies (pairFormula before after lo hi) [(k:Int)] ↔ PairAccepts before after lo hi k := by
  simp only [pairFormula,both_correct,bounds_correct]
  constructor
  · rintro ⟨⟨hl,hh⟩,hb,ha⟩
    exact ⟨hl,hh,(before.formula_correct _ _ _ (leftExpr_eval lo k hl)).mp hb,
      (after.formula_correct _ _ _ (rightExpr_eval hi k hh)).mp ha⟩
  · rintro ⟨hl,hh,hb,ha⟩
    exact ⟨⟨hl,hh⟩,(before.formula_correct _ _ _ (leftExpr_eval lo k hl)).mpr hb,
      (after.formula_correct _ _ _ (rightExpr_eval hi k hh)).mpr ha⟩

theorem compatible_both (K : Nat) (F G : Formula) (hF : Compatible K F) (hG : Compatible K G) :
    Compatible K (both F G) := by
  intro C hC a ha
  obtain ⟨A,hA,hC⟩ := List.mem_flatMap.mp hC
  obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hC
  rcases List.mem_append.mp ha with h|h
  · exact hF A hA a h
  · exact hG B hB a h

theorem compatible_le (K : Nat) (a b : Aff) : Compatible K (le a b) := by
  intro C hC atom ha
  have hc : C=[.le (a.sub b)] := by simpa only [le,unit,List.mem_singleton] using hC
  subst C
  have he : atom=.le (a.sub b) := by simpa only [List.mem_singleton] using ha
  subst atom
  trivial

theorem descriptor_compatible (K : Nat) (D : FiniteOrbit.Descriptor) (t : Aff)
    (h : D.period∣K) : Compatible K (descriptorFormula D t) := by
  intro C hC atom ha
  rcases List.mem_append.mp hC with hc|hc
  · obtain ⟨k,_,rfl⟩ := List.mem_map.mp hc
    simp only [exactCount,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> trivial
  · obtain ⟨r,_,rfl⟩ := List.mem_map.mp hc
    simp only [progression,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl
    · trivial
    · exact h

theorem pairFormula_compatible_common (before : OrbitData m) (after : OrbitData n)
    (lo hi S : Nat) (hm : m≤S) (hn : n≤S) :
    Compatible (common S) (pairFormula before after lo hi) := by
  apply compatible_both
  · exact compatible_both _ _ _ (compatible_le _ _ _) (compatible_le _ _ _)
  · apply compatible_both
    · apply descriptor_compatible
      exact common_dvd _ _ before.descriptor_spec.1
        (Nat.le_trans (by have h:=before.descriptor_spec.2.1; omega) hm)
    · apply descriptor_compatible
      exact common_dvd _ _ after.descriptor_spec.1
        (Nat.le_trans (by have h:=after.descriptor_spec.2.1; omega) hn)

theorem pairFormula_compatible (before : OrbitData m) (after : OrbitData n) (lo hi : Nat) :
    Compatible (modulus m n) (pairFormula before after lo hi) :=
  pairFormula_compatible_common before after lo hi (max m n) (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem both_length (F G : Formula) : (both F G).length=F.length*G.length := by
  induction F with
  | nil => simp [both]
  | cons C F ih =>
    simp only [both,List.flatMap_cons,List.length_append,List.length_map,List.length_cons,
      Nat.add_mul,Nat.one_mul] at *
    omega

theorem orbitFormula_length (orbit : OrbitData m) (t : Aff) : (orbit.formula t).length≤m := by
  have hs:=orbit.descriptor_spec.2.2.1
  have hf:=List.length_filter_le (fun k=>decide (k<orbit.descriptor.threshold)) orbit.descriptor.initialCounts
  simp only [OrbitData.formula,descriptorFormula,List.length_append,List.length_map]
  omega

theorem pairFormula_length (before : OrbitData m) (after : OrbitData n) (lo hi : Nat) :
    (pairFormula before after lo hi).length≤m*n := by
  simp only [pairFormula,bounds,both_length,le,unit,List.length_singleton,Nat.one_mul]
  exact Nat.mul_le_mul (orbitFormula_length before _) (orbitFormula_length after _)

end REWB.MaskedCluster
