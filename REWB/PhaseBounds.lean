import REWB.P2PhaseFamily
import REWB.LiteralShape

/-! Size of the input formula at a fixed phase. Each regular factor
    contributes at most one disjunct per state of its DFA. The number
    of initial branches is independent of the period and text length.
    LiteralShape separately checks independence of projection branches
    under changes of numeric constants. -/
namespace REWB.FiniteOrbit
variable {S : Type}

theorem compress_size [DecidableEq S] (e : FiniteRelation.Enumeration S)
    (step : S→S) (q : S) (accept : S→Bool) (D : Descriptor)
    (hD : compress e step q accept=some D) :
    D.initialCounts.length+D.residues.length≤e.elems.length := by
  obtain ⟨i,j,hf,hij,hj,he⟩ := findCycle_spec e step q
  rw [compress,hf] at hD
  simp only [Option.map,Option.some.injEq] at hD
  subst D
  have h1 := List.length_filter_le (fun k=>accept (orbit step q k)) (List.range i)
  have h2 := List.length_filter_le (fun r=>accept (orbit step q (i+r))) (List.range (j-i))
  rw [List.length_range] at h1 h2
  change ((List.range i).filter _).length+((List.range (j-i)).filter _).length≤e.elems.length
  omega

end REWB.FiniteOrbit

namespace REWB.PhaseSolver
open REWB.AffineProjection
open REWB.Periodic
variable {α : Type}

theorem both_length (F G : Formula) : (both F G).length=F.length*G.length := by
  induction F with
  | nil => simp [both]
  | cons A As ih =>
    change ((G.map (fun B=>A++B))++both As G).length=(As.length+1)*G.length
    rw [List.length_append,List.length_map,ih,Nat.add_mul,Nat.one_mul]
    omega

theorem le_length (a b : Aff) : (le a b).length=1 := rfl
theorem eq_length (a b : Aff) : (eq a b).length=1 := rfl

theorem bound_length (a : Endpoint) (q n : Nat) : (a.bound q n).length≤1 := by
  unfold Endpoint.bound
  split
  · simp [both_length,le_length]
  · simp

theorem order_length (q n : Nat) (a b : Endpoint) : (orderFormula q n a b).length≤1 := by
  simp only [orderFormula,both_length,le_length,Nat.mul_one]
  exact Nat.le_trans (Nat.mul_le_mul (bound_length a q n) (bound_length b q n)) (by decide)

theorem descriptor_length (D : FiniteOrbit.Descriptor) (t : Aff) :
    (descriptorFormula D t).length≤D.initialCounts.length+D.residues.length := by
  unfold descriptorFormula
  simp only [List.length_append,List.length_map]
  have h := List.length_filter_le (fun k=>decide (k<D.threshold)) D.initialCounts
  omega

theorem regular_length (q n : Nat) (s : Nat→α) (d : DFA α) (a b : Endpoint) :
    (regularFormula q n s d a b).length≤d.stateCount := by
  unfold regularFormula
  rw [both_length]
  cases he : factorDescriptor d s a.phase q (tailLen q a b) with
  | none => simp
  | some D =>
    have hc : D.initialCounts.length+D.residues.length≤d.stateCount := by
      unfold factorDescriptor at he
      have hb := FiniteOrbit.compress_size _ _ _ _ D he
      simpa [FiniteRelation.finEnum] using hb
    change (orderFormula q n a b).length*(descriptorFormula D (countExpr a b)).length≤d.stateCount
    exact Nat.le_trans (Nat.mul_le_mul (order_length q n a b)
      (Nat.le_trans (descriptor_length D _) hc)) (by simp)

theorem equalCore_length [DecidableEq α] (q : Nat) (s : Nat→α)
    (a b c d : Endpoint) : (equalityCore q s a b c d).length≤1 := by
  unfold equalityCore
  split
  · split
    · simp [eq_length]
    · split <;> simp [both_length,eq_length]
  · simp

theorem equal_length [DecidableEq α] (q n : Nat) (s : Nat→α)
    (a b c d : Endpoint) : (equalFormula q n s a b c d).length≤1 := by
  simp only [equalFormula,both_length]
  exact Nat.le_trans (Nat.mul_le_mul
    (Nat.mul_le_mul (order_length q n a b) (order_length q n c d))
    (Nat.mul_le_mul (order_length q n a c) (equalCore_length q s a b c d))) (by decide)

def Constraint.weight : Constraint α→Nat
  | .regular d _ _ => d.stateCount
  | _ => 1

theorem constraint_length [DecidableEq α] (q n : Nat) (s : Nat→α) (c : Constraint α) :
    (c.compile q n s).length≤c.weight := by
  cases c with
  | bound a => exact bound_length a q n
  | order a b => exact order_length q n a b
  | regular d a b => exact regular_length q n s d a b
  | equal a b c d => exact equal_length q n s a b c d

def weight : List (Constraint α)→Nat
  | [] => 1
  | c::cs => c.weight*weight cs

theorem system_length [DecidableEq α] (q n : Nat) (s : Nat→α) (cs : List (Constraint α)) :
    (compileSystem q n s cs).length≤weight cs := by
  induction cs with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    rw [compileSystem,both_length,weight]
    exact Nat.mul_le_mul (constraint_length q n s c) ih

end REWB.PhaseSolver

namespace REWB.P2Periodic
open REWB.PhaseSolver
variable {α : Type}

theorem fixed_formula_bound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : Layout Nat) :
    (compileSystem q n s (constraints P q n pre post (endpoints ph))).length≤
      P.A.stateCount*(P.B.stateCount*(P.C.stateCount*(P.D.stateCount*
        (P.F.stateCount*(P.G.stateCount*P.H.stateCount))))) := by
  have h := system_length q n s (constraints P q n pre post (endpoints ph))
  simpa [weight,Constraint.weight,constraints,Periodic.contextual] using h

end REWB.P2Periodic
