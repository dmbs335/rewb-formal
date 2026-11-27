import REWB.ProjectionMagnitude

/-! Linear numeric magnitudes and logarithmic bit widths for the actual
    fixed-phase P2 compiler and its eight projection stages. Numeric
    literals from text coordinates are at most n; finite-state orbit
    descriptors introduce constants bounded by DFA state counts. -/
namespace REWB.ProjectionMagnitude
open REWB.AffineProjection REWB.UniformProjection REWB.UniformPhaseBounds REWB.PhaseSolver
open REWB.Periodic
variable {α : Type}

theorem empty_bound (B : Nat) : FormulaBound B [] := by
  intro C hC
  simp at hC

theorem both_bound (B : Nat) (F G : Formula) (hF : FormulaBound B F) (hG : FormulaBound B G) :
    FormulaBound B (both F G) := by
  intro C hC
  obtain ⟨D,hD,hC⟩ := List.mem_flatMap.mp hC
  obtain ⟨E,hE,rfl⟩ := List.mem_map.mp hC
  exact (conj_append B D E).mpr ⟨hF D hD,hG E hE⟩

theorem le_bound (B : Nat) (a b : Aff) (ha : AffBound B a) (hb : AffBound B b) :
    FormulaBound B (le a b) := by
  simpa [FormulaBound,ConjBound,le,unit,AtomBound,payload,Aff.sub,AffBound] using And.intro ha hb

theorem eq_bound (B : Nat) (a b : Aff) (ha : AffBound B a) (hb : AffBound B b) :
    FormulaBound B (eq a b) := both_bound B _ _ (le_bound B a b ha hb) (le_bound B b a hb ha)

theorem lit_nat_bound (B x : Nat) (hx : x≤B) : AffBound B (.lit (x:Int)) := hx

theorem lit_zero_bound (B : Nat) : AffBound B (.lit 0) := Nat.zero_le _

theorem endpoint_bound (B q n : Nat) (a : Endpoint) (hN : n≤B) (ha : AffBound B a.1) :
    FormulaBound B (a.bound q n) := by
  unfold Endpoint.bound
  split
  · exact both_bound B _ _ (le_bound B _ _ (lit_zero_bound B) ha)
      (le_bound B _ _ ha (lit_nat_bound B _ (Nat.le_trans (Nat.div_le_self _ _)
        (Nat.le_trans (Nat.sub_le _ _) hN))))
  · exact empty_bound B

theorem carry_le_one (a b : Endpoint) : carry a b≤1 := by
  unfold carry phaseCoord borrow
  split <;> omega

theorem count_bound (B : Nat) (a b : Endpoint) (hB : 1≤B)
    (ha : AffBound B a.1) (hb : AffBound B b.1) : AffBound B (countExpr a b) :=
  ⟨⟨hb,ha⟩,lit_nat_bound B _ (Nat.le_trans (carry_le_one a b) hB)⟩

theorem order_bound (B q n : Nat) (a b : Endpoint) (hN : n≤B) (hB : 1≤B)
    (ha : AffBound B a.1) (hb : AffBound B b.1) : FormulaBound B (orderFormula q n a b) :=
  both_bound B _ _
    (both_bound B _ _ (endpoint_bound B q n a hN ha) (endpoint_bound B q n b hN hb))
    (le_bound B _ _ (lit_zero_bound B) (count_bound B a b hB ha hb))

theorem exactCount_bound (B : Nat) (t : Aff) (v : Nat) (ht : AffBound B t) (hv : v≤B) :
    ConjBound B (exactCount t v) := by
  simpa [ConjBound,exactCount,AtomBound,payload,Aff.sub,AffBound] using
    And.intro (And.intro ht hv) (And.intro hv ht)

theorem progression_bound (B : Nat) (t : Aff) (v m : Nat) (ht : AffBound B t) (hv : v≤B) :
    ConjBound B (progression t v m) := by
  simpa [ConjBound,progression,AtomBound,payload,Aff.sub,AffBound] using
    And.intro (And.intro hv ht) (And.intro ht hv)

theorem descriptor_bound (B : Nat) (D : FiniteOrbit.Descriptor) (t : Aff)
    (ht : AffBound B t) (hD : D.threshold+D.period≤B)
    (hr : ∀ r,r∈D.residues→r<D.period) : FormulaBound B (descriptorFormula D t) := by
  intro C hC
  rcases List.mem_append.mp hC with h|h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
    have hv' := of_decide_eq_true (List.mem_filter.mp hv).2
    exact exactCount_bound B t v ht (by omega)
  · obtain ⟨r,hm,rfl⟩ := List.mem_map.mp h
    have hh := hr r hm
    exact progression_bound B t (D.threshold+r) D.period ht (by omega)

theorem regular_bound (B q n : Nat) (s : Nat→α) (d : DFA α) (a b : Endpoint)
    (hN : n≤B) (hB : 1≤B) (hd : d.stateCount≤B)
    (ha : AffBound B a.1) (hb : AffBound B b.1) :
    FormulaBound B (regularFormula q n s d a b) := by
  obtain ⟨D,hD,_,hsize,hr,_⟩ := FiniteOrbit.compress_spec (FiniteRelation.finEnum d.stateCount)
    (fun v=>d.run v (segment s a.phase q)) d.initial
    (fun v=>d.final (d.run v (segment s a.phase (tailLen q a b))))
  change factorDescriptor d s a.phase q (tailLen q a b)=some D at hD
  have hs : D.threshold+D.period≤d.stateCount := by
    simpa only [FiniteRelation.finEnum,List.length_ofFn] using hsize
  rw [regularFormula,hD]
  exact both_bound B _ _ (order_bound B q n a b hN hB ha hb)
    (descriptor_bound B D (countExpr a b) (count_bound B a b hB ha hb) (by omega) hr)

theorem equalityCore_bound [DecidableEq α] (B q : Nat) (s : Nat→α) (a b c d : Endpoint)
    (hB : 1≤B) (ha : AffBound B a.1) (hb : AffBound B b.1)
    (hc : AffBound B c.1) (hd : AffBound B d.1) :
    FormulaBound B (equalityCore q s a b c d) := by
  have hab := count_bound B a b hB ha hb
  have hcd := count_bound B c d hB hc hd
  unfold equalityCore
  split
  · split
    · exact eq_bound B _ _ hab hcd
    · split
      · exact both_bound B _ _ (eq_bound B _ _ hab (lit_zero_bound B))
          (eq_bound B _ _ hcd (lit_zero_bound B))
      · exact empty_bound B
  · exact empty_bound B

theorem equal_bound [DecidableEq α] (B q n : Nat) (s : Nat→α) (a b c d : Endpoint)
    (hN : n≤B) (hB : 1≤B) (ha : AffBound B a.1) (hb : AffBound B b.1)
    (hc : AffBound B c.1) (hd : AffBound B d.1) :
    FormulaBound B (equalFormula q n s a b c d) :=
  both_bound B _ _
    (both_bound B _ _ (order_bound B q n a b hN hB ha hb) (order_bound B q n c d hN hB hc hd))
    (both_bound B _ _ (order_bound B q n a c hN hB ha hc)
      (equalityCore_bound B q s a b c d hB ha hb hc hd))

def ConstraintBound (B : Nat) : Constraint α→Prop
  | .bound a => AffBound B a.1
  | .order a b => AffBound B a.1 ∧ AffBound B b.1
  | .regular d a b => d.stateCount≤B ∧ AffBound B a.1 ∧ AffBound B b.1
  | .equal a b c d => AffBound B a.1 ∧ AffBound B b.1 ∧ AffBound B c.1 ∧ AffBound B d.1

theorem constraint_bound [DecidableEq α] (B q n : Nat) (s : Nat→α) (c : Constraint α)
    (hN : n≤B) (hB : 1≤B) (h : ConstraintBound B c) : FormulaBound B (c.compile q n s) := by
  cases c with
  | bound a => exact endpoint_bound B q n a hN h
  | order a b => exact order_bound B q n a b hN hB h.1 h.2
  | regular d a b => exact regular_bound B q n s d a b hN hB h.1 h.2.1 h.2.2
  | equal a b c d => exact equal_bound B q n s a b c d hN hB h.1 h.2.1 h.2.2.1 h.2.2.2

theorem system_bound [DecidableEq α] (B q n : Nat) (s : Nat→α) (cs : List (Constraint α))
    (hN : n≤B) (hB : 1≤B) (h : ∀ c,c∈cs→ConstraintBound B c) :
    FormulaBound B (compileSystem q n s cs) := by
  induction cs with
  | nil => simp [compileSystem,FormulaBound,ConjBound]
  | cons c cs ih =>
    exact both_bound B _ _ (constraint_bound B q n s c hN hB (h c (by simp)))
      (ih (fun d hd=>h d (by simp [hd])))

def states (P : SevenDFA α) : Nat :=
  P.A.stateCount+P.B.stateCount+P.C.stateCount+P.D.stateCount+
    P.F.stateCount+P.G.stateCount+P.H.stateCount

def inputCap (P : SevenDFA α) (n : Nat) : Nat := n+states P+1

theorem p2_input_bound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    FormulaBound (inputCap P n) (compileSystem q n s
      (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph))) := by
  apply system_bound (inputCap P n) q n s _ (by unfold inputCap; omega) (by unfold inputCap; omega)
  intro c hc
  simp only [P2Periodic.constraints,List.mem_cons,List.mem_nil_iff] at hc
  rcases hc with h|h|h|h|h|h|h|h|h|h
  all_goals first
    | contradiction
    | (subst c
       simp only [ConstraintBound,P2Periodic.endpoints,P2Periodic.zeroEndpoint,
         P2Periodic.endEndpoint,contextual,AffBound,Int.natAbs,true_and,and_true] <;>
       (have hdiv := Nat.div_le_self n q
        unfold inputCap states
        omega))

def p2LiteralExtra (P : SevenDFA α) : Nat := familyExtra 8 (p2Family P)

theorem p2_projected_literals [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    FormulaBound (max (inputCap P n) (p2LiteralExtra P))
      (project 8 (compileSystem q n s
        (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph)))) :=
  uniform_projection_bound 8 _ _ _ (p2_covered P s q n pre post ph)
    (p2_input_bound P s q n pre post ph)

def p2LinearConstant (P : SevenDFA α) : Nat :=
  p2Budget P*(states P+p2LiteralExtra P+1)

theorem cap_linear (n S E : Nat) : max (n+S+1) E≤(S+E+1)*(n+2) := by
  have h := Nat.mul_le_mul_left (S+E+1) (show 1≤n+2 by omega)
  rw [Nat.mul_one] at h
  have hn : n≤(S+E+1)*n := by
    have hh := Nat.mul_le_mul_right n (show 1≤S+E+1 by omega)
    simpa only [Nat.one_mul] using hh
  rw [Nat.mul_add]
  omega

/-- Every evaluated affine constant term in the final P2 projection is
    at most a pattern-only constant times n+2. This controls actual
    integer operands, rather than only the count of symbolic atoms. -/
theorem p2_constant_linear [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat)
    (C : Conj) (a : Atom)
    (hC : C∈project 8 (compileSystem q n s
      (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph)))) (ha : a∈C) :
    ((payload a).eval []).natAbs≤p2LinearConstant P*(n+2) := by
  have hh := projected_constant_bound 8 (inputCap P n) _ _
    (p2_covered P s q n pre post ph) (p2_input_bound P s q n pre post ph) C a hC ha
  have hc := Nat.mul_le_mul_left (p2Budget P) (cap_linear n (states P) (p2LiteralExtra P))
  change ((payload a).eval []).natAbs≤p2Budget P*max (inputCap P n) (p2LiteralExtra P) at hh
  change p2Budget P*max (inputCap P n) (p2LiteralExtra P)≤
    p2Budget P*((states P+p2LiteralExtra P+1)*(n+2)) at hc
  simpa only [p2LinearConstant,Nat.mul_assoc] using Nat.le_trans hh hc

def bits (z : Int) : Nat := z.natAbs.log2+1

theorem linear_bits (z : Int) (C n : Nat) (h : z.natAbs≤C*(n+2)) :
    bits z≤C.log2+(n+2).log2+2 := by
  have hp := Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_log2_self (n:=C))
    (Nat.lt_log2_self (n:=n+2))
  rw [← Nat.pow_add] at hp
  have hz : z.natAbs<2^(C.log2+1+((n+2).log2+1)) := Nat.lt_of_le_of_lt h hp
  by_cases he : z.natAbs=0
  · simp only [bits,he,Nat.log2_zero]
    omega
  · have hl := (Nat.log2_lt he).mpr hz
    unfold bits
    omega

/-- The bit width has one logarithm of text length and a fixed additive
    pattern constant. Sign representation can add one further bit. -/
theorem p2_constant_bits [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat)
    (C : Conj) (a : Atom)
    (hC : C∈project 8 (compileSystem q n s
      (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph)))) (ha : a∈C) :
    bits ((payload a).eval [])≤(p2LinearConstant P).log2+(n+2).log2+2 :=
  linear_bits _ _ n (p2_constant_linear P s q n pre post ph C a hC ha)

def p2AllStagesLinearConstant (P : SevenDFA α) : Nat :=
  p2AllStagesBudget P*(states P+p2LiteralExtra P+1)

theorem p2_stage_constant_linear [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat)
    (k : Nat) (hk : k≤8) (C : Conj) (a : Atom)
    (hC : C∈project k (compileSystem q n s
      (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph)))) (ha : a∈C) :
    ((payload a).eval []).natAbs≤p2AllStagesLinearConstant P*(n+2) := by
  have hh := projected_stage_constant_bound k 8 (inputCap P n) _ _
    (p2_covered P s q n pre post ph) (p2_input_bound P s q n pre post ph) hk C a hC ha
  have hc := Nat.mul_le_mul_left (p2AllStagesBudget P) (cap_linear n (states P) (p2LiteralExtra P))
  change ((payload a).eval []).natAbs≤p2AllStagesBudget P*max (inputCap P n) (p2LiteralExtra P) at hh
  change p2AllStagesBudget P*max (inputCap P n) (p2LiteralExtra P)≤
    p2AllStagesBudget P*((states P+p2LiteralExtra P+1)*(n+2)) at hc
  simpa only [p2AllStagesLinearConstant,Nat.mul_assoc] using Nat.le_trans hh hc

theorem p2_all_stage_bits [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat)
    (k : Nat) (hk : k≤8) (C : Conj) (a : Atom)
    (hC : C∈project k (compileSystem q n s
      (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph)))) (ha : a∈C) :
    bits ((payload a).eval [])≤(p2AllStagesLinearConstant P).log2+(n+2).log2+2 :=
  linear_bits _ _ n (p2_stage_constant_linear P s q n pre post ph k hk C a hC ha)

end REWB.ProjectionMagnitude
