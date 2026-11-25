import REWB.UniformPhaseBounds

/-! Numeric magnitude in the actual symbolic projection algorithm.
    Elimination preserves existing literal leaves and introduces only
    residues smaller than its shape-dependent common period. Multipliers
    are stored separately in affine syntax and are uniformly bounded by
    UniformProjection. Thus literal growth is bounded independently of
    the values of numeric endpoint constants. -/
namespace REWB.ProjectionMagnitude
open REWB.AffineProjection REWB.UniformProjection REWB.PhaseSolver

def AffBound (B : Nat) : Aff→Prop
  | .lit z => z.natAbs≤B
  | .var _ => True
  | .add a b => AffBound B a ∧ AffBound B b
  | .scale _ a => AffBound B a

def AtomBound (B : Nat) (a : Atom) : Prop := AffBound B (payload a)
def ConjBound (B : Nat) (C : Conj) : Prop := ∀ a,a∈C→AtomBound B a
def FormulaBound (B : Nat) (F : Formula) : Prop := ∀ C,C∈F→ConjBound B C

def NormBound (B : Nat) (N : Norm) : Prop :=
  (∀ a,a∈N.lower→AffBound B a) ∧
  (∀ a,a∈N.upper→AffBound B a) ∧ ConjBound B N.free ∧
  (∀ g,g∈N.guards→AffBound B g.rest)

theorem aff_mono (B C : Nat) (hBC : B≤C) (a : Aff) (h : AffBound B a) : AffBound C a := by
  induction a with
  | lit z => exact Nat.le_trans h hBC
  | var i => trivial
  | add a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | scale k a ha => exact ha h

theorem atom_mono (B C : Nat) (hBC : B≤C) (a : Atom) (h : AtomBound B a) : AtomBound C a :=
  aff_mono B C hBC (payload a) h

theorem conj_mono (B C : Nat) (hBC : B≤C) (F : Conj) (h : ConjBound B F) : ConjBound C F :=
  fun a ha=>atom_mono B C hBC a (h a ha)

theorem formula_mono (B C : Nat) (hBC : B≤C) (F : Formula) (h : FormulaBound B F) :
    FormulaBound C F := fun a ha=>conj_mono B C hBC a (h a ha)

theorem norm_mono (B C : Nat) (hBC : B≤C) (N : Norm) (h : NormBound B N) : NormBound C N :=
  ⟨fun a ha=>aff_mono B C hBC a (h.1 a ha),
    fun a ha=>aff_mono B C hBC a (h.2.1 a ha),conj_mono B C hBC _ h.2.2.1,
    fun g hg=>aff_mono B C hBC g.rest (h.2.2.2 g hg)⟩

theorem aff_split (B : Nat) (a : Aff) (h : AffBound B a) : AffBound B a.split.2 := by
  induction a with
  | lit z => exact h
  | var i =>
    cases i with
    | zero => exact Nat.zero_le _
    | succ i => trivial
  | add a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | scale c a ha => exact ha h

theorem conj_append (B : Nat) (C D : Conj) :
    ConjBound B (C++D) ↔ ConjBound B C ∧ ConjBound B D := by
  constructor
  · intro h
    exact ⟨fun a ha=>h a (List.mem_append.mpr (Or.inl ha)),
      fun a ha=>h a (List.mem_append.mpr (Or.inr ha))⟩
  · rintro ⟨hC,hD⟩ a ha
    exact (List.mem_append.mp ha).elim (hC a) (hD a)

theorem norm_merge (B : Nat) (N M : Norm) (hN : NormBound B N) (hM : NormBound B M) :
    NormBound B (N.merge M) := by
  refine ⟨?_,?_,(conj_append B _ _).mpr ⟨hN.2.2.1,hM.2.2.1⟩,?_⟩
  · intro a ha
    exact (List.mem_append.mp ha).elim (hN.1 a) (hM.1 a)
  · intro a ha
    exact (List.mem_append.mp ha).elim (hN.2.1 a) (hM.2.1 a)
  · intro g hg
    exact (List.mem_append.mp hg).elim (hN.2.2.2 g) (hM.2.2.2 g)

theorem normalizeAtom_bound (B D : Nat) (a : Atom) (h : AtomBound B a) :
    NormBound B (normalizeAtom D a) := by
  cases a with
  | le t =>
    have hr := aff_split B t h
    unfold normalizeAtom
    dsimp only
    split
    · simpa [NormBound,ConjBound,AtomBound,payload] using hr
    · split <;> simpa [NormBound,ConjBound,AtomBound,payload,AffBound] using hr
  | dvd m t =>
    have hr := aff_split B t h
    simpa [normalizeAtom,NormBound,ConjBound,AtomBound,payload,AffBound] using hr

theorem normalizeRows_bound (B D : Nat) (C : Conj) (h : ConjBound B C) :
    NormBound B (normalizeRows D C) := by
  induction C with
  | nil => simp [normalizeRows,Norm.empty,NormBound,ConjBound]
  | cons a as ih =>
    exact norm_merge B _ _ (normalizeAtom_bound B D a (h a (by simp)))
      (ih (fun b hb=>h b (by simp [hb])))

theorem normalize_bound (B : Nat) (C : Conj) (h : ConjBound B C) : NormBound B (normalize C) := by
  apply norm_merge B _ _ (normalizeRows_bound B _ C h)
  simp [integrality,NormBound,ConjBound,AffBound]

theorem candidates_bound (B K : Nat) (N : Norm) (h : NormBound B N) (a : Aff)
    (ha : a∈N.candidates K) : AffBound (max B K) a := by
  unfold Norm.candidates at ha
  split at ha
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
    have hr' := List.mem_range.mp hr
    change r≤max B K
    omega
  · obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
    have hr' := List.mem_range.mp hr
    refine ⟨aff_mono B (max B K) (Nat.le_max_left _ _) b (h.1 b hb),?_⟩
    change r≤max B K
    omega

theorem substitute_bound (B : Nat) (N : Norm) (a : Aff)
    (hN : NormBound B N) (ha : AffBound B a) : ConjBound B (N.substitute a) := by
  unfold Norm.substitute
  apply (conj_append B _ _).mpr
  refine ⟨(conj_append B _ _).mpr ⟨hN.2.2.1,?_⟩,?_⟩
  · split
    · intro b hb
      simp at hb
    · apply (conj_append B _ _).mpr
      constructor
      · intro b hb
        obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hb
        exact ⟨hN.1 l hl,ha⟩
      · intro b hb
        obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hb
        exact ⟨ha,hN.2.1 u hu⟩
  · intro b hb
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hb
    exact ⟨ha,hN.2.2.2 g hg⟩

theorem eliminateConj_bound (B : Nat) (C : Conj) (h : ConjBound B C) :
    FormulaBound (max B (commonPeriod (normalize C).guards)) (eliminateConj C) := by
  intro D hD
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hD
  exact substitute_bound _ _ a
    (norm_mono B _ (Nat.le_max_left _ _) _ (normalize_bound B C h))
    (candidates_bound B _ (normalize C) (normalize_bound B C h) a ha)

def residueBound : Formula→Nat
  | [] => 0
  | C::Cs => max (commonPeriod (normalize C).guards) (residueBound Cs)

theorem residueBound_member (F : Formula) (C : Conj) (h : C∈F) :
    commonPeriod (normalize C).guards≤residueBound F := by
  induction F with
  | nil => simp at h
  | cons D Ds ih =>
    rcases List.mem_cons.mp h with he|hm
    · subst C
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)

theorem eliminateFormula_bound (B : Nat) (F : Formula) (h : FormulaBound B F) :
    FormulaBound (max B (residueBound F)) (eliminateFormula F) := by
  intro D hD
  obtain ⟨C,hC,hD⟩ := List.mem_flatMap.mp hD
  exact conj_mono _ _ (by have hh := residueBound_member F C hC; omega) D
    (eliminateConj_bound B C (h C hC) D hD)

theorem commonPeriod_erase (C : Conj) :
    commonPeriod (normalize (LiteralShape.conj C)).guards=commonPeriod (normalize C).guards := by
  rw [← LiteralShape.norm_normalize]
  change commonPeriod ((normalize C).guards.map LiteralShape.guard)=_
  exact LiteralShape.commonPeriod_map _

theorem residueBound_erase (F : Formula) : residueBound (LiteralShape.formula F)=residueBound F := by
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change max (commonPeriod (normalize (LiteralShape.conj C)).guards)
      (residueBound (LiteralShape.formula Cs))=residueBound (C::Cs)
    rw [commonPeriod_erase,ih]
    rfl

def extra : Nat→Formula→Nat
  | 0,_ => 0
  | k+1,F => max (extra k F) (residueBound (project k F))

theorem extra_mono (k K : Nat) (F : Formula) (h : k≤K) : extra k F≤extra K F := by
  induction K with
  | zero =>
    have he : k=0 := by omega
    subst k
    exact Nat.le_refl _
  | succ K ih =>
    by_cases he : k=K+1
    · subst k
      exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (Nat.le_max_left _ _)

theorem projection_bound (k : Nat) (B : Nat) (F : Formula) (h : FormulaBound B F) :
    FormulaBound (max B (extra k F)) (project k F) := by
  induction k with
  | zero => simpa only [extra,project,Nat.max_zero] using h
  | succ k ih =>
    have hh := eliminateFormula_bound _ (project k F) ih
    simpa only [project,extra,Nat.max_assoc] using hh

theorem extra_shape (k : Nat) (F G : Formula)
    (h : LiteralShape.formula F=LiteralShape.formula G) : extra k F=extra k G := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have he := congrArg residueBound (LiteralShape.project_shape k F G h)
    rw [residueBound_erase,residueBound_erase] at he
    change max (extra k F) (residueBound (project k F))=
      max (extra k G) (residueBound (project k G))
    rw [ih,he]

def familyExtra (k : Nat) : Family→Nat
  | [] => 0
  | F::fs => max (extra k F) (familyExtra k fs)

theorem extra_le_family (k : Nat) (fs : Family) (F : Formula) (h : F∈fs) :
    extra k F≤familyExtra k fs := by
  induction fs with
  | nil => simp at h
  | cons G gs ih =>
    rcases List.mem_cons.mp h with he|hm
    · subst F
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)

/-- Literal leaves can only come from the input, zeroes introduced by
    splitting, or bounded residues. This cap does not multiply by n. -/
theorem uniform_projection_bound (k B : Nat) (F : Formula) (fs : Family)
    (hf : Covered F fs) (hB : FormulaBound B F) :
    FormulaBound (max B (familyExtra k fs)) (project k F) := by
  have he := extra_shape k F (LiteralShape.formula F) (by
    simp only [LiteralShape.formula,LiteralShape.conj,List.map_map,Function.comp_def,
      LiteralShape.atom_idem]
    rfl)
  have hcap : extra k F≤familyExtra k fs := by
    rw [he]
    exact extra_le_family k fs _ hf
  exact formula_mono _ _ (by omega) _ (projection_bound k B F hB)

theorem familyExtra_mono (k K : Nat) (fs : Family) (hk : k≤K) :
    familyExtra k fs≤familyExtra K fs := by
  induction fs with
  | nil => exact Nat.le_refl _
  | cons F fs ih =>
    have hh := extra_mono k K F hk
    change max (extra k F) (familyExtra k fs)≤max (extra K F) (familyExtra K fs)
    omega

theorem uniform_stage_literals (k K B : Nat) (F : Formula) (fs : Family)
    (hf : Covered F fs) (hB : FormulaBound B F) (hk : k≤K) :
    FormulaBound (max B (familyExtra K fs)) (project k F) := by
  have hm := familyExtra_mono k K fs hk
  exact formula_mono _ _ (by omega) _ (uniform_projection_bound k B F fs hf hB)

/-- Evaluation at zero is the affine constant term. Since the erased
    structural weight also bounds coefficient growth, its magnitude is
    at most that weight times the literal cap. -/
theorem eval_nil_bound (B : Nat) (a : Aff) (h : AffBound B a) :
    (a.eval []).natAbs≤affMeasure a*B := by
  induction a with
  | lit z => simpa only [Aff.eval,affMeasure,Nat.one_mul] using h
  | var i =>
    simp [Aff.eval,affMeasure]
  | add a b ha hb =>
    have hh := Int.natAbs_add_le (a.eval []) (b.eval [])
    have hab := Nat.add_le_add (ha h.1) (hb h.2)
    change (a.eval []+b.eval []).natAbs≤(affMeasure a+affMeasure b+1)*B
    rw [Nat.add_mul,Nat.one_mul, Nat.add_mul]
    omega
  | scale c a ha =>
    change (c*a.eval []).natAbs≤((c.natAbs+1)*(affMeasure a+1))*B
    rw [Int.natAbs_mul]
    have hh := Nat.mul_le_mul_left c.natAbs (ha h)
    have hm : c.natAbs*affMeasure a≤(c.natAbs+1)*(affMeasure a+1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hm' := Nat.mul_le_mul_right B hm
    rw [Nat.mul_assoc] at hm'
    exact Nat.le_trans hh hm'

theorem formula_eval_bound (B : Nat) (F : Formula) (h : FormulaBound B F)
    (C : Conj) (a : Atom) (hC : C∈F) (ha : a∈C) :
    ((payload a).eval []).natAbs≤measure F*B := by
  have hm := Nat.le_trans (payload_measure a)
    (Nat.le_trans (member_atom_measure C a ha) (member_conj_measure F C hC))
  exact Nat.le_trans (eval_nil_bound B _ (h C hC a ha)) (Nat.mul_le_mul_right B hm)

theorem projected_constant_bound (k B : Nat) (F : Formula) (fs : Family)
    (hf : Covered F fs) (hB : FormulaBound B F) (C : Conj) (a : Atom)
    (hC : C∈project k F) (ha : a∈C) :
    ((payload a).eval []).natAbs≤budget k fs*max B (familyExtra k fs) :=
  Nat.le_trans (formula_eval_bound _ _ (uniform_projection_bound k B F fs hf hB) C a hC ha)
    (Nat.mul_le_mul_right _ (projection_budget k F fs hf))

theorem projected_stage_constant_bound (k K B : Nat) (F : Formula) (fs : Family)
    (hf : Covered F fs) (hB : FormulaBound B F) (hk : k≤K)
    (C : Conj) (a : Atom) (hC : C∈project k F) (ha : a∈C) :
    ((payload a).eval []).natAbs≤stageBudget K fs*max B (familyExtra K fs) :=
  Nat.le_trans (formula_eval_bound _ _ (uniform_stage_literals k K B F fs hf hB hk) C a hC ha)
    (Nat.mul_le_mul_right _ (projection_stage_budget k K F fs hf hk))

end REWB.ProjectionMagnitude
