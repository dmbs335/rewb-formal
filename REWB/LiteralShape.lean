import REWB.DescriptorFormula

/-! The Cooper projection's branching structure is independent of the
    numeric values of literal constants. Erasing literals preserves all
    variable indices, coefficient multipliers and divisibility moduli.
    This is an exact shape theorem, not yet a bit-operation bound. -/
namespace REWB.AffineProjection.LiteralShape
open REWB.AffineProjection

def aff : Aff→Aff
  | .lit _ => .lit 0
  | .var i => .var i
  | .add a b => .add (aff a) (aff b)
  | .scale c a => .scale c (aff a)

@[simp] theorem aff_idem (a : Aff) : aff (aff a)=aff a := by
  induction a <;> simp_all [aff]

@[simp] theorem aff_sub (a b : Aff) : aff (a.sub b)=(aff a).sub (aff b) := rfl

theorem split_aff (a : Aff) :
    (aff a).split=(a.split.1,aff a.split.2) := by
  induction a with
  | lit v => rfl
  | var i => cases i <;> rfl
  | add a b ha hb =>
    simp only [aff,Aff.split,ha,hb]
  | scale c a ha =>
    simp only [aff,Aff.split,ha]

def atom : Atom→Atom
  | .le a => .le (aff a)
  | .dvd m a => .dvd m (aff a)

def conj (C : Conj) : Conj := C.map atom
def formula (F : Formula) : Formula := F.map conj

@[simp] theorem conj_append (C D : Conj) : conj (C++D)=conj C++conj D := by
  simp [conj]

@[simp] theorem factor_atom (a : Atom) : (atom a).factor=a.factor := by
  cases a with
  | le a => simp [atom,Atom.factor,split_aff]
  | dvd m a => rfl

theorem multiplier_conj (C : Conj) : multiplier (conj C)=multiplier C := by
  induction C with
  | nil => rfl
  | cons a as ih =>
    change Nat.lcm (atom a).factor (multiplier (conj as))=Nat.lcm a.factor (multiplier as)
    rw [factor_atom,ih]

def guard (g : Guard) : Guard := ⟨g.modulus,g.coeff,aff g.rest⟩

def norm (N : Norm) : Norm :=
  ⟨N.lower.map aff,N.upper.map aff,conj N.free,N.guards.map guard⟩

theorem norm_merge (N M : Norm) : norm (N.merge M)=(norm N).merge (norm M) := by
  simp [norm,Norm.merge,List.map_append]

theorem norm_atom (D : Nat) (a : Atom) :
    norm (normalizeAtom D a)=normalizeAtom D (atom a) := by
  cases a with
  | le a =>
    simp only [normalizeAtom,atom,split_aff]
    by_cases h : a.split.1=0
    · simp [h,norm,conj,atom]
    · by_cases hp : 0<a.split.1 <;> simp [h,hp,norm,conj,aff,guard]
  | dvd m a =>
    simp [normalizeAtom,atom,split_aff,norm,conj,guard,aff]

theorem norm_rows (D : Nat) (C : Conj) :
    norm (normalizeRows D C)=normalizeRows D (conj C) := by
  induction C with
  | nil => rfl
  | cons a as ih =>
    change norm ((normalizeAtom D a).merge (normalizeRows D as)) =
      (normalizeAtom D (atom a)).merge (normalizeRows D (conj as))
    rw [norm_merge,norm_atom,ih]

theorem norm_normalize (C : Conj) :
    norm (normalize C)=normalize (conj C) := by
  unfold normalize
  rw [multiplier_conj,norm_merge,norm_rows]
  rfl

theorem commonPeriod_map (gs : List Guard) :
    commonPeriod (gs.map guard)=commonPeriod gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change Nat.lcm g.modulus (commonPeriod (gs.map guard))=Nat.lcm g.modulus (commonPeriod gs)
    rw [ih]

private theorem map_flat {X Y Z : Type} (xs : List X) (f : X→List Y) (g : Y→Z) :
    (xs.flatMap f).map g=xs.flatMap (fun x=>(f x).map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.map_append,ih]

theorem candidate_shape (N : Norm) (K : Nat) :
    (N.candidates K).map aff=((norm N).candidates K).map aff := by
  have h : ∀ xs : List Aff,
      (xs.flatMap (fun l=>(List.range K).map (fun r : Nat=>Aff.add l (.lit (r:Int))))).map aff =
      ((xs.map aff).flatMap (fun l=>(List.range K).map
        (fun r : Nat=>Aff.add l (.lit (r:Int))))).map aff := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a as ih =>
      simp only [List.flatMap_cons,List.map_cons,List.map_append,List.map_map,Function.comp_def,
        aff,aff_idem,ih]
  unfold Norm.candidates norm
  cases he : N.lower with
  | nil => rfl
  | cons a as =>
    simp only [he,List.map_cons,List.isEmpty_cons,Bool.false_eq_true,if_false]
    exact h (a::as)

theorem substitute_shape (N : Norm) (c : Aff) :
    conj (N.substitute c)=(norm N).substitute (aff c) := by
  unfold Norm.substitute
  have h : (N.lower.map aff).isEmpty=N.lower.isEmpty := by cases N.lower <;> rfl
  simp only [norm,h,conj_append,conj,List.map_map,Function.comp_def,
    atom,Guard.substitute,guard,aff,aff_sub]
  cases he : N.lower.isEmpty <;> simp [he,conj,List.map_append,List.map_map,
    Function.comp_def,atom,aff,aff_sub]

@[simp] theorem atom_idem (a : Atom) : atom (atom a)=atom a := by
  cases a <;> simp [atom,aff_idem]

@[simp] theorem guard_idem (g : Guard) : guard (guard g)=guard g := by
  cases g
  simp [guard,aff_idem]

theorem norm_idem (N : Norm) : norm (norm N)=norm N := by
  cases N
  simp [norm,conj,List.map_map,Function.comp_def,aff_idem,atom_idem,guard_idem]

theorem elimination_shape (N : Norm) (K : Nat) :
    formula (N.eliminate K)=formula ((norm N).eliminate K) := by
  unfold formula Norm.eliminate
  simp only [List.map_map,Function.comp_def,substitute_shape]
  rw [norm_idem]
  have he := congrArg (List.map (fun c=>(norm N).substitute c)) (candidate_shape N K)
  simpa only [List.map_map,Function.comp_def] using he

theorem eliminateConj_shape (C : Conj) :
    formula (eliminateConj C)=formula (eliminateConj (conj C)) := by
  unfold eliminateConj
  rw [← norm_normalize]
  change formula ((normalize C).eliminate (commonPeriod (normalize C).guards)) =
    formula ((norm (normalize C)).eliminate
      (commonPeriod ((normalize C).guards.map guard)))
  rw [commonPeriod_map]
  exact elimination_shape _ _

theorem eliminateFormula_shape (F : Formula) :
    formula (eliminateFormula F)=formula (eliminateFormula (formula F)) := by
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change formula (eliminateConj C++eliminateFormula Cs)=
      formula (eliminateConj (conj C)++eliminateFormula (formula Cs))
    simp only [formula,List.map_append]
    have h := eliminateConj_shape C
    change (eliminateConj C).map conj=(eliminateConj (conj C)).map conj at h
    change (eliminateFormula Cs).map conj=(eliminateFormula (formula Cs)).map conj at ih
    rw [h,ih]
    rfl

/-- All stages have exactly the same erased formula when the starting
    coefficient/modulus structure agrees. In particular branch counts
    cannot depend on the numeric values of RHS constants. -/
theorem project_shape (k : Nat) (F G : Formula) (h : formula F=formula G) :
    formula (project k F)=formula (project k G) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    change formula (eliminateFormula (project k F)) =
      formula (eliminateFormula (project k G))
    rw [eliminateFormula_shape (project k F),eliminateFormula_shape (project k G),ih]

theorem project_branches (k : Nat) (F G : Formula) (h : formula F=formula G) :
    (project k F).length=(project k G).length := by
  have he := congrArg List.length (project_shape k F G h)
  simpa only [formula,List.length_map] using he

end REWB.AffineProjection.LiteralShape
