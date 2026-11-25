import REWB.MatrixTable
import REWB.DyadicIndex

/-! Finite-monoid summaries of all cuts of a word.

The two stored transformations always arise from the same cut.  The
strict-cut summary excludes the terminal boundary, making concatenation
an ordinary monoid operation even on arbitrary summaries.  Queries add
the terminal cut explicitly.  Every product materializes its finite
Boolean table; it does not retain a chain of deferred predicates.
-/
namespace REWB.MaskedCut
open REWB.FiniteRelation
open REWB.RangeProducts (Ops product)

variable {M : Type} [DecidableEq M]

structure Summary (e : Enumeration M) where
  total : M
  cuts : MatrixTable.Matrix e

variable {e : Enumeration M}

def relation (a : Summary e) : Rel M := MatrixTable.denote a.cuts

private theorem bool_ext (a b : Bool) (h : a=true ↔ b=true) : a=b := by
  cases a <;> cases b <;> simp_all

theorem ext (a b : Summary e) (ht : a.total=b.total)
    (hc : relation a=relation b) : a=b := by
  cases a with
  | mk av ac =>
    cases b with
    | mk bt bc =>
      have he : ac=bc := MatrixTable.matrix_ext _ _ hc
      cases ht
      cases he
      rfl

def one (o : Ops M) (e : Enumeration M) : Summary e :=
  ⟨o.one,MatrixTable.ofRel e (fun _ _=>false)⟩

def mul (o : Ops M) (e : Enumeration M) (a b : Summary e) : Summary e :=
  ⟨o.mul a.total b.total,MatrixTable.ofRel e (fun p s=>
    any e (fun t=>relation a p t && decide (o.mul t b.total=s)) ||
    any e (fun t=>relation b t s && decide (o.mul a.total t=p)))⟩

@[simp] theorem one_total (o : Ops M) (e : Enumeration M) :
    (one o e).total=o.one := rfl

@[simp] theorem one_relation (o : Ops M) (e : Enumeration M) :
    relation (one o e)=fun _ _=>false := MatrixTable.denote_ofRel _ _

@[simp] theorem mul_total (o : Ops M) (e : Enumeration M) (a b : Summary e) :
    (mul o e a b).total=o.mul a.total b.total := rfl

theorem mul_true (o : Ops M) (e : Enumeration M) (a b : Summary e) (p s : M) :
    relation (mul o e a b) p s=true ↔
      (∃ t,relation a p t=true ∧ o.mul t b.total=s) ∨
      (∃ t,relation b t s=true ∧ o.mul a.total t=p) := by
  simp only [relation,mul,MatrixTable.denote_ofRel,Bool.or_eq_true,
    any_true,Bool.and_eq_true,decide_eq_true_eq]

theorem one_mul (o : Ops M) (e : Enumeration M) (a : Summary e) :
    mul o e (one o e) a=a := by
  apply ext
  · exact o.one_mul _
  · funext p s
    apply bool_ext
    simp only [mul_true,one_relation,Bool.false_eq_true,false_and,exists_false,
      false_or,one_total,o.one_mul]
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht
    · intro h
      exact ⟨p,h,rfl⟩

theorem mul_one (o : Ops M) (e : Enumeration M) (a : Summary e) :
    mul o e a (one o e)=a := by
  apply ext
  · exact o.mul_one _
  · funext p s
    apply bool_ext
    simp only [mul_true,one_relation,Bool.false_eq_true,false_and,exists_false,
      or_false,one_total,o.mul_one]
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht
    · intro h
      exact ⟨s,h,rfl⟩

theorem mul_assoc (o : Ops M) (e : Enumeration M) (a b c : Summary e) :
    mul o e (mul o e a b) c=mul o e a (mul o e b c) := by
  apply ext
  · exact o.assoc _ _ _
  · funext p s
    apply bool_ext
    simp only [mul_true,mul_total]
    constructor
    · rintro (⟨t,ht,hs⟩|⟨t,ht,hp⟩)
      · rcases ht with ⟨u,hu,he⟩|⟨u,hu,he⟩
        · exact Or.inl ⟨u,hu,by rw [← o.assoc,he,hs]⟩
        · exact Or.inr ⟨u,Or.inl ⟨t,hu,hs⟩,he⟩
      · exact Or.inr ⟨o.mul b.total t,Or.inr ⟨t,ht,rfl⟩,by rw [← o.assoc,hp]⟩
    · rintro (⟨t,ht,hs⟩|⟨t,ht,hp⟩)
      · exact Or.inl ⟨o.mul t b.total,Or.inl ⟨t,ht,rfl⟩,by rw [o.assoc,hs]⟩
      · rcases ht with ⟨u,hu,he⟩|⟨u,hu,he⟩
        · exact Or.inl ⟨u,Or.inr ⟨t,hu,hp⟩,he⟩
        · exact Or.inr ⟨u,hu,by rw [o.assoc,he,hp]⟩

def ops (o : Ops M) (e : Enumeration M) : Ops (Summary e) :=
  ⟨one o e,mul o e,one_mul o e,mul_one o e,mul_assoc o e⟩

def atom (o : Ops M) (e : Enumeration M) (x : M) : Summary e :=
  ⟨x,MatrixTable.ofRel e (fun p s=>decide (p=o.one ∧ s=x))⟩

@[simp] theorem atom_total (o : Ops M) (e : Enumeration M) (x : M) :
    (atom o e x).total=x := rfl

theorem atom_true (o : Ops M) (e : Enumeration M) (x p s : M) :
    relation (atom o e x) p s=true ↔ p=o.one ∧ s=x := by
  simp only [relation,atom,MatrixTable.denote_ofRel,decide_eq_true_eq]

def trace (o : Ops M) (e : Enumeration M) (xs : List M) : Summary e :=
  product (ops o e) (xs.map (atom o e))

theorem trace_total (o : Ops M) (e : Enumeration M) (xs : List M) :
    (trace o e xs).total=product o xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change o.mul x (trace o e xs).total=o.mul x (product o xs)
    rw [ih]

theorem trace_strict (o : Ops M) (e : Enumeration M) (xs : List M) (p s : M) :
    relation (trace o e xs) p s=true ↔
      ∃ i,i<xs.length ∧ product o (xs.take i)=p ∧ product o (xs.drop i)=s := by
  induction xs generalizing p s with
  | nil =>
    change relation (one o e) p s=true ↔ _
    simp only [one_relation,Bool.false_eq_true,List.length_nil,Nat.not_lt_zero,
      false_and,exists_false]
  | cons x xs ih =>
    change relation (mul o e (atom o e x) (trace o e xs)) p s=true ↔ _
    rw [mul_true]
    simp only [atom_true,atom_total,trace_total,ih]
    constructor
    · rintro (⟨t,⟨hp,ht⟩,hs⟩|⟨t,⟨i,hi,hp,hs⟩,he⟩)
      · refine ⟨0,by simp,?_,?_⟩
        · exact hp.symm
        · simpa only [List.drop_zero,product,ht] using hs
      · refine ⟨i+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hi,?_,hs⟩
        change o.mul x (product o (xs.take i))=p
        rw [hp,he]
    · rintro ⟨i,hi,hp,hs⟩
      cases i with
      | zero =>
        exact Or.inl ⟨x,⟨hp.symm,rfl⟩,hs⟩
      | succ i =>
        refine Or.inr ⟨product o (xs.take i),⟨i,by simpa using hi,rfl,hs⟩,hp⟩

/-- The inclusive terminal cut is added exactly once as a Boolean union. -/
def closed (o : Ops M) (a : Summary e) : Rel M := fun p s=>
  relation a p s || decide (p=a.total ∧ s=o.one)

theorem trace_closed (o : Ops M) (e : Enumeration M) (xs : List M) (p s : M) :
    closed o (trace o e xs) p s=true ↔
      ∃ i,i≤xs.length ∧ product o (xs.take i)=p ∧ product o (xs.drop i)=s := by
  simp only [closed,Bool.or_eq_true,decide_eq_true_eq,trace_strict,trace_total]
  constructor
  · rintro (⟨i,hi,hp,hs⟩|⟨hp,hs⟩)
    · exact ⟨i,Nat.le_of_lt hi,hp,hs⟩
    · exact ⟨xs.length,Nat.le_refl _,by simpa using hp.symm,by simpa [product] using hs.symm⟩
  · rintro ⟨i,hi,hp,hs⟩
    by_cases h : i<xs.length
    · exact Or.inl ⟨i,h,hp,hs⟩
    · have he : i=xs.length := by omega
      subst i
      exact Or.inr ⟨by simpa using hp.symm,by simpa [product] using hs.symm⟩

end REWB.MaskedCut
