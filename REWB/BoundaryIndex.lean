import REWB.MarkedTransfer

/-! Finite colored-position aggregates for the boundary index.

The represented set may have many positions. Its summary contains one DFA
transition table and one reachable-state table per color. Color maps are
arbitrary: several old colors can merge into the same new color. The merge is
Boolean union, so endpoints are retained even for noninjective maps.

The executable tables use materialized vectors. The `View` functions below
are only their extensional specification. They are not accumulated closures
in the executable implementation. -/
namespace REWB.BoundaryIndex
open REWB.FiniteRelation

structure View (k m : Nat) where
  trans : Fin m → Fin m
  active : Fin k → Fin m → Bool

namespace View
variable {k m : Nat}

@[ext] theorem ext {a b : View k m} (ht : a.trans=b.trans) (ha : a.active=b.active) : a=b := by
  cases a; cases b; simp_all

def one : View k m := ⟨id,fun _ _=>false⟩

def mul (a b : View k m) : View k m :=
  ⟨fun q=>b.trans (a.trans q),fun c q=>b.active c q ||
    any (finEnum m) (fun p=>a.active c p && decide (b.trans p=q))⟩

@[simp] theorem mul_trans (a b : View k m) (q : Fin m) :
    (mul a b).trans q=b.trans (a.trans q) := rfl

theorem mul_active (a b : View k m) (c : Fin k) (q : Fin m) :
    (mul a b).active c q=true ↔ b.active c q=true ∨
      ∃ p, a.active c p=true ∧ b.trans p=q := by
  simp only [mul,Bool.or_eq_true,any_true,Bool.and_eq_true,decide_eq_true_eq]

theorem one_mul (a : View k m) : mul one a=a := by
  apply ext
  · rfl
  · funext c q
    apply Bool.eq_iff_iff.mpr
    simp [mul_active,one]

theorem mul_one (a : View k m) : mul a one=a := by
  apply ext
  · rfl
  · funext c q
    apply Bool.eq_iff_iff.mpr
    simp [mul_active,one]

theorem mul_assoc (a b c : View k m) : mul (mul a b) c=mul a (mul b c) := by
  apply ext
  · rfl
  · funext color q
    apply Bool.eq_iff_iff.mpr
    simp only [mul_active,mul_trans]
    constructor
    · rintro (hc | ⟨p,(hb | ⟨r,ha,he⟩),hq⟩)
      · exact Or.inl (Or.inl hc)
      · exact Or.inl (Or.inr ⟨p,hb,hq⟩)
      · exact Or.inr ⟨r,ha,by rw [he,hq]⟩
    · rintro ((hc | ⟨p,hb,hq⟩) | ⟨r,ha,hq⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨p,Or.inl hb,hq⟩
      · exact Or.inr ⟨b.trans r,Or.inr ⟨r,ha,rfl⟩,hq⟩

def ops : RangeProducts.Ops (View k m) :=
  ⟨one,mul,one_mul,mul_one,mul_assoc⟩

def rename (g : Fin k→Fin k) (a : View k m) : View k m :=
  ⟨a.trans,fun c q=>any (finEnum k) (fun old=>decide (g old=c) && a.active old q)⟩

@[simp] theorem rename_trans (g : Fin k→Fin k) (a : View k m) (q : Fin m) :
    (rename g a).trans q=a.trans q := rfl

theorem rename_active (g : Fin k→Fin k) (a : View k m) (c : Fin k) (q : Fin m) :
    (rename g a).active c q=true ↔ ∃ old, g old=c ∧ a.active old q=true := by
  simp only [rename,any_true,Bool.and_eq_true,decide_eq_true_eq]

theorem rename_id (a : View k m) : rename id a=a := by
  apply ext
  · rfl
  · funext c q
    apply Bool.eq_iff_iff.mpr
    simp [rename_active]

theorem rename_comp (g f : Fin k→Fin k) (a : View k m) :
    rename g (rename f a)=rename (fun c=>g (f c)) a := by
  apply ext
  · rfl
  · funext c q
    apply Bool.eq_iff_iff.mpr
    simp only [rename_active]
    constructor
    · rintro ⟨d,hd,e,he,ha⟩
      exact ⟨e,by rw [he,hd],ha⟩
    · rintro ⟨e,he,ha⟩
      exact ⟨f e,he,e,rfl,ha⟩

theorem rename_one (g : Fin k→Fin k) : rename g (one : View k m)=one := by
  apply ext
  · rfl
  · funext c q
    apply Bool.eq_iff_iff.mpr
    simp [rename_active,one]

theorem rename_mul (g : Fin k→Fin k) (a b : View k m) :
    rename g (mul a b)=mul (rename g a) (rename g b) := by
  apply ext
  · rfl
  · funext c q
    apply Bool.eq_iff_iff.mpr
    simp only [rename_active,mul_active,rename_trans]
    constructor
    · rintro ⟨old,he,(hb | ⟨p,ha,hq⟩)⟩
      · exact Or.inl ⟨old,he,hb⟩
      · exact Or.inr ⟨p,⟨old,he,ha⟩,hq⟩
    · rintro (⟨old,he,hb⟩ | ⟨p,⟨old,he,ha⟩,hq⟩)
      · exact ⟨old,he,Or.inl hb⟩
      · exact ⟨old,he,Or.inr ⟨p,ha,hq⟩⟩

def product : List (View k m)→View k m := RangeProducts.product ops

theorem product_append (xs ys : List (View k m)) :
    product (xs++ys)=mul (product xs) (product ys) :=
  RangeProducts.product_append ops xs ys

theorem rename_product (g : Fin k→Fin k) (xs : List (View k m)) :
    rename g (product xs)=product (xs.map (rename g)) := by
  induction xs with
  | nil => exact rename_one g
  | cons a xs ih =>
    change rename g (mul a (product xs))=mul (rename g a) (product (xs.map (rename g)))
    rw [rename_mul,ih]

end View

/-- Fixed-size tables. Reads do not follow a chain of earlier color maps. -/
structure Table (k m : Nat) where
  trans : Vector (Fin m) m
  active : Vector (Vector Bool m) k

namespace Table
variable {k m : Nat}

def view (a : Table k m) : View k m := ⟨a.trans.get,fun c q=>(a.active.get c).get q⟩

def ofView (a : View k m) : Table k m :=
  ⟨Vector.ofFn a.trans,Vector.ofFn (fun c=>Vector.ofFn (a.active c))⟩

@[simp] theorem get_ofFn {n : Nat} {β : Type} (f : Fin n→β) (i : Fin n) :
    (Vector.ofFn f).get i=f i := by
  simp [Vector.get,Vector.getElem_ofFn]

@[simp] theorem view_ofView (a : View k m) : view (ofView a)=a := by
  apply View.ext
  · funext q; simp [view,ofView]
  · funext c q; simp [view,ofView]

def one : Table k m := ofView View.one

def mul (a b : Table k m) : Table k m := ofView (View.mul a.view b.view)

def rename (g : Vector (Fin k) k) (a : Table k m) : Table k m :=
  ofView (View.rename g.get a.view)

@[simp] theorem view_one : (one : Table k m).view=View.one := view_ofView _
@[simp] theorem view_mul (a b : Table k m) : (mul a b).view=View.mul a.view b.view := view_ofView _
@[simp] theorem view_rename (g : Vector (Fin k) k) (a : Table k m) :
    (rename g a).view=View.rename g.get a.view := view_ofView _

end Table

/-- A marker inserts an endpoint. A letter moves every existing endpoint
through the same DFA transition. Markers do not consume text. -/
inductive Token (α : Type) (k : Nat) where
  | letter : α→Token α k
  | mark : Fin k→Token α k

def erase {α : Type} {k : Nat} : List (Token α k)→Word α
  | [] => []
  | .letter c::xs => c::erase xs
  | .mark _::xs => erase xs

theorem erase_append {α : Type} {k : Nat} (xs ys : List (Token α k)) :
    erase (xs++ys)=erase xs++erase ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [erase,ih]

def atom {α : Type} {k : Nat} (d : DFA α) : Token α k→Table k d.stateCount
  | .letter a => Table.ofView ⟨fun q=>d.step q a,fun _ _=>false⟩
  | .mark c => Table.ofView ⟨id,fun b q=>decide (b=c ∧ d.initial=q)⟩

def trace {α : Type} {k : Nat} (d : DFA α) (xs : List (Token α k)) : View k d.stateCount :=
  View.product (xs.map (fun t=>(atom d t).view))

theorem trace_trans {α : Type} {k : Nat} (d : DFA α) (xs : List (Token α k))
    (q : Fin d.stateCount) : (trace d xs).trans q=d.run q (erase xs) := by
  induction xs generalizing q with
  | nil => rfl
  | cons t xs ih =>
    cases t with
    | letter c =>
      change (trace d xs).trans ((atom d (.letter c)).view.trans q)=_
      simp only [atom,Table.view_ofView]
      exact ih _
    | mark c =>
      change (trace d xs).trans ((atom d (.mark c)).view.trans q)=_
      simp only [atom,Table.view_ofView]
      exact ih _

/-- The direct endpoint semantics, including multiple endpoints of a color. -/
def Active {α : Type} {k : Nat} (d : DFA α) (xs : List (Token α k))
    (c : Fin k) (q : Fin d.stateCount) : Prop :=
  ∃ pre post, xs=pre++Token.mark c::post ∧ d.run d.initial (erase post)=q

theorem active_nil {α : Type} {k : Nat} (d : DFA α) (c : Fin k) (q : Fin d.stateCount) :
    ¬Active d [] c q := by
  rintro ⟨pre,post,h,_⟩
  have := congrArg List.length h
  simp only [List.length_nil,List.length_append,List.length_cons] at this
  omega

theorem active_cons {α : Type} {k : Nat} (d : DFA α) (t : Token α k)
    (xs : List (Token α k)) (c : Fin k) (q : Fin d.stateCount) :
    Active d (t::xs) c q ↔ Active d xs c q ∨
      (t=.mark c ∧ d.run d.initial (erase xs)=q) := by
  constructor
  · rintro ⟨pre,post,h,hr⟩
    cases pre with
    | nil =>
      simp only [List.nil_append,List.cons.injEq] at h
      exact Or.inr ⟨h.1,h.2 ▸ hr⟩
    | cons a pre =>
      simp only [List.cons_append,List.cons.injEq] at h
      exact Or.inl ⟨pre,post,h.2,hr⟩
  · rintro (⟨pre,post,h,hr⟩ | ⟨ht,hr⟩)
    · exact ⟨t::pre,post,by simp [h],hr⟩
    · exact ⟨[],xs,by simp [ht],hr⟩

theorem trace_active {α : Type} {k : Nat} (d : DFA α) (xs : List (Token α k))
    (c : Fin k) (q : Fin d.stateCount) : (trace d xs).active c q=true ↔ Active d xs c q := by
  induction xs with
  | nil => simp [trace,View.product,RangeProducts.product,View.ops,View.one,active_nil]
  | cons t xs ih =>
    change (View.mul (atom d t).view (trace d xs)).active c q=true ↔ _
    rw [View.mul_active,ih,active_cons]
    cases t with
    | letter a => simp [atom,trace_trans]
    | mark b =>
      simp only [atom,Table.view_ofView,decide_eq_true_eq,trace_trans,Token.mark.injEq]
      constructor
      · rintro (h | ⟨p,⟨hcb,hp⟩,hr⟩)
        · exact Or.inl h
        · exact Or.inr ⟨hcb.symm,by rw [hp]; exact hr⟩
      · rintro (h | ⟨hbc,hr⟩)
        · exact Or.inl h
        · exact Or.inr ⟨d.initial,⟨hbc.symm,rfl⟩,hr⟩

/-- Inspect the aggregate at its actual right endpoint. This operation
never tries to invert a DFA transition from a later endpoint. -/
def accepted {α : Type} {k : Nat} (d : DFA α) (select : Fin k→Bool)
    (a : Table k d.stateCount) : Bool :=
  any (finEnum k) (fun c=>select c &&
    any (finEnum d.stateCount) (fun q=>a.view.active c q && d.final q))

theorem accepted_true {α : Type} {k : Nat} (d : DFA α) (select : Fin k→Bool)
    (a : Table k d.stateCount) :
    accepted d select a=true ↔ ∃ c q, select c=true ∧ a.view.active c q=true ∧ d.final q=true := by
  simp only [accepted,any_true,Bool.and_eq_true]
  constructor
  · rintro ⟨c,hc,q,ha,hq⟩; exact ⟨c,q,hc,ha,hq⟩
  · rintro ⟨c,q,hc,ha,hq⟩; exact ⟨c,hc,q,ha,hq⟩

theorem accepted_trace {α : Type} {k : Nat} (d : DFA α) (select : Fin k→Bool)
    (a : Table k d.stateCount) (xs : List (Token α k)) (h : a.view=trace d xs) :
    accepted d select a=true ↔ ∃ pre post c,
      xs=pre++Token.mark c::post ∧ select c=true ∧ d.accepts (erase post) := by
  rw [accepted_true]
  simp only [h,trace_active,Active,DFA.accepts]
  constructor
  · rintro ⟨c,q,hc,⟨pre,post,hx,hr⟩,hf⟩
    exact ⟨pre,post,c,hx,hc,by rw [hr]; exact hf⟩
  · rintro ⟨pre,post,c,hx,hc,hf⟩
    exact ⟨c,d.run d.initial (erase post),hc,⟨pre,post,hx,rfl⟩,hf⟩

end REWB.BoundaryIndex
