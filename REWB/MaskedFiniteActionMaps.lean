import REWB.MaskedFiniteAction
import REWB.OuterColumn

/-! An explicit fixed-pattern universe of materialized DFA transformations.

    There are m^m enumerated maps on an m-state automaton.  The universe
    contains no text positions or period phases.  Its enumeration and
    multiplication/index tables can be prepared once for a fixed pattern.
    The generic action-tree counters charge materialized reindex maps as
    inputs; they do not yet include this preprocessing or the text range
    queries used to select the actual shortening transformation.

    The final shortening theorem is an algebraic fact about slices.  It
    does not establish the proposed local-anchor cluster geometry. -/
namespace REWB.MaskedFiniteAction.Maps

abbrev Map (m : Nat) := Vector (Fin m) m

def vectors (m : Nat) : (n : Nat) → List (Vector (Fin m) n)
  | 0 => [#v[]]
  | n+1 => (vectors m n).flatMap (fun v =>
      (List.ofFn (fun i : Fin m => i)).map (fun x => v.push x))

theorem vectors_complete (m n : Nat) (v : Vector (Fin m) n) : v∈vectors m n := by
  induction n with
  | zero =>
    have hv : v=#v[] := by ext i hi; omega
    simp [vectors,hv]
  | succ n ih =>
    have hv : v=v.pop.push v.back := by simp
    rw [hv]
    apply List.mem_flatMap.mpr
    refine ⟨v.pop,ih v.pop,?_⟩
    apply List.mem_map.mpr
    exact ⟨v.back,by simp,rfl⟩

private theorem flatMap_length {α β : Type} (xs : List α) (f : α → List β)
    (c : Nat) (h : ∀ x, (f x).length=c) : (xs.flatMap f).length=xs.length*c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,h,ih,List.length_cons,
      Nat.add_mul,Nat.one_mul]
    omega

theorem vectors_length (m n : Nat) : (vectors m n).length=m^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [vectors,flatMap_length _ _ m (by intro v; simp),ih,Nat.pow_succ]

def allMaps (m : Nat) : List (Map m) := vectors m m
def count (m : Nat) : Nat := (allMaps m).length

theorem universe_complete (m : Nat) (f : Map m) : f∈allMaps m := vectors_complete m m f

theorem count_eq (m : Nat) : count m=m^m := vectors_length m m

def identity (m : Nat) : Map m := Vector.ofFn id

def mul {m : Nat} (a b : Map m) : Map m :=
  Vector.ofFn (fun q => b.get (a.get q))

@[simp] theorem mul_get {m : Nat} (a b : Map m) (q : Fin m) :
    (mul a b).get q=b.get (a.get q) := by
  simp only [mul,BoundaryIndex.Table.get_ofFn]

theorem mul_assoc {m : Nat} (a b c : Map m) : mul (mul a b) c=mul a (mul b c) := by
  apply Vector.ext
  intro i hi
  change (mul (mul a b) c).get ⟨i,hi⟩=(mul a (mul b c)).get ⟨i,hi⟩
  simp only [mul_get]

private theorem get_idx [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (h : x∈xs) :
    xs[xs.idxOf x]?=some x := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    by_cases he : x=a
    · subst x
      simp
    · have hx : x∈xs := (List.mem_cons.mp h).resolve_left he
      rw [List.idxOf_cons]
      simp only [cond_eq_if,beq_iff_eq,if_neg (Ne.symm he),List.getElem?_cons_succ]
      exact ih hx

def encode {m : Nat} (f : Map m) : Fin (count m) :=
  ⟨(allMaps m).idxOf f,List.idxOf_lt_length (universe_complete m f)⟩

def decode (m : Nat) (i : Fin (count m)) : Map m :=
  ((allMaps m)[i.val]?).getD (identity m)

theorem decode_encode {m : Nat} (f : Map m) : decode m (encode f)=f := by
  unfold decode encode
  change ((allMaps m)[(allMaps m).idxOf f]?).getD (identity m)=f
  rw [get_idx _ _ (universe_complete m f)]
  rfl

/-- The right-multiplication table is materialized once when selected.
    Its entries are map indices, not phases of a periodic text. -/
def rightAction {m : Nat} (z : Map m) : Vector (Fin (count m)) (count m) :=
  Vector.ofFn (fun i => encode (mul (decode m i) z))

theorem rightAction_get {m : Nat} (z : Map m) (i : Fin (count m)) :
    (rightAction z).get i=encode (mul (decode m i) z) := by
  simp only [rightAction,BoundaryIndex.Table.get_ofFn]

theorem rightAction_decode {m : Nat} (z : Map m) (i : Fin (count m)) :
    decode m ((rightAction z).get i)=mul (decode m i) z := by
  rw [rightAction_get,decode_encode]

/-- First prepend z0, then prepend z1: the combined word map is z1*z0.
    This explicitly fixes the order for lazy precomposition tags. -/
theorem rightAction_comp {m : Nat} (z0 z1 : Map m) (i : Fin (count m)) :
    (rightAction z0).get ((rightAction z1).get i)=
      (rightAction (mul z1 z0)).get i := by
  rw [rightAction_get,rightAction_decode,rightAction_get,mul_assoc]

def bank {m r : Nat} (f : Map m → FiniteRelation.Rel (Fin r)) : Table (count m) r :=
  Table.ofView (fun i => f (decode m i))

theorem bank_reindex {m r : Nat} (f : Map m → FiniteRelation.Rel (Fin r))
    (z : Map m) :
    (Counted.reindex (rightAction z) (bank f)).1.view=
      (bank (fun a => f (mul a z))).view := by
  rw [Counted.reindex_view]
  funext i p q
  simp only [bank,Table.view_ofView,View.reindex,rightAction_decode]

def wordMap {α : Type} (d : DFA α) (w : Word α) : Map d.stateCount :=
  Vector.ofFn (fun q => d.run q w)

@[simp] theorem wordMap_get {α : Type} (d : DFA α) (w : Word α)
    (q : Fin d.stateCount) : (wordMap d w).get q=d.run q w := by
  simp only [wordMap,BoundaryIndex.Table.get_ofFn]

theorem wordMap_append {α : Type} (d : DFA α) (u v : Word α) :
    wordMap d (u++v)=mul (wordMap d u) (wordMap d v) := by
  apply Vector.ext
  intro i hi
  change (wordMap d (u++v)).get ⟨i,hi⟩=(mul (wordMap d u) (wordMap d v)).get ⟨i,hi⟩
  simp only [wordMap_get,mul_get,DFA.run_append]

/-- Different local anchors may retain different old tails.  Every one
    of them receives the identical newly exposed prefix under shortening. -/
theorem localAnchor_shortening {α : Type} (d : DFA α) (w : Word α)
    (newLength oldLength anchor : Nat)
    (hlo : newLength≤oldLength) (hhi : oldLength≤anchor) :
    wordMap d (Spec.slice w newLength anchor)=
      mul (wordMap d (Spec.slice w newLength oldLength))
        (wordMap d (Spec.slice w oldLength anchor)) := by
  rw [OuterColumn.slice_split w newLength oldLength anchor hlo hhi,wordMap_append]

end REWB.MaskedFiniteAction.Maps
