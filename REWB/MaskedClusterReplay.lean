import REWB.MaskedClusterCursorBudget
import REWB.MaskedCutDFA

/-! The finite universe needed by the cursor compiler is exactly the
    product of the C/E transformation universes. It contains no text
    positions, occurrence counts, period phases or copy lengths.

    The materialized catalog can be prepared once for a fixed pattern.
    Enumeration and encoding work is deliberately separate from the
    existing finite-action tree counters. Replay composition below calls
    an actual counted vector composition for each automaton.
-/
namespace REWB.MaskedCluster.ReplayMaps
open REWB.MaskedFiniteAction
variable {α : Type}

abbrev Value (c e : Nat) := Maps.Map c×Maps.Map e

def enumeration (c e : Nat) : FiniteRelation.Enumeration (Value c e) :=
  MaskedCut.DFAIndex.prodEnum (MaskedCut.DFAIndex.mapEnum c) (MaskedCut.DFAIndex.mapEnum e)

def count (c e : Nat) : Nat := (enumeration c e).elems.length

theorem count_eq (c e : Nat) : count c e=c^c*e^e := by
  simp only [count,enumeration,MaskedCut.DFAIndex.prodEnum_length]
  change Maps.count c*Maps.count e=_
  rw [Maps.count_eq,Maps.count_eq]

def one (c e : Nat) : Value c e := (Maps.identity c,Maps.identity e)

def mul {c e : Nat} (a b : Value c e) : Value c e :=
  (Maps.mul a.1 b.1,Maps.mul a.2 b.2)

theorem mul_assoc {c e : Nat} (a b d : Value c e) : mul (mul a b) d=mul a (mul b d) := by
  simp only [mul,Maps.mul_assoc]

theorem one_mul {c e : Nat} (a : Value c e) : mul (one c e) a=a := by
  exact (MaskedCut.DFAIndex.prodOps (MaskedCut.DFAIndex.mapOps c) (MaskedCut.DFAIndex.mapOps e)).one_mul a

theorem mul_one {c e : Nat} (a : Value c e) : mul a (one c e)=a := by
  exact (MaskedCut.DFAIndex.prodOps (MaskedCut.DFAIndex.mapOps c) (MaskedCut.DFAIndex.mapOps e)).mul_one a

def mulCounted {c e : Nat} (a b : Value c e) : Value c e×Nat :=
  let cc:=BoundaryIndex.Counted.compose b.1 a.1
  let ee:=BoundaryIndex.Counted.compose b.2 a.2
  ((cc.1,ee.1),cc.2+ee.2)

theorem mulCounted_value {c e : Nat} (a b : Value c e) : (mulCounted a b).1=mul a b := by
  apply Prod.ext
  · apply Vector.ext
    intro i hi
    change (BoundaryIndex.Counted.compose b.1 a.1).1.get ⟨i,hi⟩=(Maps.mul a.1 b.1).get ⟨i,hi⟩
    simp only [BoundaryIndex.Counted.compose_get,Maps.mul_get]
  · apply Vector.ext
    intro i hi
    change (BoundaryIndex.Counted.compose b.2 a.2).1.get ⟨i,hi⟩=(Maps.mul a.2 b.2).get ⟨i,hi⟩
    simp only [BoundaryIndex.Counted.compose_get,Maps.mul_get]

theorem mulCounted_steps {c e : Nat} (a b : Value c e) : (mulCounted a b).2=c+e := rfl

private theorem get_idx [DecidableEq β] [BEq β] [LawfulBEq β]
    (xs : List β) (x : β) (h : x∈xs) : xs[xs.idxOf x]?=some x := by
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

def encode {c e : Nat} (a : Value c e) : Fin (count c e) :=
  ⟨(enumeration c e).elems.idxOf a,List.idxOf_lt_length ((enumeration c e).complete a)⟩

def decode (c e : Nat) (i : Fin (count c e)) : Value c e :=
  ((enumeration c e).elems[i.val]?).getD (one c e)

theorem decode_encode {c e : Nat} (a : Value c e) : decode c e (encode a)=a := by
  unfold decode encode
  rw [get_idx _ _ ((enumeration c e).complete a)]
  rfl

def catalog (c e : Nat) : Vector (Value c e) (count c e) := Vector.ofFn (decode c e)

theorem catalog_get (c e : Nat) (i : Fin (count c e)) : (catalog c e).get i=decode c e i := by
  simp only [catalog,BoundaryIndex.Table.get_ofFn]

/-- One immutable pattern catalog, shared by every cluster bank. -/
structure Prepared (c e : Nat) where
  values : Vector (Value c e) (count c e)
  exact : ∀ i,values.get i=decode c e i

def prepare (c e : Nat) : Prepared c e := ⟨catalog c e,catalog_get c e⟩

/-- Reindex the extra prefix T by T*z. A source-bank selector is stored
    outside this pair index and will be preserved by the lifted action. -/
def rightAction {c e : Nat} (z : Value c e) : Vector (Fin (count c e)) (count c e) :=
  Vector.ofFn fun i=>encode (mul (decode c e i) z)

theorem rightAction_get {c e : Nat} (z : Value c e) (i : Fin (count c e)) :
    (rightAction z).get i=encode (mul (decode c e i) z) := by
  simp only [rightAction,BoundaryIndex.Table.get_ofFn]

theorem rightAction_decode {c e : Nat} (z : Value c e) (i : Fin (count c e)) :
    decode c e ((rightAction z).get i)=mul (decode c e i) z := by
  rw [rightAction_get,decode_encode]

theorem rightAction_comp {c e : Nat} (z0 z1 : Value c e) (i : Fin (count c e)) :
    (rightAction z0).get ((rightAction z1).get i)=
      (rightAction (mul z1 z0)).get i := by
  rw [rightAction_get,rightAction_decode,rightAction_get,mul_assoc]

def word (C E : DFA α) (w : Word α) : Value C.stateCount E.stateCount :=
  (Maps.wordMap C w,Maps.wordMap E w)

theorem word_append (C E : DFA α) (u v : Word α) : word C E (u++v)=mul (word C E u) (word C E v) := by
  simp only [word,mul,Maps.wordMap_append]

/-- Old local tails can differ. Equal actual old-length copies suffice
    to identify the newly exposed prefix with the representative's
    prefix; equality of the longer local anchors is not assumed. -/
theorem common_shortening (C E : DFA α) (w : Word α) (representative start fresh old H : Nat)
    (hnew : fresh≤old) (hH : old≤H)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w start (start+old)) :
    word C E (Spec.slice w (start+fresh) (start+H))=
      mul (word C E (Spec.slice w (representative+fresh) (representative+old)))
        (word C E (Spec.slice w (start+old) (start+H))) := by
  have he:=MaskedClusterStage.anchor_tail w representative start fresh old hcopy
  rw [OuterColumn.slice_split w (start+fresh) (start+old) (start+H) (by omega) (by omega),
    word_append,←he]

theorem replay_common_shortening (C E : DFA α) (w : Word α) (representative start fresh old H : Nat)
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : start+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w start (start+old)) :
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) start fresh H).maps=
      mul (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        representative fresh old).maps
        (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) start old H).maps := by
  rw [replay_value C E w start fresh H (by omega) hstart,
    replay_value C E w representative fresh old hnew hrep,replay_value C E w start old H hH hstart]
  exact common_shortening C E w representative start fresh old H hnew hH hcopy

end REWB.MaskedCluster.ReplayMaps
