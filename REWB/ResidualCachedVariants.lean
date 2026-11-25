import REWB.ResidualDispatchQueries
import REWB.BoundaryRangeCacheCost
import REWB.OneUseRangeCacheCost

/-! Finite, fixed-pattern variants for the separated residual queries.
The three text-dependent choices use shared transition-map indexes.
No factor is copied, and no DFA or text index is constructed by a
selector. The finite DFA compilation is fixed-pattern preprocessing;
the counters here measure the actual text/map/table operations. -/
namespace REWB.ResidualCached
open REWB.BoundaryApplication REWB.BoundaryRange REWB.BoundaryIndex
variable {σ : Nat}

def gap (P : SevenDFA (Fin σ)) (g : Fin P.G.stateCount) : DFA (Fin σ) :=
  Automata.start P.G g

def suffix (P : SevenDFA (Fin σ)) (q : Fin P.G.stateCount)
    (c : TableColor.Key P.H) : DFA (Fin σ) :=
  Automata.join P.F (Automata.meet (Automata.stop P.G q)
    (Automata.finish P.H (Colors.decode P.H c)))

def front (P : SevenDFA (Fin σ)) (a : Fin P.A.stateCount)
    (g : Fin P.G.stateCount) : DFA (Fin σ) :=
  Automata.join (Automata.meet (Automata.start P.A a) (gap P g)) P.B

structure Selectors (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) where
  aranges : Range.Index P.A
  granges : Range.Index P.G
  tailKeys : OneUseRange.FarSelection.Index P.H w
  states : List (Fin P.G.stateCount)
  length : Nat
  length_eq : length=w.length
  work : Nat

def prepareSelectors (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) : Selectors P w :=
  let aranges:=Range.build P.A w
  let granges:=Range.build P.G w
  let tailKeys:=OneUseRange.FarSelection.build P.H w
  let states:=List.finRange P.G.stateCount
  ⟨aranges,granges,tailKeys,states,w.length,rfl,
    StartIndex.rangeBuildWork P.A aranges+StartIndex.rangeBuildWork P.G granges+
      tailKeys.work+P.G.stateCount+w.length+6⟩

structure Choice (P : SevenDFA (Fin σ)) where
  initial : Fin P.A.stateCount
  middle : Range.Map P.G.stateCount
  tailKey : TableColor.Key P.H
  work : Nat

def select {P : SevenDFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Selectors P w) (left right shift : Nat) : Choice P :=
  let initial:=Range.query P.A idx.aranges 0 left
  let middle:=Range.query P.G idx.granges right (left+shift)
  let tailKey:=OneUseRange.FarSelection.key idx.tailKeys (right+shift) idx.length
  ⟨initial.map.get P.A.initial,middle.map,tailKey.1,
    initial.work+middle.work+tailKey.2+6⟩

theorem select_gap (P : SevenDFA (Fin σ)) (w : Word (Fin σ))
    (left right shift : Nat) (q : Fin P.G.stateCount) :
    gap P ((select (prepareSelectors P w) left right shift).middle.get q)=
      ResidualSeparated.gapStart P.G (Range.build P.G w) left right shift q := rfl

theorem select_suffix (P : SevenDFA (Fin σ)) (w : Word (Fin σ))
    (left right shift : Nat) (q : Fin P.G.stateCount) :
    suffix P q (select (prepareSelectors P w) left right shift).tailKey=
      ResidualSeparated.outerSuffix P.F P.G P.H (Range.build P.H w) right shift w.length q := by
  unfold suffix ResidualSeparated.outerSuffix
  have hh:=OneUseRange.FarSelection.key_variant P.H w (right+shift) w.length
  change Automata.finish P.H (Colors.decode P.H
    (select (prepareSelectors P w) left right shift).tailKey)=_ at hh
  rw [hh]

theorem select_front (P : SevenDFA (Fin σ)) (w : Word (Fin σ))
    (left right shift : Nat) (q : Fin P.G.stateCount) :
    front P (select (prepareSelectors P w) left right shift).initial
      ((select (prepareSelectors P w) left right shift).middle.get q)=
      ResidualSeparated.innerPrefix P.A P.B P.G (Range.build P.A w)
        (Range.build P.G w) left right shift q := rfl

def selectorBuildBudget (P : SevenDFA (Fin σ)) (n : Nat) : Nat :=
  StartIndex.rangeBound P.A n+StartIndex.rangeBound P.G n+
    OneUseRange.FarSelection.buildBudget P.H n+P.G.stateCount+n+6

theorem prepareSelectors_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) :
    (prepareSelectors P w).work=selectorBuildBudget P w.length := by
  simp only [prepareSelectors,selectorBuildBudget,StartIndex.rangeBuildWork_build,
    OneUseRange.FarSelection.build_work]

def selectorBudget (P : SevenDFA (Fin σ)) (n : Nat) : Nat :=
  NearIndex.rangeBudget P.A n+NearIndex.rangeBudget P.G n+
    OneUseRange.FarSelection.keyBudget P.H n+6

theorem select_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ))
    (left right shift : Nat) (h : ResidualSeparated.Window w left right shift) :
    (select (prepareSelectors P w) left right shift).work≤selectorBudget P w.length := by
  have hl:=h.ordered
  have hn:=h.within
  have hm:=h.separated
  have ha:=Range.query_work P.A w 0 left (Nat.zero_le _) (by omega)
  have hg:=Range.query_work P.G w right (left+shift) hm (by omega)
  have ht:=OneUseRange.FarSelection.key_work P.H w (right+shift) w.length hn (Nat.le_refl _)
  change (Range.query P.A (Range.build P.A w) 0 left).work+
    (Range.query P.G (Range.build P.G w) right (left+shift)).work+
    (OneUseRange.FarSelection.key (OneUseRange.FarSelection.build P.H w)
      (right+shift) w.length).2+6≤_
  unfold selectorBudget NearIndex.rangeBudget
  omega

theorem ofFn_le_sum {n : Nat} (f : Fin n→Nat) (i : Fin n) :
    f i≤(List.ofFn f).sum := by
  have hm : f i∈List.ofFn f := List.mem_ofFn.mpr ⟨i,rfl⟩
  generalize he : List.ofFn f=xs at *
  clear he
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    simp only [List.mem_cons] at hm
    simp only [List.sum_cons]
    rcases hm with h|h
    · omega
    · have hh:=ih h
      omega

/-- Actual linear Boolean fold, with each callback executed once. -/
def any (f : α→Bool×Nat) : List α→Bool×Nat
  | [] => (false,1)
  | x::xs =>
    let one:=f x
    let rest:=any f xs
    (one.1 || rest.1,one.2+rest.2+3)

theorem any_correct (f : α→Bool×Nat) (xs : List α) :
    (any f xs).1=true ↔ ∃x,x∈xs ∧ (f x).1=true := by
  induction xs with
  | nil => simp [any]
  | cons x xs ih => simp [any,ih]

theorem any_work (f : α→Bool×Nat) (xs : List α) (bound : Nat)
    (h : ∀x,x∈xs→(f x).2≤bound) :
    (any f xs).2≤xs.length*(bound+3)+1 := by
  induction xs with
  | nil => simp [any]
  | cons x xs ih =>
    have hh:=h x List.mem_cons_self
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [any,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def anyTail (f : α→Bool×Nat) : List α→Bool→Nat→Bool×Nat
  | [],answer,work => (answer,work+1)
  | x::xs,answer,work =>
    let one:=f x
    anyTail f xs (answer || one.1) (work+one.2+3)

theorem anyTail_spec (f : α→Bool×Nat) (xs : List α) (answer : Bool) (work : Nat) :
    anyTail f xs answer work=(answer || (any f xs).1,work+(any f xs).2) := by
  induction xs generalizing answer work with
  | nil => simp [anyTail,any]
  | cons x xs ih =>
    simp only [anyTail,ih,any,Bool.or_assoc]
    congr 1
    omega

def anyTR (f : α→Bool×Nat) (xs : List α) : Bool×Nat := anyTail f xs false 0

@[csimp] theorem any_eq_anyTR : @any=@anyTR := by
  funext α f xs
  simp only [anyTR,anyTail_spec,Bool.false_or,Nat.zero_add]

end REWB.ResidualCached
