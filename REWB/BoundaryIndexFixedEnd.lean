import REWB.BoundaryIndexCuts

/-! The bounded-cut index specialized to the fixed-source-end predicate.
A and D run in parallel before the cut; B runs after it. All cut windows
query the same indexes over the original text. The reversed-trie statement
at the end records the orientation used by the boundary-index construction. -/
namespace REWB.BoundaryIndex.FixedEnd
open REWB.Spec (slice)
variable {α : Type}

def pairMachine (A D : DFA α) : RegularDFA.Machine α where
  State := Fin A.stateCount×Fin D.stateCount
  decEq := inferInstance
  enumeration := RegularDFA.prodEnum (FiniteRelation.finEnum A.stateCount)
    (FiniteRelation.finEnum D.stateCount)
  initial := (A.initial,D.initial)
  step := fun q c=>(A.step q.1 c,D.step q.2 c)
  final := fun q=>A.final q.1 && D.final q.2

theorem pair_run (A D : DFA α) (a : Fin A.stateCount) (d : Fin D.stateCount) (w : Word α) :
    (pairMachine A D).run (a,d) w=(A.run a w,D.run d w) := by
  induction w generalizing a d with
  | nil => rfl
  | cons c cs ih => exact ih _ _

def leftDFA (A D : DFA α) : DFA α := (pairMachine A D).toDFA

def initial (A D : DFA α) (a : Fin A.stateCount) (d : Fin D.stateCount) :
    Fin (leftDFA A D).stateCount := (pairMachine A D).encode (a,d)

theorem left_final (A D : DFA α) (a : Fin A.stateCount) (d : Fin D.stateCount) (w : Word α) :
    (leftDFA A D).final ((leftDFA A D).run (initial A D a d) w)=
      (A.final (A.run a w) && D.final (D.run d w)) := by
  change (pairMachine A D).final ((pairMachine A D).decode
    ((pairMachine A D).toDFA.run ((pairMachine A D).encode (a,d)) w))=_
  rw [RegularDFA.Machine.toDFA_run,RegularDFA.Machine.decode_encode,pair_run]
  rfl

abbrev Index (A B D : DFA α) := Cuts.Index (leftDFA A D) B

def build (A B D : DFA α) (w : Word α) : Index A B D×Nat := Cuts.build (leftDFA A D) B w

/-- The cut is the start of the B suffix of length L. A depth window
lo≤L≤hi therefore becomes the forward cut interval [a-hi,a-lo]. -/
def query (A B D : DFA α) (idx : Index A B D) (a depth lo hi : Nat)
    (alpha : Fin A.stateCount) (delta : Fin D.stateCount) : Cuts.Result :=
  Cuts.query (leftDFA A D) B idx (a-depth) (a-hi) (a-lo) a (initial A D alpha delta)

/-- Exact fixed-end factor predicate with arbitrary A and D entry states. -/
def Predicate (A B D : DFA α) (w : Word α) (a depth lo hi : Nat)
    (alpha : Fin A.stateCount) (delta : Fin D.stateCount) : Prop :=
  ∃ L, lo≤L ∧ L≤hi ∧
    A.final (A.run alpha (slice w (a-depth) (a-L)))=true ∧
    D.final (D.run delta (slice w (a-depth) (a-L)))=true ∧
    B.accepts (slice w (a-L) a)

theorem query_correct (A B D : DFA α) (w : Word α) (a depth lo hi : Nat)
    (alpha : Fin A.stateCount) (delta : Fin D.stateCount)
    (hlo : lo≤hi) (hhi : hi≤depth) (hd : depth≤a) (ha : a≤w.length) :
    (query A B D (build A B D w).1 a depth lo hi alpha delta).answer=some true ↔
      Predicate A B D w a depth lo hi alpha delta := by
  unfold query build
  rw [Cuts.query_correct _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) ha]
  simp only [left_final,Bool.and_eq_true,Predicate]
  constructor
  · rintro ⟨i,hli,hih,⟨hA,hD⟩,hB⟩
    have hia : i≤a := by omega
    have he : a-(a-i)=i := by omega
    refine ⟨a-i,by omega,by omega,?_,?_,?_⟩
    · simpa only [he] using hA
    · simpa only [he] using hD
    · simpa only [he] using hB
  · rintro ⟨L,hLlo,hLhi,hA,hD,hB⟩
    exact ⟨a-L,by omega,by omega,⟨hA,hD⟩,hB⟩

theorem query_bounds (A B D : DFA α) (w : Word α) (a depth lo hi : Nat)
    (alpha : Fin A.stateCount) (delta : Fin D.stateCount)
    (hlo : lo≤hi) (hhi : hi≤depth) (hd : depth≤a) (ha : a≤w.length) :
    (query A B D (build A B D w).1 a depth lo hi alpha delta).products≤6 ∧
    (query A B D (build A B D w).1 a depth lo hi alpha delta).visits≤3*(Nat.log2 w.length+2) :=
  Cuts.query_bounds _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) ha

theorem build_products (A B D : DFA α) (w : Word α) :
    (build A B D w).2=2*((Nat.log2 w.length+1)*w.length) := Cuts.build_products _ _ _

/-- Predicate in the audit's reversed-trie notation: X is the path label
read in reversed order; the actual input fragment is X.reverse. -/
def ReversePredicate (A B D : DFA α) (X : Word α) (lo hi : Nat)
    (alpha : Fin A.stateCount) (delta : Fin D.stateCount) : Prop :=
  ∃ L, lo≤L ∧ L≤hi ∧ B.accepts (X.take L).reverse ∧
    A.final (A.run alpha (X.drop L).reverse)=true ∧
    D.final (D.run delta (X.drop L).reverse)=true

theorem reverse_query_correct (A B D : DFA α) (X : Word α) (lo hi : Nat)
    (alpha : Fin A.stateCount) (delta : Fin D.stateCount)
    (hlo : lo≤hi) (hhi : hi≤X.length) :
    (query A B D (build A B D X.reverse).1 X.length X.length lo hi alpha delta).answer=some true ↔
      ReversePredicate A B D X lo hi alpha delta := by
  rw [query_correct A B D X.reverse X.length X.length lo hi alpha delta hlo hhi (Nat.le_refl _)
    (by simpa only [List.length_reverse] using Nat.le_refl X.length)]
  unfold Predicate ReversePredicate
  constructor
  · rintro ⟨L,hLlo,hLhi,hA,hD,hB⟩
    have hL : L≤X.length := by omega
    have hpre : slice X.reverse (X.length-X.length) (X.length-L)=(X.drop L).reverse := by
      simp only [Nat.sub_self,slice,List.drop_zero,Nat.sub_zero,← List.reverse_drop]
    have hsuf : slice X.reverse (X.length-L) X.length=(X.take L).reverse := by
      have hh := MaskScan.slice_to_end X.reverse (X.length-L) (by simp)
      simp only [List.length_reverse] at hh
      rw [hh,List.drop_reverse,show X.length-(X.length-L)=L by omega]
    rw [hpre] at hA hD
    rw [hsuf] at hB
    exact ⟨L,hLlo,hLhi,hB,hA,hD⟩
  · rintro ⟨L,hLlo,hLhi,hB,hA,hD⟩
    have hL : L≤X.length := by omega
    have hpre : slice X.reverse (X.length-X.length) (X.length-L)=(X.drop L).reverse := by
      simp only [Nat.sub_self,slice,List.drop_zero,Nat.sub_zero,← List.reverse_drop]
    have hsuf : slice X.reverse (X.length-L) X.length=(X.take L).reverse := by
      have hh := MaskScan.slice_to_end X.reverse (X.length-L) (by simp)
      simp only [List.length_reverse] at hh
      rw [hh,List.drop_reverse,show X.length-(X.length-L)=L by omega]
    exact ⟨L,hLlo,hLhi,hpre ▸ hA,hpre ▸ hD,hsuf ▸ hB⟩

end REWB.BoundaryIndex.FixedEnd
