import REWB.Integrated

/-! Actual counts of endpoint tests in the short-circuiting matcher.
    They are distinct from the cost of each indexed test, memory allocation,
    and the cost of preprocessing. -/
namespace REWB.EndpointCounts
open REWB.OuterTables
variable {α X : Type}

def scan (f : X → Bool × Nat) : List X → Bool × Nat
  | [] => (false,0)
  | x::xs =>
    let a := f x
    if a.1 then a else
      let b := scan f xs
      (b.1,a.2+b.2)

theorem scan_answer (f : X → Bool × Nat) (xs : List X) :
    (scan f xs).1=xs.any (fun x=>(f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : (f x).1 <;> simp [scan,h,ih]

theorem scan_bound (f : X → Bool × Nat) (xs : List X) (C : Nat)
    (h : ∀ x, x∈xs → (f x).2≤C) :
    (scan f xs).2≤xs.length*C := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (fun y hy=>h y (by simp [hy]))
    cases hf : (f x).1
    · simp only [scan,hf,if_false,Bool.false_eq_true,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simp only [scan,hf,if_true,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

def testColumn1 (P : SevenDFA α) (w : Word α) (I : Prepared P)
    (R : ReadyTable P) (t : Nat) : Bool × Nat :=
  let m := fun p => readyAt P R p t
  let idx := P1Index.build P (IndexedMarked.decorate m 0 w)
  scan (fun a => (Integrated.test1 P I m idx t a,1)) (List.range (t+1))

def testColumn2 (P : SevenDFA α) (w : Word α) (I : Prepared P)
    (R : ReadyTable P) (t : Nat) : Bool × Nat :=
  let r := fun p => readyAt P R p t
  let row := MaskScan.first2Row P w r
  let m := MaskScan.accepted P.B row
  let idx := (IndexedMarked.build P.D P.C (IndexedMarked.decorate m 0 w)).1
  scan (fun a => (Integrated.test2 P I m idx t a,1)) (List.range (t+1))

theorem col1_answer (P : SevenDFA α) (w : Word α) (I : Prepared P)
    (R : ReadyTable P) (t : Nat) :
    (testColumn1 P w I R t).1=Integrated.col1 P w I R t := by
  unfold testColumn1 Integrated.col1
  dsimp only
  rw [scan_answer]

theorem col2_answer (P : SevenDFA α) (w : Word α) (I : Prepared P)
    (R : ReadyTable P) (t : Nat) :
    (testColumn2 P w I R t).1=Integrated.col2 P w I R t := by
  unfold testColumn2 Integrated.col2
  dsimp only
  rw [scan_answer]

theorem col1_bound (P : SevenDFA α) (w : Word α) (I : Prepared P)
    (R : ReadyTable P) (t : Nat) :
    (testColumn1 P w I R t).2≤t+1 := by
  unfold testColumn1
  dsimp only
  simpa only [List.length_range,Nat.mul_one] using
    (scan_bound (fun a => (Integrated.test1 P I (fun p => readyAt P R p t)
      (P1Index.build P (IndexedMarked.decorate (fun p => readyAt P R p t) 0 w)) t a,1))
      (List.range (t+1)) 1 (fun _ _=>Nat.le_refl _))

theorem col2_bound (P : SevenDFA α) (w : Word α) (I : Prepared P)
    (R : ReadyTable P) (t : Nat) :
    (testColumn2 P w I R t).2≤t+1 := by
  let r := fun p => readyAt P R p t
  let row := MaskScan.first2Row P w r
  let m := MaskScan.accepted P.B row
  let idx := (IndexedMarked.build P.D P.C (IndexedMarked.decorate m 0 w)).1
  change (scan (fun a => (Integrated.test2 P I m idx t a,1)) (List.range (t+1))).2≤t+1
  simpa only [List.length_range,Nat.mul_one] using
    (scan_bound (fun a => (Integrated.test2 P I m idx t a,1))
      (List.range (t+1)) 1 (fun _ _=>Nat.le_refl _))

def match1 [DecidableEq α] (P : SevenDFA α) (w : Word α) : Bool × Nat :=
  let I := prepare P w
  let R := buildReady P w I
  scan (testColumn1 P w I R) (List.range (I.n+1))

def match2 [DecidableEq α] (P : SevenDFA α) (w : Word α) : Bool × Nat :=
  let I := prepare P w
  let R := buildReady P w I
  scan (testColumn2 P w I R) (List.range (I.n+1))

theorem match1_answer [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    (match1 P w).1=Integrated.match1 P w := by
  unfold match1 Integrated.match1
  dsimp only
  rw [scan_answer]
  simp only [col1_answer]

theorem match2_answer [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    (match2 P w).1=Integrated.match2 P w := by
  unfold match2 Integrated.match2
  dsimp only
  rw [scan_answer]
  simp only [col2_answer]

theorem match1_bound [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    (match1 P w).2≤(w.length+1)*(w.length+1) := by
  let I := prepare P w
  let R := buildReady P w I
  change (scan (testColumn1 P w I R) (List.range (w.length+1))).2≤_
  have h := scan_bound (testColumn1 P w I R) (List.range (w.length+1)) (w.length+1)
    (fun t ht=>Nat.le_trans (col1_bound P w I R t) (by have := List.mem_range.mp ht; omega))
  simpa only [List.length_range] using h

theorem match2_bound [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    (match2 P w).2≤(w.length+1)*(w.length+1) := by
  let I := prepare P w
  let R := buildReady P w I
  change (scan (testColumn2 P w I R) (List.range (w.length+1))).2≤_
  have h := scan_bound (testColumn2 P w I R) (List.range (w.length+1)) (w.length+1)
    (fun t ht=>Nat.le_trans (col2_bound P w I R t) (by have := List.mem_range.mp ht; omega))
  simpa only [List.length_range] using h

theorem match1_spec [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    ((match1 P w).1=true ↔ MatchesWithin P.nested1 w 2) ∧
    (match1 P w).2≤(w.length+1)*(w.length+1) := by
  rw [match1_answer,Integrated.match1_correct]
  exact ⟨Iff.rfl,match1_bound P w⟩

theorem match2_spec [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    ((match2 P w).1=true ↔ MatchesWithin P.nested2 w 2) ∧
    (match2 P w).2≤(w.length+1)*(w.length+1) := by
  rw [match2_answer,Integrated.match2_correct]
  exact ⟨Iff.rfl,match2_bound P w⟩

end REWB.EndpointCounts
