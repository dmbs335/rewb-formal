import REWB.NestedColumns

/-! Independent exact common-prefix table, used on reversed text for LCS.
    A cell compares one pair of symbols and reuses the adjacent prior cell.
    Counters record equality tests in the executable row construction.
    The full array uses quadratic space; a linear-space suffix index is open. -/
namespace REWB.LCSTable
open REWB.Spec (slice)
open REWB.OuterColumn (Common IsMaxCommon)
variable {α : Type}

def lcp [DecidableEq α] : Word α → Word α → Nat
  | [], _ => 0
  | _::_, [] => 0
  | x::xs, y::ys => if x=y then lcp xs ys+1 else 0

@[simp] theorem lcp_nil_right [DecidableEq α] (x : Word α) : lcp x [] = 0 := by
  cases x <;> rfl

def Agree (x y : Word α) (k : Nat) : Prop :=
  k ≤ x.length ∧ k ≤ y.length ∧ x.take k = y.take k

theorem agree_zero (x y : Word α) : Agree x y 0 := by
  simp [Agree]

theorem agree_succ (x y : α) (xs ys : Word α) (k : Nat) :
    Agree (x::xs) (y::ys) (k+1) ↔ x=y ∧ Agree xs ys k := by
  constructor
  · rintro ⟨hx,hy,he⟩
    have h : x=y ∧ xs.take k = ys.take k := by simpa using he
    exact ⟨h.1,by simpa using hx,by simpa using hy,h.2⟩
  · rintro ⟨rfl,hx,hy,he⟩
    exact ⟨by simpa using hx,by simpa using hy,by simp [he]⟩

theorem lcp_spec [DecidableEq α] (x y : Word α) :
    Agree x y (lcp x y) ∧ ∀ k, Agree x y k → k ≤ lcp x y := by
  induction x generalizing y with
  | nil =>
    refine ⟨agree_zero [] y,?_⟩
    intro k hk
    exact hk.1
  | cons x xs ih =>
    cases y with
    | nil =>
      refine ⟨agree_zero (x::xs) [],?_⟩
      intro k hk
      exact hk.2.1
    | cons y ys =>
      by_cases h : x=y
      · subst y
        rw [lcp,if_pos rfl]
        obtain ⟨ha,hmax⟩ := ih ys
        refine ⟨(agree_succ x x xs ys _).mpr ⟨rfl,ha⟩,?_⟩
        intro k hk
        cases k with
        | zero => omega
        | succ k =>
          have hh := hmax k ((agree_succ x x xs ys k).mp hk).2
          omega
      · rw [lcp,if_neg h]
        refine ⟨agree_zero _ _,?_⟩
        intro k hk
        cases k with
        | zero => omega
        | succ k => exact False.elim (h ((agree_succ x y xs ys k).mp hk).1)

theorem agree_shorten (x y : Word α) (d k : Nat)
    (hd : Agree x y d) (hk : k ≤ d) : Agree x y k := by
  refine ⟨by have := hd.1; omega,by have := hd.2.1; omega,?_⟩
  have he := congrArg (List.take k) hd.2.2
  simpa only [List.take_take,Nat.min_eq_left hk,Nat.min_eq_right hk] using he

/-- Specification of the row for one suffix against all suffixes of y. -/
def rowSpec [DecidableEq α] (x : Word α) : Word α → List Nat
  | [] => [0]
  | y::ys => lcp x (y::ys) :: rowSpec x ys

theorem row_length [DecidableEq α] (x y : Word α) :
    (rowSpec x y).length = y.length+1 := by
  induction y with
  | nil => rfl
  | cons y ys ih =>
    change (rowSpec x ys).length+1=ys.length+1+1
    rw [ih]

theorem row_head [DecidableEq α] (x y : Word α) :
    (rowSpec x y).headD 0 = lcp x y := by
  cases y <;> simp [rowSpec]

theorem row_nil [DecidableEq α] (y : Word α) :
    rowSpec ([] : Word α) y = List.replicate (y.length+1) 0 := by
  induction y with
  | nil => rfl
  | cons y ys ih =>
    change 0 :: rowSpec [] ys = List.replicate (ys.length+1+1) 0
    rw [ih]
    rfl

/-- prev is the previous row with its first cell removed.
    For each y-position the next previous cell is read once. -/
def stepRow [DecidableEq α] (x : α) : Word α → List Nat → List Nat × Nat
  | [], _ => ([0],0)
  | y::ys, prev =>
    let tail := stepRow x ys prev.tail
    ((if x=y then prev.headD 0+1 else 0)::tail.1,tail.2+1)

theorem step_cost [DecidableEq α] (x : α) (y : Word α) (prev : List Nat) :
    (stepRow x y prev).2 = y.length := by
  induction y generalizing prev with
  | nil => rfl
  | cons y ys ih =>
    change (stepRow x ys prev.tail).2+1=ys.length+1
    rw [ih]

theorem step_correct [DecidableEq α] (x : α) (xs y : Word α) :
    (stepRow x y (rowSpec xs y).tail).1 = rowSpec (x::xs) y := by
  induction y with
  | nil => rfl
  | cons y ys ih =>
    change (if x=y then (rowSpec xs ys).headD 0+1 else 0) ::
      (stepRow x ys (rowSpec xs ys).tail).1 =
      lcp (x::xs) (y::ys) :: rowSpec (x::xs) ys
    rw [row_head,ih]
    rfl

def tableSpec [DecidableEq α] : Word α → Word α → List (List Nat)
  | [], y => [rowSpec [] y]
  | x::xs, y => rowSpec (x::xs) y :: tableSpec xs y

theorem table_head [DecidableEq α] (x y : Word α) :
    (tableSpec x y).headD [] = rowSpec x y := by
  cases x <;> rfl

def buildRows [DecidableEq α] : Word α → Word α → List (List Nat) × Nat
  | [], y => ([List.replicate (y.length+1) 0],0)
  | x::xs, y =>
    let prev := buildRows xs y
    let row := stepRow x y (prev.1.headD []).tail
    (row.1::prev.1,row.2+prev.2)

theorem build_correct [DecidableEq α] (x y : Word α) :
    (buildRows x y).1 = tableSpec x y := by
  induction x with
  | nil =>
    change [List.replicate (y.length+1) 0] = [rowSpec [] y]
    rw [row_nil]
  | cons x xs ih =>
    change (stepRow x y ((buildRows xs y).1.headD []).tail).1 ::
      (buildRows xs y).1 = rowSpec (x::xs) y :: tableSpec xs y
    rw [ih,table_head,step_correct]

theorem build_cost [DecidableEq α] (x y : Word α) :
    (buildRows x y).2 = x.length*y.length := by
  induction x with
  | nil => simp [buildRows]
  | cons x xs ih =>
    change (stepRow x y ((buildRows xs y).1.headD []).tail).2 +
      (buildRows xs y).2 = (xs.length+1)*y.length
    rw [step_cost,ih,Nat.add_mul,Nat.one_mul]
    omega

def cells : List (List Nat) → Nat
  | [] => 0
  | r::rs => r.length+cells rs

theorem table_cells [DecidableEq α] (x y : Word α) :
    cells (tableSpec x y) = (x.length+1)*(y.length+1) := by
  induction x with
  | nil =>
    change (rowSpec [] y).length+0 = (0+1)*(y.length+1)
    rw [row_length]
    omega
  | cons x xs ih =>
    change (rowSpec (x::xs) y).length+cells (tableSpec xs y) =
      (xs.length+1+1)*(y.length+1)
    rw [row_length,ih,Nat.add_mul,Nat.one_mul]
    omega

theorem build_cells [DecidableEq α] (x y : Word α) :
    cells (buildRows x y).1 = (x.length+1)*(y.length+1) := by
  rw [build_correct,table_cells]

theorem row_get [DecidableEq α] (x y : Word α) (j : Nat) (hj : j ≤ y.length) :
    (rowSpec x y)[j]? = some (lcp x (y.drop j)) := by
  induction y generalizing j with
  | nil =>
    have h : j=0 := by simpa using hj
    subst j
    simp [rowSpec]
  | cons y ys ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have h : j ≤ ys.length := by simpa using hj
      exact ih j h

theorem table_get [DecidableEq α] (x y : Word α) (i : Nat) (hi : i ≤ x.length) :
    (tableSpec x y)[i]? = some (rowSpec (x.drop i) y) := by
  induction x generalizing i with
  | nil =>
    have h : i=0 := by simpa using hi
    subst i
    rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h : i ≤ xs.length := by simpa using hi
      exact ih i h

def buildTable [DecidableEq α] (x y : Word α) : Array (Array Nat) × Nat :=
  let r := buildRows x y
  ((r.1.map List.toArray).toArray,r.2)

def lookup (idx : Array (Array Nat)) (i j : Nat) : Option Nat :=
  (idx[i]?).bind fun row => row[j]?

theorem lookup_correct [DecidableEq α] (x y : Word α) (i j : Nat)
    (hi : i ≤ x.length) (hj : j ≤ y.length) :
    lookup (buildTable x y).1 i j = some (lcp (x.drop i) (y.drop j)) := by
  unfold lookup buildTable
  simp only [build_correct,List.getElem?_toArray,List.getElem?_map,table_get x y i hi,
    Option.map,Option.bind,row_get (x.drop i) y j hj]

private theorem take_prefix (x y : Word α) :
    (x++y).take x.length = x := by
  induction x with
  | nil => rfl
  | cons x xs ih =>
    change x :: (xs++y).take xs.length = x::xs
    rw [ih]

private theorem drop_prefix (x y : Word α) :
    (x++y).drop x.length = y := by
  induction x with
  | nil => rfl
  | cons x xs ih => exact ih

/-- Reversal turns a prefix end into a suffix start. -/
theorem rev_end (w : Word α) (e : Nat) (he : e ≤ w.length) :
    w.reverse.drop (w.length-e) = (slice w 0 e).reverse := by
  have h := OuterColumn.slice_split w 0 e w.length (by omega) he
  rw [NestedColumns.slice_full] at h
  have hr : w.reverse = (slice w e w.length).reverse ++ (slice w 0 e).reverse := by
    simpa only [List.reverse_append] using congrArg List.reverse h
  have hlen : (slice w e w.length).reverse.length = w.length-e := by
    rw [List.length_reverse,OuterColumn.slice_length w e w.length he (by omega)]
  calc
    w.reverse.drop (w.length-e) =
        ((slice w e w.length).reverse ++ (slice w 0 e).reverse).drop
          ((slice w e w.length).reverse.length) := by
      exact congrArg (fun v => v.drop (w.length-e)) hr |>.trans
        (by rw [hlen])
    _ = _ := drop_prefix _ _

theorem rev_end_take (w : Word α) (e k : Nat) (he : e ≤ w.length) (hk : k ≤ e) :
    (w.reverse.drop (w.length-e)).take k = (slice w (e-k) e).reverse := by
  rw [rev_end w e he]
  have h := OuterColumn.slice_split w 0 (e-k) e (by omega) (by omega)
  have hr : (slice w 0 e).reverse =
      (slice w (e-k) e).reverse ++ (slice w 0 (e-k)).reverse := by
    simpa only [List.reverse_append] using congrArg List.reverse h
  have hlen : (slice w (e-k) e).reverse.length = k := by
    rw [List.length_reverse,OuterColumn.slice_length w (e-k) e (by omega) he]
    omega
  calc
    (slice w 0 e).reverse.take k =
      ((slice w (e-k) e).reverse ++ (slice w 0 (e-k)).reverse).take
        ((slice w (e-k) e).reverse.length) := by rw [hr,hlen]
    _ = _ := take_prefix _ _

theorem rev_end_length (w : Word α) (e : Nat) (he : e ≤ w.length) :
    (w.reverse.drop (w.length-e)).length = e := by
  rw [List.length_drop,List.length_reverse]
  omega

theorem common_iff_agree (w : Word α) (e f k : Nat)
    (hef : e ≤ f) (hf : f ≤ w.length) :
    Common w e f k ↔
      k ≤ f-e ∧ Agree (w.reverse.drop (w.length-e)) (w.reverse.drop (w.length-f)) k := by
  constructor
  · rintro ⟨hk,hn,he⟩
    refine ⟨hn,?_,?_,?_⟩
    · rw [rev_end_length w e (by omega)]; exact hk
    · rw [rev_end_length w f hf]; omega
    · rw [rev_end_take w e k (by omega) hk,rev_end_take w f k hf (by omega),he]
  · rintro ⟨hn,hke,hkf,he⟩
    rw [rev_end_length w e (by omega)] at hke
    rw [rev_end_length w f hf] at hkf
    rw [rev_end_take w e k (by omega) hke,rev_end_take w f k hf hkf] at he
    refine ⟨hke,hn,?_⟩
    simpa only [List.reverse_reverse] using congrArg List.reverse he

def clipped [DecidableEq α] (w : Word α) (e f : Nat) : Nat :=
  min (lcp (w.reverse.drop (w.length-e)) (w.reverse.drop (w.length-f))) (f-e)

theorem clipped_isMax [DecidableEq α] (w : Word α) (e f : Nat)
    (hef : e ≤ f) (hf : f ≤ w.length) :
    IsMaxCommon w e f (clipped w e f) := by
  let x := w.reverse.drop (w.length-e)
  let y := w.reverse.drop (w.length-f)
  have hs := lcp_spec x y
  constructor
  · apply (common_iff_agree w e f _ hef hf).mpr
    change min (lcp x y) (f-e) ≤ f-e ∧ Agree x y (min (lcp x y) (f-e))
    exact ⟨Nat.min_le_right _ _,agree_shorten x y _ _ hs.1 (Nat.min_le_left _ _)⟩
  · intro k hk
    have hh := (common_iff_agree w e f k hef hf).mp hk
    have h1 := hs.2 k hh.2
    unfold clipped
    exact Nat.le_min.mpr ⟨h1,hh.1⟩

def buildLCS [DecidableEq α] (w : Word α) : Array (Array Nat) × Nat :=
  buildTable w.reverse w.reverse

def commonAt (idx : Array (Array Nat)) (n e f : Nat) : Option Nat :=
  (lookup idx (n-e) (n-f)).map fun d => min d (f-e)

theorem commonAt_correct [DecidableEq α] (w : Word α) (e f : Nat)
    (hef : e ≤ f) (hf : f ≤ w.length) :
    commonAt (buildLCS w).1 w.length e f =
      some (OuterColumn.maxCommon w e f e) := by
  have he : w.length-e ≤ w.reverse.length := by rw [List.length_reverse]; omega
  have hf' : w.length-f ≤ w.reverse.length := by rw [List.length_reverse]; omega
  unfold commonAt buildLCS
  rw [lookup_correct _ _ _ _ he hf']
  change some (clipped w e f) = some (OuterColumn.maxCommon w e f e)
  have h1 := clipped_isMax w e f hef hf
  have h2 := OuterColumn.maxCommon_isMax w e f
  exact congrArg some (Nat.le_antisymm (h2.2 _ h1.1) (h1.2 _ h2.1))

theorem lcs_comparisons [DecidableEq α] (w : Word α) :
    (buildLCS w).2 = w.length*w.length := by
  change (buildRows w.reverse w.reverse).2 = _
  rw [build_cost,List.length_reverse]

end REWB.LCSTable
