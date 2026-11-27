import REWB.CachedPhase

/-! Materialized equality tests for short factors of a period block.
    Each pair of starting phases is scanned once, recording equality of
    every prefix of length at most q. Construction makes q^3 character
    comparisons. A query uses three array reads and scans no characters.
    The counter counts character comparisons, not all machine operations. -/
namespace REWB.PhaseEqualityCache
open REWB.Periodic REWB.PhaseSolver REWB.AffineProjection
variable {α : Type} [DecidableEq α]

abbrev Table := Array (Array (Array Bool))

/-- The accumulator records equality before the next character pair. -/
def scan (s : Nat→α) (a c : Nat) (same : Bool) : Nat→List Bool×Nat
  | 0 => ([same],0)
  | k+1 =>
    let hit := decide (s a=s c)
    let rest := scan s (a+1) (c+1) (same && hit) k
    (same::rest.1,rest.2+1)

theorem scan_cost (s : Nat→α) (a c : Nat) (same : Bool) (k : Nat) :
    (scan s a c same k).2=k := by
  induction k generalizing a c same with
  | zero => rfl
  | succ k ih =>
    change (scan s (a+1) (c+1) (same && decide (s a=s c)) k).2+1=k+1
    rw [ih]

theorem scan_length (s : Nat→α) (a c : Nat) (same : Bool) (k : Nat) :
    (scan s a c same k).1.length=k+1 := by
  induction k generalizing a c same with
  | zero => rfl
  | succ k ih =>
    change (scan s (a+1) (c+1) (same && decide (s a=s c)) k).1.length+1=k+1+1
    rw [ih]

theorem scan_get (s : Nat→α) (a c : Nat) (same : Bool) (k r : Nat)
    (hr : r≤k) :
    (scan s a c same k).1[r]? =
      some (same && decide (segment s a r=segment s c r)) := by
  induction r generalizing a c same k with
  | zero =>
    cases k <;> simp [scan,segment]
  | succ r ih =>
    cases k with
    | zero => omega
    | succ k =>
      change (scan s (a+1) (c+1) (same && decide (s a=s c)) k).1[r]?=_
      rw [ih _ _ _ _ (by omega)]
      simp only [segment,List.cons.injEq]
      by_cases h1 : s a=s c <;>
        by_cases h2 : segment s (a+1) r=segment s (c+1) r <;> simp [h1,h2]

def buildRow (s : Nat→α) (q a : Nat) : Array (Array Bool)×Nat :=
  let rows := PeriodicCache.countedMap
    (fun c=>let row := scan s a c true q; (row.1.toArray,row.2)) (List.range q)
  (rows.1.toArray,rows.2)

def build (s : Nat→α) (q : Nat) : Table×Nat :=
  let rows := PeriodicCache.countedMap (buildRow s q) (List.range q)
  (rows.1.toArray,rows.2)

theorem buildRow_cost (s : Nat→α) (q a : Nat) :
    (buildRow s q a).2=q*q := by
  unfold buildRow
  rw [PeriodicCache.countedMap_cost _ _ q]
  · rw [List.length_range]
  · intro c _
    exact scan_cost s a c true q

theorem build_cost (s : Nat→α) (q : Nat) :
    (build s q).2=q^3 := by
  unfold build
  rw [PeriodicCache.countedMap_cost _ _ (q*q)]
  · simp [Nat.pow_succ,Nat.mul_assoc]
  · intro a _
    exact buildRow_cost s q a

def lookup (T : Table) (a c r : Nat) : Option Bool := do
  let row ← T[a]?
  let pair ← row[c]?
  pair[r]?

theorem lookup_correct (s : Nat→α) (q a c r : Nat)
    (ha : a<q) (hc : c<q) (hr : r≤q) :
    lookup (build s q).1 a c r=some (decide (segment s a r=segment s c r)) := by
  unfold lookup build
  simp only [List.getElem?_toArray,PeriodicCache.countedMap_values,List.getElem?_map,
    List.getElem?_range,ha,if_true,Option.map]
  change ((buildRow s q a).1[c]?).bind (fun pair=>pair[r]?)=_
  unfold buildRow
  simp only [List.getElem?_toArray,PeriodicCache.countedMap_values,List.getElem?_map,
    List.getElem?_range,hc,if_true,Option.map]
  change ((scan s a c true q).1.toArray)[r]?=_
  rw [List.getElem?_toArray,scan_get s a c true q r hr]
  simp

def equalAt (T : Table) (a c r : Nat) : Bool := (lookup T a c r).getD false

theorem equalAt_correct (s : Nat→α) (q a c r : Nat)
    (ha : a<q) (hc : c<q) (hr : r≤q) :
    equalAt (build s q).1 a c r=decide (segment s a r=segment s c r) := by
  unfold equalAt
  rw [lookup_correct s q a c r ha hc hr]
  rfl

/-- Out-of-bounds reads stop early; the count never exceeds three. -/
def countedLookup (T : Table) (a c r : Nat) : Option Bool×Nat :=
  match T[a]? with
  | none => (none,1)
  | some row =>
    match row[c]? with
    | none => (none,2)
    | some pair => (pair[r]?,3)

theorem countedLookup_correct (T : Table) (a c r : Nat) :
    (countedLookup T a c r).1=lookup T a c r := by
  unfold countedLookup lookup
  cases T[a]? with
  | none => rfl
  | some row =>
    change (match row[c]? with | none => (none,2) | some pair => (pair[r]?,3)).1=
      (row[c]?).bind (fun pair=>pair[r]?)
    cases row[c]? <;> rfl

theorem countedLookup_cost (T : Table) (a c r : Nat) :
    (countedLookup T a c r).2≤3 := by
  unfold countedLookup
  cases T[a]? with
  | none => simp
  | some row =>
    change (match row[c]? with | none => (none,2) | some pair => (pair[r]?,3)).2≤3
    cases row[c]? <;> simp

def equalityCore (q : Nat) (T : Table) (a b c d : Endpoint) : Formula :=
  if tailLen q a b=tailLen q c d then
    if a.phase=c.phase then eq (countExpr a b) (countExpr c d)
    else if equalAt T a.phase c.phase (tailLen q a b) then
      both (eq (countExpr a b) (.lit 0)) (eq (countExpr c d) (.lit 0))
    else []
  else []

theorem equalityCore_eq (q : Nat) (s : Nat→α) (a b c d : Endpoint)
    (ha : a.phase<q) (hb : b.phase<q) (hc : c.phase<q) :
    equalityCore q (build s q).1 a b c d=PhaseSolver.equalityCore q s a b c d := by
  unfold equalityCore PhaseSolver.equalityCore
  by_cases ht : tailLen q a b=tailLen q c d
  · rw [if_pos ht,if_pos ht]
    rw [equalAt_correct s q a.phase c.phase (tailLen q a b) ha hc
      (Nat.le_of_lt (CachedPhase.tail_lt q a b ha hb))]
    simp only [← ht,decide_eq_true_eq]
  · rw [if_neg ht,if_neg ht]

def countedCore (q : Nat) (T : Table) (a b c d : Endpoint) : Formula×Nat :=
  if tailLen q a b=tailLen q c d then
    if a.phase=c.phase then (eq (countExpr a b) (countExpr c d),0)
    else
      let test := countedLookup T a.phase c.phase (tailLen q a b)
      (if test.1.getD false then
        both (eq (countExpr a b) (.lit 0)) (eq (countExpr c d) (.lit 0)) else [],test.2)
  else ([],0)

theorem countedCore_correct (q : Nat) (T : Table) (a b c d : Endpoint) :
    (countedCore q T a b c d).1=equalityCore q T a b c d := by
  unfold countedCore equalityCore
  split
  · split
    · rfl
    · dsimp only
      rw [countedLookup_correct]
      rfl
  · rfl

theorem countedCore_cost (q : Nat) (T : Table) (a b c d : Endpoint) :
    (countedCore q T a b c d).2≤3 := by
  unfold countedCore
  split
  · split
    · simp
    · exact countedLookup_cost T a.phase c.phase (tailLen q a b)
  · decide

def equalFormula (q n : Nat) (T : Table) (a b c d : Endpoint) : Formula :=
  both (both (orderFormula q n a b) (orderFormula q n c d))
    (both (orderFormula q n a c) (equalityCore q T a b c d))

def countedFormula (q n : Nat) (T : Table) (a b c d : Endpoint) : Formula×Nat :=
  let core := countedCore q T a b c d
  (both (both (orderFormula q n a b) (orderFormula q n c d))
    (both (orderFormula q n a c) core.1),core.2)

theorem countedFormula_correct (q n : Nat) (T : Table) (a b c d : Endpoint) :
    (countedFormula q n T a b c d).1=equalFormula q n T a b c d := by
  unfold countedFormula equalFormula
  dsimp only
  rw [countedCore_correct]

theorem countedFormula_cost (q n : Nat) (T : Table) (a b c d : Endpoint) :
    (countedFormula q n T a b c d).2≤3 := countedCore_cost q T a b c d

/-- Invalid phases are rejected by endpoint bounds before their cached
    comparison can affect the formula. The equality holds for all inputs. -/
theorem equalFormula_eq (q n : Nat) (s : Nat→α) (a b c d : Endpoint) :
    equalFormula q n (build s q).1 a b c d=PhaseSolver.equalFormula q n s a b c d := by
  unfold equalFormula PhaseSolver.equalFormula
  by_cases ha : a.phase<q
  · by_cases hb : b.phase<q
    · by_cases hc : c.phase<q
      · rw [equalityCore_eq q s a b c d ha hb hc]
      · rw [CachedPhase.order_empty_left q n c d hc,
          CachedPhase.both_nil_right,CachedPhase.both_nil_left,CachedPhase.both_nil_left]
    · rw [CachedPhase.order_empty_right q n a b hb,
        CachedPhase.both_nil_left,CachedPhase.both_nil_left,CachedPhase.both_nil_left]
  · rw [CachedPhase.order_empty_left q n a b ha,
      CachedPhase.both_nil_left,CachedPhase.both_nil_left,CachedPhase.both_nil_left]

end REWB.PhaseEqualityCache
