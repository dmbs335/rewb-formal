import REWB.EndpointCounts

/-! Flatten a dyadic cut tree into an array. Routing depends only on the
    length and height, not on the monoid or on the input letters.
    One routing table can be reused across all mask columns. -/
namespace REWB.FlatIndex
open RangeProducts
open REWB.Spec (slice)
variable {M : Type}

inductive Entry (M : Type) where
  | leaf : List M → Entry M
  | cut : CutIndex M → Entry M

def flatten : DyadicIndex.Tree M → List (Entry M)
  | .leaf xs => [.leaf xs]
  | .node row left right => .cut row :: (flatten left ++ flatten right)

theorem flatten_length (o : Ops M) (h : Nat) (xs : List M) :
    (flatten (DyadicIndex.build o h xs).1).length+1=2^(h+1) := by
  induction h generalizing xs with
  | zero => rfl
  | succ h ih =>
    change ((flatten (DyadicIndex.build o h (xs.take (2^h))).1 ++
      flatten (DyadicIndex.build o h (xs.drop (2^h))).1).length+1)+1=2^(h+1+1)
    rw [List.length_append,Nat.pow_succ]
    have ha := ih (xs.take (2^h))
    have hb := ih (xs.drop (2^h))
    omega

structure Route where
  addr : Nat
  lo : Nat
  hi : Nat
  visits : Nat
  deriving Repr

/-- The pre-order address of the first crossing cut, or a leaf.
    The full binary tree shape is independent of the contents. -/
def route : Nat → Nat → Nat → Nat → Route
  | 0, _, l, r => ⟨0,l,r,1⟩
  | h+1, n, l, r =>
    let c := min (2^h) n
    if r≤c then
      let p := route h c l r
      { p with addr := p.addr+1, visits := p.visits+1 }
    else if c≤l then
      let p := route h (n-c) (l-c) (r-c)
      { p with addr := p.addr+2^(h+1), visits := p.visits+1 }
    else ⟨0,l,r,1⟩

theorem route_bound (h n l r : Nat) :
    (route h n l r).addr+1 < 2^(h+1) ∧
      (route h n l r).visits≤h+1 := by
  induction h generalizing n l r with
  | zero => simp [route]
  | succ h ih =>
    let c := min (2^h) n
    let p := if r≤c then
      let q := route h c l r
      {q with addr:=q.addr+1,visits:=q.visits+1}
      else if c≤l then
        let q := route h (n-c) (l-c) (r-c)
        {q with addr:=q.addr+2^(h+1),visits:=q.visits+1}
      else ⟨0,l,r,1⟩
    change p.addr+1<2^(h+1+1) ∧ p.visits≤h+1+1
    rw [Nat.pow_succ]
    dsimp only [p]
    by_cases hx : r≤c
    · rw [if_pos hx]
      have hh := ih c l r
      dsimp only
      omega
    · rw [if_neg hx]
      by_cases hy : c≤l
      · rw [if_pos hy]
        have hh := ih (n-c) (l-c) (r-c)
        dsimp only
        omega
      · rw [if_neg hy]
        have hh := ih c l r
        dsimp only
        omega

private theorem get_left {X : Type} (a b : List X) (i : Nat)
    (hi : i<a.length) : (a++b)[i]?=a[i]? := by
  induction a generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hh : i<xs.length := by simpa using hi
      exact ih i hh

private theorem get_right {X : Type} (a b : List X) (i : Nat) :
    (a++b)[a.length+i]?=b[i]? := by
  induction a with
  | nil => simp only [List.nil_append,List.length_nil,Nat.zero_add]
  | cons x xs ih =>
    have he : (x::xs).length+i = (xs.length+i)+1 := by simp; omega
    rw [he]
    exact ih

def eval (o : Ops M) (entry : Entry M) (l r : Nat) : Option M :=
  match entry with
  | .leaf xs => some (product o (slice xs l r))
  | .cut row => queryCut o row l r

def listQuery (o : Ops M) (entries : List (Entry M)) (p : Route) : Option M :=
  (entries[p.addr]?).bind (fun entry=>eval o entry p.lo p.hi)

theorem listQuery_correct (o : Ops M) (h : Nat) (xs : List M) (l r : Nat) :
    listQuery o (flatten (DyadicIndex.build o h xs).1) (route h xs.length l r) =
      (DyadicIndex.query o (DyadicIndex.build o h xs).1 l r).answer := by
  induction h generalizing xs l r with
  | zero => rfl
  | succ h ih =>
    let x := xs.take (2^h)
    let y := xs.drop (2^h)
    let lx := flatten (DyadicIndex.build o h x).1
    let ly := flatten (DyadicIndex.build o h y).1
    have hx : x.length=min (2^h) xs.length := List.length_take
    have hy : y.length=xs.length-x.length := by
      rw [List.length_drop,hx]
      omega
    have hlen := flatten_length o h x
    change lx.length+1=2^(h+1) at hlen
    have hroute : route (h+1) xs.length l r =
        (if r≤x.length then
          let p := route h x.length l r
          {p with addr := p.addr+1, visits := p.visits+1}
        else if x.length≤l then
          let p := route h y.length (l-x.length) (r-x.length)
          {p with addr := p.addr+2^(h+1), visits := p.visits+1}
        else ⟨0,l,r,1⟩) := by
      simp only [route]
      rw [← hx,← hy]
    rw [hroute]
    change listQuery o (.cut (buildCut o x y).1 :: (lx++ly)) _ =
      (DyadicIndex.query o (.node (buildCut o x y).1
        (DyadicIndex.build o h x).1 (DyadicIndex.build o h y).1) l r).answer
    simp only [DyadicIndex.query]
    change _ = (if r≤x.length then
      (DyadicIndex.query o (DyadicIndex.build o h x).1 l r).bump
      else if x.length≤l then
        (DyadicIndex.query o (DyadicIndex.build o h y).1 (l-x.length) (r-x.length)).bump
      else ⟨queryCut o (buildCut o x y).1 l r,1,1⟩).answer
    by_cases hl : r≤x.length
    · rw [if_pos hl,if_pos hl]
      let p := route h x.length l r
      have hb := (route_bound h x.length l r).1
      have hp : p.addr<lx.length := by change (route h x.length l r).addr<lx.length; omega
      change ((lx++ly)[p.addr]?).bind (fun e=>eval o e p.lo p.hi) = _
      rw [get_left lx ly p.addr hp]
      exact ih x l r
    · rw [if_neg hl,if_neg hl]
      by_cases hr : x.length≤l
      · rw [if_pos hr,if_pos hr]
        let p := route h y.length (l-x.length) (r-x.length)
        have he : p.addr+2^(h+1)=lx.length+p.addr+1 := by omega
        change (((.cut (buildCut o x y).1 :: (lx++ly))[p.addr+2^(h+1)]?).bind
          (fun e=>eval o e p.lo p.hi)) = _
        rw [he]
        change ((lx++ly)[lx.length+p.addr]?).bind (fun e=>eval o e p.lo p.hi) = _
        rw [get_right]
        exact ih y (l-x.length) (r-x.length)
      · rw [if_neg hr,if_neg hr]
        rfl

def build (o : Ops M) (xs : List M) : Array (Entry M) :=
  (flatten (DyadicIndex.buildFor o xs).1).toArray

/-- For the macro blocks only. Computing this shared table takes one
    logarithmic route computation per ordered pair, once per text length. -/
def buildRoutes (n : Nat) : Array (Array Route) :=
  OuterTables.tabulate (n+1) (fun l =>
    OuterTables.tabulate (n+1) (fun r => route (DyadicIndex.heightFor n) n l r))

def lookupRoute (routes : Array (Array Route)) (l r : Nat) : Option Route :=
  (routes[l]?).bind (fun row=>row[r]?)

theorem lookupRoute_correct (n l r : Nat) (hl : l≤n) (hr : r≤n) :
    lookupRoute (buildRoutes n) l r =
      some (route (DyadicIndex.heightFor n) n l r) := by
  unfold lookupRoute buildRoutes
  rw [OuterTables.tabulate_get _ _ l (by omega)]
  change (OuterTables.tabulate (n+1) (fun r=>route (DyadicIndex.heightFor n) n l r))[r]?=_
  rw [OuterTables.tabulate_get _ _ r (by omega)]

def query (o : Ops M) (entries : Array (Entry M))
    (routes : Array (Array Route)) (l r : Nat) : Option M := do
  let p ← lookupRoute routes l r
  let entry ← entries[p.addr]?
  eval o entry p.lo p.hi

theorem query_correct (o : Ops M) (xs : List M) (l r : Nat)
    (hl : l≤r) (hr : r≤xs.length) :
    query o (build o xs) (buildRoutes xs.length) l r =
      some (product o (slice xs l r)) := by
  unfold query
  rw [lookupRoute_correct xs.length l r (by omega) hr]
  let p := route (DyadicIndex.heightFor xs.length) xs.length l r
  change (((flatten (DyadicIndex.buildFor o xs).1).toArray)[p.addr]?).bind
    (fun e=>eval o e p.lo p.hi) = _
  rw [List.getElem?_toArray]
  change listQuery o (flatten (DyadicIndex.build o (DyadicIndex.heightFor xs.length) xs).1)
    (route (DyadicIndex.heightFor xs.length) xs.length l r)=_
  rw [listQuery_correct,DyadicIndex.query_correct o _ xs l r hl hr]

end REWB.FlatIndex
