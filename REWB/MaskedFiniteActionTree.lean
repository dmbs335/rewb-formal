import REWB.MaskedFiniteAction

/-! Balanced position trees for finite-action matrix vectors.

Cluster leaders occupy their text positions and other cells can be identity
vectors. Global shortening reindexes the root without visiting positions.
Point replacement first pushes the older map to both old children, so a
newly reset cluster is not subjected to an action predating its creation.

Counters are those of MaskedFiniteAction.Counted plus materialized map
writes and tree-node allocations. The fixed vector dimension k must depend
only on pattern automata, never on text length or period. Cluster geometry,
leaf construction and a suffix-tree traversal remain separate obligations.
-/
namespace REWB.MaskedFiniteAction

inductive Tree (k m : Nat) : Nat→Type where
  | leaf : Table k m→Tree k m 0
  | node {h : Nat} : Table k m→Vector (Fin k) k→Tree k m h→Tree k m h→Tree k m (h+1)

namespace Tree
variable {k m h : Nat}

def cache : {h : Nat}→Tree k m h→Table k m
  | _,.leaf a => a
  | _,.node a _ _ _ => a

/-- Mathematical ordered cells, with every pending map interpreted. This
function is used only in statements/proofs, never during a query. -/
def leaves : {h : Nat}→Tree k m h→List (View k m)
  | _,.leaf a => [a.view]
  | _,.node _ g l r => (leaves l++leaves r).map (View.reindex g.get)

theorem leaves_length (t : Tree k m h) : (leaves t).length=2^h := by
  induction t with
  | leaf a => rfl
  | @node h a g l r il ir =>
    simp only [leaves,List.length_map,List.length_append,il,ir,Nat.pow_succ,Nat.mul_two]

def Good : {h : Nat}→Tree k m h→Prop
  | _,.leaf _ => True
  | _,.node a g l r => Good l ∧ Good r ∧
      a.view=View.reindex g.get (View.mul (cache l).view (cache r).view)

theorem cache_correct (t : Tree k m h) (ht : Good t) :
    (cache t).view=View.product (leaves t) := by
  induction t with
  | leaf a =>
    change a.view=View.mul a.view View.one
    rw [View.mul_one]
  | @node h a g l r il ir =>
    rcases ht with ⟨hl,hr,he⟩
    change a.view=View.product ((leaves l++leaves r).map (View.reindex g.get))
    rw [← View.reindex_product,View.product_append,← il hl,← ir hr]
    exact he

/-- Recolor a whole persistent version without visiting its represented
positions. The old value remains available because all operations are pure. -/
def reindex (g : Vector (Fin k) k) : {h : Nat}→Tree k m h→Tree k m h×Nat
  | _,.leaf a =>
    let rr := Counted.reindex g a
    (.leaf rr.1,rr.2+1)
  | _,.node a old l r =>
    let rr := Counted.reindex g a
    let gg := Counted.compose old g
    (.node rr.1 gg.1 l r,rr.2+gg.2+1)

theorem reindex_cache (g : Vector (Fin k) k) (t : Tree k m h) :
    (cache (reindex g t).1).view=View.reindex g.get (cache t).view := by
  cases t <;> simp only [reindex,cache,Counted.reindex_view]

theorem reindex_leaves (g : Vector (Fin k) k) (t : Tree k m h) :
    leaves (reindex g t).1=(leaves t).map (View.reindex g.get) := by
  cases t with
  | leaf a => simp only [reindex,leaves,List.map_cons,List.map_nil,Counted.reindex_view]
  | node a old l r =>
    simp only [reindex,leaves,List.map_map]
    congr 1
    funext v
    change View.reindex (Counted.compose old g).1.get v=
      View.reindex g.get (View.reindex old.get v)
    rw [View.reindex_comp]
    funext c p q
    simp only [View.reindex,Counted.compose_get]

theorem reindex_good (g : Vector (Fin k) k) (t : Tree k m h) (ht : Good t) :
    Good (reindex g t).1 := by
  cases t with
  | leaf a => trivial
  | node a old l r =>
    rcases ht with ⟨hl,hr,he⟩
    refine ⟨hl,hr,?_⟩
    change (Counted.reindex g a).1.view=
      View.reindex (Counted.compose old g).1.get (View.mul (cache l).view (cache r).view)
    rw [Counted.reindex_view,he,View.reindex_comp]
    funext c p q
    simp only [View.reindex,Counted.compose_get]

def reindexBudget (k m : Nat) : Nat := 2*k+1

theorem reindex_steps (g : Vector (Fin k) k) (t : Tree k m h) :
    (reindex g t).2≤reindexBudget k m := by
  cases t <;> simp only [reindex,Counted.reindex_steps,Counted.compose_steps,reindexBudget] <;> omega

/-- Rebuild one parent after an update. Child caches already contain their
pending maps, so the new parent's map is the identity. -/
def join (l r : Tree k m h) : Tree k m (h+1)×Nat :=
  let cc := Counted.mul (cache l) (cache r)
  (.node cc.1 (Counted.identity k) l r,cc.2+k+1)

theorem join_leaves (l r : Tree k m h) : leaves (join l r).1=leaves l++leaves r := by
  change (leaves l++leaves r).map (View.reindex (Counted.identity k).get)=_
  have hg : (Counted.identity k).get=id := funext Counted.identity_get
  rw [hg]
  have hi : View.reindex (m:=m) (k:=k) id=id := funext View.reindex_id
  rw [hi,List.map_id]

theorem join_good (l r : Tree k m h) (hl : Good l) (hr : Good r) : Good (join l r).1 := by
  refine ⟨hl,hr,?_⟩
  change (Counted.mul (cache l) (cache r)).1.view=
    View.reindex (Counted.identity k).get (View.mul (cache l).view (cache r).view)
  rw [Counted.mul_view]
  have hg : (Counted.identity k).get=id := funext Counted.identity_get
  rw [hg,View.reindex_id]

def joinBudget (k m : Nat) : Nat := k*(m*(m*(m+1)))+k+1

theorem join_steps (l r : Tree k m h) : (join l r).2=joinBudget k m := by
  simp only [join,Counted.mul_steps,joinBudget]

/-- Building the materialized identity and allocating one leaf. -/
def leafBudget (k m : Nat) : Nat := 1+k*m*m

/-- Build from a finite array; missing padding cells are identities. The
identity construction is charged even when a supplied array cell is read. -/
def build (a : Array (Table k m)) : (h : Nat)→Nat→Tree k m h×Nat
  | 0,off => (.leaf (a[off]?.getD Table.one),leafBudget k m)
  | h+1,off =>
    let ll := build a h off
    let rr := build a h (off+2^h)
    let node := join ll.1 rr.1
    (node.1,ll.2+rr.2+node.2)

theorem build_good (a : Array (Table k m)) (h off : Nat) : Good (build a h off).1 := by
  induction h generalizing off with
  | zero => trivial
  | succ h ih => exact join_good _ _ (ih _) (ih _)

theorem build_steps (a : Array (Table k m)) (h off : Nat) :
    (build a h off).2+joinBudget k m=2^h*(joinBudget k m+leafBudget k m) := by
  induction h generalizing off with
  | zero => simp [build,Nat.add_comm]
  | succ h ih =>
    change (build a h off).2+(build a h (off+2^h)).2+
      (join (build a h off).1 (build a h (off+2^h)).1).2+joinBudget k m=_
    rw [join_steps,Nat.pow_succ,Nat.mul_assoc]
    have h1 := ih off
    have h2 := ih (off+2^h)
    have hm : 2*(joinBudget k m+leafBudget k m)=(joinBudget k m+leafBudget k m)+(joinBudget k m+leafBudget k m) := by omega
    rw [hm,Nat.mul_add]
    omega

/-- A lookup-free mathematical description of the built leaf order. -/
def cells (a : Array (Table k m)) (off n : Nat) : List (View k m) :=
  (List.range' off n).map (fun i=>(a[i]?.getD Table.one).view)

theorem build_leaves (a : Array (Table k m)) (h off : Nat) :
    leaves (build a h off).1=cells a off (2^h) := by
  induction h generalizing off with
  | zero => simp [build,leaves,cells,List.range']
  | succ h ih =>
    change leaves (join (build a h off).1 (build a h (off+2^h)).1).1=_
    rw [join_leaves,ih,ih]
    unfold cells
    rw [← List.map_append]
    congr 1
    have hr := List.range'_append (s:=off) (m:=2^h) (n:=2^h) (step:=1)
    simpa [Nat.pow_succ,Nat.mul_two] using hr

/-- Query the first n cells. Only one child is partially visited at each
level; complete prefixes use stored caches. Earlier suffix states are
computed from that prefix itself, never by inverse transitions. -/
def queryPrefix : {h : Nat}→Tree k m h→Nat→Table k m×Nat
  | h,t,n =>
    if n=0 then (Table.one,leafBudget k m) else if 2^h≤n then (cache t,1) else
    match t with
    | .leaf a => (a,1)
    | @Tree.node _ _ d _ g l r =>
      if n≤2^d then
        let part := queryPrefix l n
        let out := Counted.reindex g part.1
        (out.1,part.2+out.2+1)
      else
        let part := queryPrefix r (n-2^d)
        let both := Counted.mul (cache l) part.1
        let out := Counted.reindex g both.1
        (out.1,part.2+both.2+out.2+1)

theorem queryPrefix_correct (t : Tree k m h) (ht : Good t) (n : Nat) :
    (queryPrefix t n).1.view=View.product ((leaves t).take n) := by
  induction t generalizing n with
  | leaf a =>
    by_cases hz : n=0
    · simp [queryPrefix,hz,leaves,View.product,RangeProducts.product,View.ops]
    · have hn : 1≤n := by omega
      simp [queryPrefix,hz,hn,leaves,cache,List.take_of_length_le,View.product,RangeProducts.product,View.ops,View.mul_one]
  | @node h a g l r il ir =>
    rcases ht with ⟨hl,hr,he⟩
    by_cases hz : n=0
    · simp [queryPrefix,hz,leaves,View.product,RangeProducts.product,View.ops]
    · by_cases hn : 2^(h+1)≤n
      · simp only [queryPrefix,hz,if_false,hn,if_true]
        rw [List.take_of_length_le (by rw [leaves_length]; exact hn)]
        exact cache_correct _ ⟨hl,hr,he⟩
      · by_cases hc : n≤2^h
        · simp only [queryPrefix,hz,if_false,hn,hc,if_true,Counted.reindex_view]
          rw [il hl]
          change View.reindex g.get (View.product ((leaves l).take n))=
            View.product (((leaves l++leaves r).map (View.reindex g.get)).take n)
          rw [← List.map_take,List.take_append_of_le_length (by rw [leaves_length]; exact hc),
            ← View.reindex_product]
        · simp only [queryPrefix,hz,if_false,hn,hc,Counted.reindex_view,Counted.mul_view]
          rw [ir hr,cache_correct l hl]
          change View.reindex g.get (View.mul (View.product (leaves l))
            (View.product ((leaves r).take (n-2^h))))=
            View.product (((leaves l++leaves r).map (View.reindex g.get)).take n)
          have hlTake : (leaves l).take n=leaves l :=
            List.take_of_length_le (by rw [leaves_length]; omega)
          rw [← List.map_take,List.take_append_eq_append_take,hlTake,leaves_length,
            ← View.reindex_product,View.product_append]

def queryBudget (k m : Nat) : Nat :=
  leafBudget k m+joinBudget k m+reindexBudget k m+1

theorem queryPrefix_steps (t : Tree k m h) (n : Nat) :
    (queryPrefix t n).2≤(h+1)*queryBudget k m := by
  induction t generalizing n with
  | leaf a =>
    simp only [queryPrefix]
    split
    · unfold queryBudget leafBudget joinBudget reindexBudget; omega
    · split <;> unfold queryBudget leafBudget joinBudget reindexBudget <;> omega
  | @node h a g l r il ir =>
    simp only [queryPrefix]
    split
    · unfold queryBudget leafBudget joinBudget reindexBudget; have : 1≤h+1+1 := by omega
      exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))
    · split
      · unfold queryBudget leafBudget joinBudget reindexBudget; exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))
      · split
        · simp only [Counted.reindex_steps]
          have hh := il n
          have hm : (h+1+1)*queryBudget k m=(h+1)*queryBudget k m+queryBudget k m := by
            rw [Nat.add_mul,Nat.one_mul]
          rw [hm]
          unfold queryBudget leafBudget joinBudget reindexBudget at *
          omega
        · simp only [Counted.reindex_steps,Counted.mul_steps]
          have hh := ir (n-2^h)
          have hm : (h+1+1)*queryBudget k m=(h+1)*queryBudget k m+queryBudget k m := by
            rw [Nat.add_mul,Nat.one_mul]
          rw [hm]
          unfold queryBudget leafBudget joinBudget reindexBudget at *
          omega

/-- Replace one cell, preserving all other persistent positions. Older
maps are applied to old children before the new cell is introduced. -/
def replace : {h : Nat}→Tree k m h→Nat→Table k m→Tree k m h×Nat
  | h,t,i,a =>
    if 2^h≤i then (t,1) else
    match t with
    | .leaf _ => (.leaf a,1)
    | @Tree.node _ _ d _ g l r =>
      let ll := reindex g l
      let rr := reindex g r
      if i<2^d then
        let updated := replace ll.1 i a
        let parent := join updated.1 rr.1
        (parent.1,ll.2+rr.2+updated.2+parent.2+1)
      else
        let updated := replace rr.1 (i-2^d) a
        let parent := join ll.1 updated.1
        (parent.1,ll.2+rr.2+updated.2+parent.2+1)

theorem replace_good (t : Tree k m h) (ht : Good t) (i : Nat) (a : Table k m) :
    Good (replace t i a).1 := by
  induction h generalizing i with
  | zero =>
    cases t
    simp only [replace]
    split
    · exact ht
    · trivial
  | succ h ih =>
    cases t with
    | node old g l r =>
      rcases ht with ⟨hl,hr,he⟩
      simp only [replace]
      split
      · exact ⟨hl,hr,he⟩
      · split
        · exact join_good _ _ (ih _ (reindex_good _ _ hl) _) (reindex_good _ _ hr)
        · exact join_good _ _ (reindex_good _ _ hl) (ih _ (reindex_good _ _ hr) _)

theorem replace_leaves (t : Tree k m h) (i : Nat) (a : Table k m) :
    leaves (replace t i a).1=(leaves t).set i a.view := by
  induction h generalizing i with
  | zero =>
    cases t with
    | leaf old =>
      by_cases hi : 1≤i
      · simp only [replace,Nat.pow_zero,hi,if_true]
        rw [List.set_eq_of_length_le (by rw [leaves_length]; exact hi)]
      · have hz : i=0 := by omega
        subst i
        simp [replace,leaves]
  | succ h ih =>
    cases t with
    | node old g l r =>
      by_cases hi : 2^(h+1)≤i
      · simp only [replace,hi,if_true]
        rw [List.set_eq_of_length_le (by rw [leaves_length]; exact hi)]
      · by_cases hc : i<2^h
        · simp only [replace,hi,if_false,hc,if_true,join_leaves,ih,reindex_leaves]
          change ((leaves l).map (View.reindex g.get)).set i a.view++
              (leaves r).map (View.reindex g.get)=_
          simp only [leaves,List.map_append]
          rw [List.set_append_left i a.view (by rw [List.length_map,leaves_length]; exact hc)]
        · simp only [replace,hi,if_false,hc,join_leaves,ih,reindex_leaves]
          simp only [leaves,List.map_append]
          rw [List.set_append_right i a.view (by rw [List.length_map,leaves_length]; omega),
            List.length_map,leaves_length]

def replaceBudget (k m : Nat) : Nat :=
  2*reindexBudget k m+joinBudget k m+1

theorem replace_steps (t : Tree k m h) (i : Nat) (a : Table k m) :
    (replace t i a).2≤(h+1)*replaceBudget k m := by
  induction h generalizing i with
  | zero =>
    cases t
    simp only [replace]
    split <;> unfold replaceBudget <;> omega
  | succ h ih =>
    cases t with
    | node old g l r =>
      simp only [replace]
      split
      · unfold replaceBudget
        exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))
      · have hl := reindex_steps g l
        have hr := reindex_steps g r
        have hm : (h+1+1)*replaceBudget k m=(h+1)*replaceBudget k m+replaceBudget k m := by
          rw [Nat.add_mul,Nat.one_mul]
        rw [hm]
        split
        · simp only [join_steps]
          have hu := ih (reindex g l).1 i
          unfold replaceBudget at *
          omega
        · simp only [join_steps]
          have hu := ih (reindex g r).1 (i-2^h)
          unfold replaceBudget at *
          omega


end Tree
end REWB.MaskedFiniteAction
