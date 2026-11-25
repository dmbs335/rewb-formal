import REWB.MaskedFiniteActionTree
import REWB.DyadicIndex

/-! Ordered interval products in a persistent finite-action tree.

The query visits only the two boundary paths.  Pending noninjective maps
act on the returned summary, including at a range crossing a split.  No
inverse or cancellation of prefix transformations is used.
-/
namespace REWB.MaskedFiniteAction.Tree
open REWB.Spec (slice)
variable {k m h : Nat}

def querySuffix : {h : Nat}→Tree k m h→Nat→Table k m×Nat
  | h,t,n =>
    if n=0 then (cache t,1) else if 2^h≤n then (Table.one,leafBudget k m) else
    match t with
    | .leaf a => (a,1)
    | @Tree.node _ _ d _ g l r =>
      if n≤2^d then
        let part := querySuffix l n
        let both := Counted.mul part.1 (cache r)
        let out := Counted.reindex g both.1
        (out.1,part.2+both.2+out.2+1)
      else
        let part := querySuffix r (n-2^d)
        let out := Counted.reindex g part.1
        (out.1,part.2+out.2+1)

theorem querySuffix_correct (t : Tree k m h) (ht : Good t) (n : Nat) :
    (querySuffix t n).1.view=View.product ((leaves t).drop n) := by
  induction t generalizing n with
  | leaf a =>
    by_cases hz : n=0
    · simp only [querySuffix,hz,if_true,cache,leaves,List.drop_zero]
      change a.view=View.mul a.view View.one
      rw [View.mul_one]
    · have hn : 1≤n := by omega
      simp only [querySuffix,hz,if_false,Nat.pow_zero,hn,if_true,Table.view_one]
      rw [List.drop_eq_nil_of_le (by rw [leaves_length]; exact hn)]
      rfl
  | @node h a g l r il ir =>
    rcases ht with ⟨hl,hr,he⟩
    by_cases hz : n=0
    · simp only [querySuffix,hz,if_true,List.drop_zero]
      exact cache_correct _ ⟨hl,hr,he⟩
    · by_cases hn : 2^(h+1)≤n
      · simp only [querySuffix,hz,if_false,hn,if_true,Table.view_one]
        rw [List.drop_eq_nil_of_le (by rw [leaves_length]; exact hn)]
        rfl
      · by_cases hc : n≤2^h
        · simp only [querySuffix,hz,if_false,hn,hc,if_true,Counted.reindex_view,Counted.mul_view]
          rw [il hl,cache_correct r hr]
          change View.reindex g.get (View.mul (View.product ((leaves l).drop n))
            (View.product (leaves r)))=View.product
              (((leaves l++leaves r).map (View.reindex g.get)).drop n)
          rw [← List.map_drop,List.drop_append_of_le_length (by rw [leaves_length]; exact hc),
            ← View.reindex_product,View.product_append]
        · simp only [querySuffix,hz,if_false,hn,hc,Counted.reindex_view]
          rw [ir hr]
          change View.reindex g.get (View.product ((leaves r).drop (n-2^h)))=
            View.product (((leaves l++leaves r).map (View.reindex g.get)).drop n)
          have hdrop : (leaves l).drop n=[] :=
            List.drop_eq_nil_of_le (by rw [leaves_length]; omega)
          rw [← List.map_drop,List.drop_append_eq_append_drop,hdrop,List.nil_append,
            leaves_length,← View.reindex_product]

theorem querySuffix_steps (t : Tree k m h) (n : Nat) :
    (querySuffix t n).2≤(h+1)*queryBudget k m := by
  induction t generalizing n with
  | leaf a =>
    simp only [querySuffix]
    split
    · unfold queryBudget leafBudget joinBudget reindexBudget; omega
    · split <;> unfold queryBudget leafBudget joinBudget reindexBudget <;> omega
  | @node h a g l r il ir =>
    simp only [querySuffix]
    split
    · unfold queryBudget leafBudget joinBudget reindexBudget
      exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))
    · split
      · unfold queryBudget leafBudget joinBudget reindexBudget
        exact Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))
      · split
        · simp only [Counted.reindex_steps,Counted.mul_steps]
          have hh := il n
          rw [show (h+1+1)*queryBudget k m=(h+1)*queryBudget k m+queryBudget k m by
            rw [Nat.add_mul,Nat.one_mul]]
          unfold queryBudget leafBudget joinBudget reindexBudget at *
          omega
        · simp only [Counted.reindex_steps]
          have hh := ir (n-2^h)
          rw [show (h+1+1)*queryBudget k m=(h+1)*queryBudget k m+queryBudget k m by
            rw [Nat.add_mul,Nat.one_mul]]
          unfold queryBudget leafBudget joinBudget reindexBudget at *
          omega

def queryRange : {h : Nat}→Tree k m h→Nat→Nat→Table k m×Nat
  | h,t,lo,hi =>
    if hi≤lo then (Table.one,leafBudget k m)
    else if lo=0 then queryPrefix t hi
    else if 2^h≤hi then querySuffix t lo
    else match t with
    | .leaf a => (a,1)
    | @Tree.node _ _ d _ g l r =>
      if hi≤2^d then
        let part := queryRange l lo hi
        let out := Counted.reindex g part.1
        (out.1,part.2+out.2+1)
      else if 2^d≤lo then
        let part := queryRange r (lo-2^d) (hi-2^d)
        let out := Counted.reindex g part.1
        (out.1,part.2+out.2+1)
      else
        let left := querySuffix l lo
        let right := queryPrefix r (hi-2^d)
        let both := Counted.mul left.1 right.1
        let out := Counted.reindex g both.1
        (out.1,left.2+right.2+both.2+out.2+1)

private theorem slice_map {X Y : Type} (f : X→Y) (xs : List X) (lo hi : Nat) :
    slice (xs.map f) lo hi=(slice xs lo hi).map f := by
  simp only [slice,List.map_drop,List.map_take]

theorem queryRange_correct (t : Tree k m h) (ht : Good t) (lo hi : Nat) :
    (queryRange t lo hi).1.view=View.product (slice (leaves t) lo hi) := by
  induction t generalizing lo hi with
  | leaf a =>
    by_cases he : hi≤lo
    · simp only [queryRange,he,if_true,Table.view_one,slice,Nat.sub_eq_zero_of_le he,List.take_zero]
      rfl
    · by_cases hz : lo=0
      · have hnz : ¬hi≤0 := by omega
        simp only [queryRange,hz,hnz,if_false,if_true]
        simpa only [slice,List.drop_zero,Nat.sub_zero] using queryPrefix_correct (.leaf a) ht hi
      · have hc : 2^0≤hi := by simp only [Nat.pow_zero]; omega
        simp only [queryRange,he,if_false,hz,hc,if_true]
        rw [querySuffix_correct _ ht]
        unfold slice
        rw [List.take_of_length_le (by rw [List.length_drop,leaves_length]; simp only [Nat.pow_zero]; omega)]
  | @node h a g l r il ir =>
    rcases ht with ⟨hl,hr,hcache⟩
    by_cases he : hi≤lo
    · simp only [queryRange,he,if_true,Table.view_one,slice,Nat.sub_eq_zero_of_le he,List.take_zero]
      rfl
    · by_cases hz : lo=0
      · have hnz : ¬hi≤0 := by omega
        simp only [queryRange,hz,hnz,if_false,if_true]
        simpa only [slice,List.drop_zero,Nat.sub_zero] using queryPrefix_correct
          (.node a g l r) ⟨hl,hr,hcache⟩ hi
      · by_cases hc : 2^(h+1)≤hi
        · simp only [queryRange,he,if_false,hz,hc,if_true]
          rw [querySuffix_correct (.node a g l r) ⟨hl,hr,hcache⟩ lo]
          unfold slice
          rw [List.take_of_length_le (by rw [List.length_drop,leaves_length]; omega)]
        · by_cases ha : hi≤2^h
          · simp only [queryRange,he,if_false,hz,hc,ha,if_true,Counted.reindex_view]
            rw [il hl]
            change View.reindex g.get (View.product (slice (leaves l) lo hi))=
              View.product (slice ((leaves l++leaves r).map (View.reindex g.get)) lo hi)
            rw [slice_map,DyadicIndex.slice_left _ _ lo hi (by omega) (by rw [leaves_length]; exact ha),
              ← View.reindex_product]
          · by_cases hb : 2^h≤lo
            · simp only [queryRange,he,if_false,hz,hc,ha,hb,if_true,Counted.reindex_view]
              rw [ir hr]
              change View.reindex g.get (View.product (slice (leaves r) (lo-2^h) (hi-2^h)))=
                View.product (slice ((leaves l++leaves r).map (View.reindex g.get)) lo hi)
              rw [slice_map,DyadicIndex.slice_right _ _ lo hi (by rw [leaves_length]; exact hb) (by omega),
                leaves_length,← View.reindex_product]
            · simp only [queryRange,he,if_false,hz,hc,ha,hb,Counted.reindex_view,Counted.mul_view]
              rw [querySuffix_correct _ hl,queryPrefix_correct _ hr]
              change View.reindex g.get (View.mul (View.product ((leaves l).drop lo))
                  (View.product ((leaves r).take (hi-2^h))))=
                View.product (slice ((leaves l++leaves r).map (View.reindex g.get)) lo hi)
              rw [slice_map,RangeProducts.crossing_slice _ _ lo hi
                (by rw [leaves_length]; omega) (by rw [leaves_length]; omega),
                leaves_length,← View.reindex_product,View.product_append]

theorem queryRange_steps (t : Tree k m h) (lo hi : Nat) :
    (queryRange t lo hi).2≤2*(h+1)*queryBudget k m := by
  induction t generalizing lo hi with
  | leaf a =>
    simp only [queryRange]
    split
    · unfold queryBudget leafBudget joinBudget reindexBudget; omega
    · split
      · have hh := queryPrefix_steps (.leaf a : Tree k m 0) hi
        omega
      · split
        · have hh := querySuffix_steps (.leaf a : Tree k m 0) lo
          omega
        · unfold queryBudget leafBudget joinBudget reindexBudget; omega
  | @node h a g l r il ir =>
    simp only [queryRange]
    split
    · have : 0<2*(h+1+1) := by omega
      exact Nat.le_trans (by unfold queryBudget; omega) (Nat.le_mul_of_pos_left _ this)
    · split
      · have hh := queryPrefix_steps (.node a g l r) hi
        rw [Nat.mul_assoc,Nat.two_mul]
        omega
      · split
        · have hh := querySuffix_steps (.node a g l r) lo
          rw [Nat.mul_assoc,Nat.two_mul]
          omega
        · have hm : 2*(h+1+1)*queryBudget k m=2*(h+1)*queryBudget k m+2*queryBudget k m := by
            rw [Nat.mul_add,Nat.mul_one,Nat.add_mul]
          rw [hm]
          split
          · simp only [Counted.reindex_steps]
            have hh := il lo hi
            unfold queryBudget leafBudget joinBudget reindexBudget at *
            omega
          · split
            · simp only [Counted.reindex_steps]
              have hh := ir (lo-2^h) (hi-2^h)
              unfold queryBudget leafBudget joinBudget reindexBudget at *
              omega
            · simp only [Counted.reindex_steps,Counted.mul_steps]
              have hh := querySuffix_steps l lo
              have hj := queryPrefix_steps r (hi-2^h)
              rw [show 2*(h+1)*queryBudget k m=(h+1)*queryBudget k m+(h+1)*queryBudget k m by
                rw [Nat.mul_assoc,Nat.two_mul]]
              unfold queryBudget leafBudget joinBudget reindexBudget at *
              omega

end REWB.MaskedFiniteAction.Tree
