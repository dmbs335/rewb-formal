import REWB.MaskedOrderedTree

/-! A sparse bounded-key priority queue for shortening thresholds.
Each occupied key has a persistent list bucket; internal nodes cache the
number of records. Insertion and maximum extraction descend one path.
The universe capacity is computed once and passed down by halving, so
recursive operations do not recompute powers or scan bucket lengths.
This is the queue layer, separate from cluster geometry and repairs.
-/
namespace REWB.MaskedThresholdQueue
variable {α : Type}

structure Entry (α : Type) where
  key : Nat
  value : α
  deriving Repr, DecidableEq

inductive Tree (α : Type) where
  | empty
  | bucket (cached : Nat) (values : List (Entry α))
  | node (cached : Nat) (left right : Tree α)
  deriving Repr

def count : Tree α → Nat
  | .empty => 0
  | .bucket n _ => n
  | .node n _ _ => n

def entries : Tree α → List (Entry α)
  | .empty => []
  | .bucket _ xs => xs
  | .node _ l r => entries l++entries r

def left : Tree α → Tree α
  | .node _ l _ => l
  | _ => .empty

def right : Tree α → Tree α
  | .node _ _ r => r
  | _ => .empty

def bucketValues : Tree α → List (Entry α)
  | .bucket _ xs => xs
  | _ => []

def join (l r : Tree α) : Tree α := .node (count l+count r) l r

def Good : Nat → Nat → Tree α → Prop
  | _,_,.empty => True
  | 0,lo,.bucket n xs => n=xs.length ∧ ∀x,x∈xs → x.key=lo
  | h+1,lo,.node n l r => n=count l+count r ∧ Good h lo l ∧ Good h (lo+2^h) r
  | _,_,_ => False

theorem good_count (h lo : Nat) (t : Tree α) (hg : Good h lo t) : count t=(entries t).length := by
  induction h generalizing lo t with
  | zero =>
    cases t with
    | empty => rfl
    | bucket n xs => exact hg.1
    | node n l r => cases hg
  | succ h ih =>
    cases t with
    | empty => rfl
    | bucket n xs => cases hg
    | node n l r =>
      have hl:=ih lo l hg.2.1
      have hr:=ih (lo+2^h) r hg.2.2
      simp only [count,entries,List.length_append]
      exact hg.1.trans (by rw [hl,hr])

theorem good_bounds (h lo : Nat) (t : Tree α) (hg : Good h lo t) (x : Entry α)
    (hx : x∈entries t) : lo≤x.key ∧ x.key<lo+2^h := by
  induction h generalizing lo t with
  | zero =>
    cases t with
    | empty => cases hx
    | bucket n xs =>
      have he:=hg.2 x hx
      simp only [Nat.pow_zero]
      omega
    | node n l r => cases hg
  | succ h ih =>
    cases t with
    | empty => cases hx
    | bucket n xs => cases hg
    | node n l r =>
      simp only [entries,List.mem_append] at hx
      rw [Nat.pow_succ]
      rcases hx with hx|hx
      · have hh:=ih lo l hg.2.1 hx
        omega
      · have hh:=ih (lo+2^h) r hg.2.2 hx
        omega

theorem good_children (h lo : Nat) (t : Tree α) (hg : Good (h+1) lo t) :
    Good h lo (left t) ∧ Good h (lo+2^h) (right t) ∧
      count t=count (left t)+count (right t) ∧ entries t=entries (left t)++entries (right t) := by
  cases t with
  | empty =>
    exact ⟨by cases h <;> trivial,by cases h <;> trivial,rfl,rfl⟩
  | bucket n xs => cases hg
  | node n l r => exact ⟨hg.2.1,hg.2.2,hg.1,rfl⟩

theorem good_zero (lo : Nat) (t : Tree α) (hg : Good 0 lo t) :
    count t=(bucketValues t).length ∧ entries t=bucketValues t ∧
      ∀x,x∈bucketValues t → x.key=lo := by
  cases t with
  | empty => exact ⟨rfl,rfl,fun _ hx=>False.elim (List.not_mem_nil hx)⟩
  | bucket n xs => exact ⟨hg.1,rfl,hg.2⟩
  | node n l r => cases hg

theorem join_good (h lo : Nat) (l r : Tree α) (hl : Good h lo l)
    (hr : Good h (lo+2^h) r) : Good (h+1) lo (join l r) := ⟨rfl,hl,hr⟩

def insert : Nat → Nat → Nat → Entry α → Tree α → Tree α × Nat
  | 0,_,_,x,t => (.bucket (count t+1) (x::bucketValues t),5)
  | h+1,cap,lo,x,t =>
    let half:=cap/2
    if x.key<lo+half then
      let result:=insert h half lo x (left t)
      (join result.1 (right t),result.2+12)
    else
      let result:=insert h half (lo+half) x (right t)
      (join (left t) result.1,result.2+12)

/-- A complete insertion certificate, including duplicate threshold keys.
Only records, not buckets, contribute to the cached queue size. -/
theorem insert_spec (h cap lo : Nat) (x : Entry α) (t : Tree α)
    (hcap : cap=2^h) (hg : Good h lo t) (hx : lo≤x.key ∧ x.key<lo+cap) :
    Good h lo (insert h cap lo x t).1 ∧
      (entries (insert h cap lo x t).1).Perm (x::entries t) ∧
      count (insert h cap lo x t).1=count t+1 ∧
      (insert h cap lo x t).2≤12*h+5 := by
  induction h generalizing cap lo t with
  | zero =>
    have ht:=good_zero lo t hg
    have he : x.key=lo := by simp only [Nat.pow_zero] at hcap; omega
    simp only [insert]
    refine ⟨⟨by rw [List.length_cons,ht.1],?_⟩,?_,rfl,by omega⟩
    · intro y hy
      rcases List.mem_cons.mp hy with hy|hy
      · subst y; exact he
      · exact ht.2.2 y hy
    · rw [entries,ht.2.1]
  | succ h ih =>
    have hc:=good_children h lo t hg
    have hh : cap/2=2^h := by rw [hcap,Nat.pow_succ,Nat.mul_div_cancel _ (by decide : 0<2)]
    have hp : cap=2^h*2 := by rw [hcap,Nat.pow_succ]
    by_cases hb : x.key<lo+cap/2
    · have hl:=ih (cap/2) lo (left t) hh hc.1 ⟨hx.1,hb⟩
      simp only [insert,if_pos hb]
      refine ⟨join_good h lo _ _ hl.1 hc.2.1,?_,?_,?_⟩
      · change (entries (insert h (cap/2) lo x (left t)).1++entries (right t)).Perm _
        have hm:=hl.2.1.append_right (entries (right t))
        simpa only [List.cons_append,←hc.2.2.2] using hm
      · change count (insert h (cap/2) lo x (left t)).1+count (right t)=count t+1
        rw [hl.2.2.1,hc.2.2.1]
        omega
      · have hw:=hl.2.2.2
        omega
    · have hr:=ih (cap/2) (lo+cap/2) (right t) hh
        (by simpa only [hh] using hc.2.1) ⟨by omega,by omega⟩
      simp only [insert,if_neg hb]
      refine ⟨?_,?_,?_,?_⟩
      · exact join_good h lo _ _ hc.1 (by simpa only [hh] using hr.1)
      · change (entries (left t)++entries (insert h (cap/2) (lo+cap/2) x (right t)).1).Perm _
        have hm:=hr.2.1.append_left (entries (left t))
        have ht:=hm.trans List.perm_middle
        simpa only [←hc.2.2.2] using ht
      · change count (left t)+count (insert h (cap/2) (lo+cap/2) x (right t)).1=count t+1
        rw [hr.2.2.1,hc.2.2.1]
        omega
      · have hw:=hr.2.2.2
        omega

end REWB.MaskedThresholdQueue
