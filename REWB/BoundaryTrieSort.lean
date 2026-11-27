import REWB.CountedSort

/-! A measured stable merge sort for comparators that return their own
work. Each comparison is evaluated once. The additional two merge slots
charge the two list-cell operations of the tail implementation (cons to
the reversed accumulator, then transfer to the output). Length, splitting,
and scalar setup use the existing measured CountedSort operations.
No key contents are inspected by the sorting code itself. -/
namespace REWB.BoundaryTrie.Sort
variable {α : Type}

def order (cmp : α→α→Bool×Nat) (a b : α) : Bool := (cmp a b).1

def merge (cmp : α→α→Bool×Nat) : List α→List α→List α×Nat
  | [],ys => (ys,0)
  | xs,[] => (xs,0)
  | a::as,b::bs =>
    let c:=cmp a b
    if c.1 then
      let r:=merge cmp as (b::bs)
      (a::r.1,r.2+c.2+2)
    else
      let r:=merge cmp (a::as) bs
      (b::r.1,r.2+c.2+2)

theorem merge_counted_value (cmp : α→α→Bool×Nat) (xs ys : List α) :
    (merge cmp xs ys).1=(CountedSort.merge (order cmp) xs ys).1 := by
  induction xs generalizing ys with
  | nil => simp [merge,CountedSort.merge]
  | cons a as ih =>
    induction ys with
    | nil => simp [merge,CountedSort.merge]
    | cons b bs ih' =>
      simp only [merge,CountedSort.merge,order]
      split
      · rw [ih]
      · rw [ih']

theorem merge_value (cmp : α→α→Bool×Nat) (xs ys : List α) :
    (merge cmp xs ys).1=List.merge xs ys (order cmp) := by
  rw [merge_counted_value,CountedSort.merge_value]

theorem merge_steps_scale (cmp : α→α→Bool×Nat) (C : Nat)
    (hc : ∀ a b,(cmp a b).2≤C) (xs ys : List α) :
    (merge cmp xs ys).2≤(C+1)*(CountedSort.merge (order cmp) xs ys).2 := by
  induction xs generalizing ys with
  | nil => simp [merge,CountedSort.merge]
  | cons a as ih =>
    induction ys with
    | nil => simp [merge,CountedSort.merge]
    | cons b bs ih' =>
      have hab:=hc a b
      simp only [merge,CountedSort.merge,order]
      split
      · have hh:=ih (b::bs)
        simp only [Nat.mul_add]
        omega
      · simp only [Nat.mul_add]
        omega

theorem merge_steps (cmp : α→α→Bool×Nat) (C : Nat)
    (hc : ∀ a b,(cmp a b).2≤C) (xs ys : List α) :
    (merge cmp xs ys).2≤(C+1)*(2*(xs.length+ys.length)) :=
  Nat.le_trans (merge_steps_scale cmp C hc xs ys)
    (Nat.mul_le_mul_left (C+1) (CountedSort.merge_steps (order cmp) xs ys))

def mergeTR.go (cmp : α→α→Bool×Nat) : List α→List α→List α→Nat→List α×Nat
  | [],ys,acc,work => (acc.reverseAux ys,work)
  | xs,[],acc,work => (acc.reverseAux xs,work)
  | a::as,b::bs,acc,work =>
    let c:=cmp a b
    if c.1 then go cmp as (b::bs) (a::acc) (work+c.2+2)
    else go cmp (a::as) bs (b::acc) (work+c.2+2)

theorem mergeTR.go_eq (cmp : α→α→Bool×Nat) (xs ys acc : List α) (work : Nat) :
    go cmp xs ys acc work=
      (acc.reverse++(merge cmp xs ys).1,work+(merge cmp xs ys).2) := by
  induction xs generalizing ys acc work with
  | nil => simp [go,merge,List.reverseAux_eq]
  | cons a as ih =>
    induction ys generalizing acc work with
    | nil => simp [go,merge,List.reverseAux_eq]
    | cons b bs ih' =>
      simp only [go,merge]
      split
      · rw [ih]
        simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
        congr 1
        omega
      · rw [ih']
        simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
        congr 1
        omega

def mergeTR (cmp : α→α→Bool×Nat) (xs ys : List α) : List α×Nat :=
  mergeTR.go cmp xs ys [] 0

@[csimp] theorem merge_eq_mergeTR : @merge=@mergeTR := by
  funext α cmp xs ys
  simp only [mergeTR,mergeTR.go_eq,List.reverse_nil,List.nil_append,Nat.zero_add]

def sortFuel (cmp : α→α→Bool×Nat) : Nat→List α→List α×Nat
  | 0,xs => (xs,0)
  | _+1,[] => ([],0)
  | _+1,[a] => ([a],0)
  | h+1,a::b::xs =>
    let ln:=CountedSort.length (a::b::xs)
    let p:=CountedSort.splitAt ((ln.1+1)/2) (a::b::xs)
    let l:=sortFuel cmp h p.1.1
    let r:=sortFuel cmp h p.1.2
    let m:=merge cmp l.1 r.1
    (m.1,ln.2+p.2+l.2+r.2+m.2+3)

theorem sortFuel_counted_value (cmp : α→α→Bool×Nat) (h : Nat) (xs : List α) :
    (sortFuel cmp h xs).1=(CountedSort.sortFuel (order cmp) h xs).1 := by
  induction h generalizing xs with
  | zero => rfl
  | succ h ih =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b xs =>
        simp only [sortFuel,CountedSort.sortFuel,merge_counted_value,ih]

theorem sortFuel_value (cmp : α→α→Bool×Nat) (h : Nat) (xs : List α)
    (hh : xs.length≤2^h) :
    (sortFuel cmp h xs).1=xs.mergeSort (order cmp) := by
  rw [sortFuel_counted_value,CountedSort.sortFuel_value (order cmp) h xs hh]

theorem sortFuel_length (cmp : α→α→Bool×Nat) (h : Nat) (xs : List α) :
    (sortFuel cmp h xs).1.length=xs.length := by
  rw [sortFuel_counted_value,CountedSort.sortFuel_length]

theorem sortFuel_steps_scale (cmp : α→α→Bool×Nat) (C : Nat)
    (hc : ∀ a b,(cmp a b).2≤C) (h : Nat) (xs : List α) :
    (sortFuel cmp h xs).2≤(C+1)*(CountedSort.sortFuel (order cmp) h xs).2 := by
  induction h generalizing xs with
  | zero => simp [sortFuel,CountedSort.sortFuel]
  | succ h ih =>
    cases xs with
    | nil => simp [sortFuel,CountedSort.sortFuel]
    | cons a xs =>
      cases xs with
      | nil => simp [sortFuel,CountedSort.sortFuel]
      | cons b xs =>
        let ln:=CountedSort.length (a::b::xs)
        let p:=CountedSort.splitAt ((ln.1+1)/2) (a::b::xs)
        have hl:=ih p.1.1
        have hr:=ih p.1.2
        have hm:=merge_steps_scale cmp C hc
          (sortFuel cmp h p.1.1).1 (sortFuel cmp h p.1.2).1
        rw [sortFuel_counted_value,sortFuel_counted_value] at hm
        have ho : ln.2+p.2+3≤(C+1)*(ln.2+p.2+3) := by
          have hh:=Nat.mul_le_mul_right (ln.2+p.2+3) (show 1≤C+1 by omega)
          simpa only [Nat.one_mul] using hh
        simp only [sortFuel,CountedSort.sortFuel]
        change ln.2+p.2+(sortFuel cmp h p.1.1).2+(sortFuel cmp h p.1.2).2+
          (merge cmp (sortFuel cmp h p.1.1).1 (sortFuel cmp h p.1.2).1).2+3≤
          (C+1)*(ln.2+p.2+(CountedSort.sortFuel (order cmp) h p.1.1).2+
            (CountedSort.sortFuel (order cmp) h p.1.2).2+
            (CountedSort.merge (order cmp) (CountedSort.sortFuel (order cmp) h p.1.1).1
              (CountedSort.sortFuel (order cmp) h p.1.2).1).2+3)
        rw [sortFuel_counted_value,sortFuel_counted_value]
        simp only [Nat.mul_add] at ho ⊢
        omega

def sort (cmp : α→α→Bool×Nat) : List α→List α×Nat
  | [] => ([],0)
  | a::xs =>
    let ln:=CountedSort.length (a::xs)
    let r:=sortFuel cmp (ln.1.log2+1) (a::xs)
    (r.1,r.2+ln.2+1)

theorem sort_counted_value (cmp : α→α→Bool×Nat) (xs : List α) :
    (sort cmp xs).1=(CountedSort.sort (order cmp) xs).1 := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    simp only [sort,CountedSort.sort,sortFuel_counted_value]

theorem sort_value (cmp : α→α→Bool×Nat) (xs : List α) :
    (sort cmp xs).1=xs.mergeSort (order cmp) := by
  rw [sort_counted_value,CountedSort.sort_value]

theorem sort_perm (cmp : α→α→Bool×Nat) (xs : List α) :
    (sort cmp xs).1.Perm xs := by
  rw [sort_value]
  exact List.mergeSort_perm _ _

theorem sort_length (cmp : α→α→Bool×Nat) (xs : List α) :
    (sort cmp xs).1.length=xs.length := (sort_perm cmp xs).length_eq

theorem sort_mem (cmp : α→α→Bool×Nat) (xs : List α) (a : α) :
    a∈(sort cmp xs).1 ↔ a∈xs := (sort_perm cmp xs).mem_iff

theorem sort_sorted (cmp : α→α→Bool×Nat)
    (ht : ∀ a b c,order cmp a b→order cmp b c→order cmp a c)
    (ho : ∀ a b,order cmp a b || order cmp b a) (xs : List α) :
    (sort cmp xs).1.Pairwise (fun a b=>order cmp a b=true) := by
  rw [sort_value]
  exact List.sorted_mergeSort ht ho xs

theorem sort_steps_scale (cmp : α→α→Bool×Nat) (C : Nat)
    (hc : ∀ a b,(cmp a b).2≤C) (xs : List α) :
    (sort cmp xs).2≤(C+1)*(CountedSort.sort (order cmp) xs).2 := by
  cases xs with
  | nil => simp [sort,CountedSort.sort]
  | cons a xs =>
    let ln:=CountedSort.length (a::xs)
    have hh:=sortFuel_steps_scale cmp C hc (ln.1.log2+1) (a::xs)
    have ho : ln.2+1≤(C+1)*(ln.2+1) := by
      have hh:=Nat.mul_le_mul_right (ln.2+1) (show 1≤C+1 by omega)
      simpa only [Nat.one_mul] using hh
    simp only [sort,CountedSort.sort]
    change (sortFuel cmp (ln.1.log2+1) (a::xs)).2+ln.2+1≤
      (C+1)*((CountedSort.sortFuel (order cmp) (ln.1.log2+1) (a::xs)).2+ln.2+1)
    simp only [Nat.mul_add] at ho ⊢
    omega

theorem sort_steps (cmp : α→α→Bool×Nat) (C : Nat)
    (hc : ∀ a b,(cmp a b).2≤C) (xs : List α) :
    (sort cmp xs).2≤(C+1)*(8*xs.length*(xs.length.log2+1)) :=
  Nat.le_trans (sort_steps_scale cmp C hc xs)
    (Nat.mul_le_mul_left (C+1) (CountedSort.sort_steps (order cmp) xs))

end REWB.BoundaryTrie.Sort
