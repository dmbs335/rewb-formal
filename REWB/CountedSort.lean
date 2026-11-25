import REWB.IntervalSweep

/-! A measured stable merge sort, with the same output as List.mergeSort.
    The counter records length/split list visits, merge comparisons and
    output steps, and the scalar split setup. Empty/base returns have no
    data-dependent work. Sorting is bounded by 8*n*(log2 n+1). -/
namespace REWB.CountedSort
variable {α : Type}

def length : List α→Nat×Nat
  | [] => (0,0)
  | _::xs => let r:=length xs; (r.1+1,r.2+1)

theorem length_value (xs : List α) : (length xs).1=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [length,List.length_cons,ih]

theorem length_steps (xs : List α) : (length xs).2=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [length,List.length_cons,ih]

def lengthTR (xs : List α) : Nat×Nat := let n:=xs.length; (n,n)

@[csimp] theorem length_eq_lengthTR : @length=@lengthTR := by
  funext α xs
  exact Prod.ext (length_value xs) (length_steps xs)

def splitAt : Nat→List α→(List α×List α)×Nat
  | 0,xs => (([],xs),0)
  | _+1,[] => (([],[]),0)
  | k+1,x::xs => let r:=splitAt k xs; ((x::r.1.1,r.1.2),r.2+1)

theorem splitAt_value (k : Nat) (xs : List α) :
    (splitAt k xs).1=(xs.take k,xs.drop k) := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [splitAt,List.take_succ_cons,List.drop_succ_cons,ih]

theorem splitAt_steps (k : Nat) (xs : List α) : (splitAt k xs).2≤xs.length := by
  induction k generalizing xs with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    cases xs with
    | nil => exact Nat.le_refl _
    | cons x xs => exact Nat.add_le_add_right (ih xs) 1

theorem splitAt_steps_exact (k : Nat) (xs : List α) : (splitAt k xs).2=min k xs.length := by
  induction k generalizing xs with
  | zero => simp [splitAt]
  | succ k ih =>
    cases xs with
    | nil => simp [splitAt]
    | cons x xs => simp only [splitAt,ih,List.length_cons]; omega

def splitAtTR (k : Nat) (xs : List α) : (List α×List α)×Nat :=
  (xs.splitAt k,min k xs.length)

@[csimp] theorem splitAt_eq_splitAtTR : @splitAt=@splitAtTR := by
  funext α k xs
  apply Prod.ext
  · simpa only [splitAtTR,List.splitAt_eq] using splitAt_value k xs
  · exact splitAt_steps_exact k xs

def merge (le : α→α→Bool) : List α→List α→List α×Nat
  | [],ys => (ys,0)
  | xs,[] => (xs,0)
  | a::as,b::bs =>
    if le a b then
      let r:=merge le as (b::bs); (a::r.1,r.2+2)
    else
      let r:=merge le (a::as) bs; (b::r.1,r.2+2)

theorem merge_value (le : α→α→Bool) (xs ys : List α) :
    (merge le xs ys).1=List.merge xs ys le := by
  induction xs generalizing ys with
  | nil => simp [merge,List.merge]
  | cons a as ih =>
    induction ys with
    | nil => simp [merge,List.merge]
    | cons b bs ih' =>
      simp only [merge,List.merge]
      split
      · rw [ih]
      · rw [ih']

theorem merge_steps (le : α→α→Bool) (xs ys : List α) :
    (merge le xs ys).2≤2*(xs.length+ys.length) := by
  induction xs generalizing ys with
  | nil => simp [merge]
  | cons a as ih =>
    induction ys with
    | nil => simp [merge]
    | cons b bs ih' =>
      simp only [merge]
      split
      · have h:=ih (b::bs)
        simp only [List.length_cons] at h ⊢
        omega
      · simp only [List.length_cons] at ih' ⊢
        omega

def mergeTR.go (le : α→α→Bool) : List α→List α→List α→Nat→List α×Nat
  | [],ys,acc,c => (acc.reverseAux ys,c)
  | xs,[],acc,c => (acc.reverseAux xs,c)
  | a::as,b::bs,acc,c =>
    if le a b then go le as (b::bs) (a::acc) (c+2)
    else go le (a::as) bs (b::acc) (c+2)

theorem mergeTR.go_eq (le : α→α→Bool) (xs ys acc : List α) (c : Nat) :
    go le xs ys acc c=(acc.reverse++(merge le xs ys).1,c+(merge le xs ys).2) := by
  induction xs generalizing ys acc c with
  | nil => simp [go,merge,List.reverseAux_eq]
  | cons a as ih =>
    induction ys generalizing acc c with
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

def mergeTR (le : α→α→Bool) (xs ys : List α) : List α×Nat := mergeTR.go le xs ys [] 0

@[csimp] theorem merge_eq_mergeTR : @merge=@mergeTR := by
  funext α le xs ys
  simp only [mergeTR,mergeTR.go_eq,List.reverse_nil,List.nil_append,Nat.zero_add]

def sortFuel (le : α→α→Bool) : Nat→List α→List α×Nat
  | 0,xs => (xs,0)
  | _+1,[] => ([],0)
  | _+1,[a] => ([a],0)
  | h+1,a::b::xs =>
    let ln:=length (a::b::xs)
    let p:=splitAt ((ln.1+1)/2) (a::b::xs)
    let l:=sortFuel le h p.1.1
    let r:=sortFuel le h p.1.2
    let m:=merge le l.1 r.1
    (m.1,ln.2+p.2+l.2+r.2+m.2+3)

theorem sortFuel_length (le : α→α→Bool) (h : Nat) (xs : List α) :
    (sortFuel le h xs).1.length=xs.length := by
  induction h generalizing xs with
  | zero => rfl
  | succ h ih =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b xs =>
        simp only [sortFuel,merge_value,List.length_merge,ih,length_value,splitAt_value,
          List.length_take,List.length_drop]
        omega

theorem sortFuel_value (le : α→α→Bool) (h : Nat) (xs : List α) (hh : xs.length≤2^h) :
    (sortFuel le h xs).1=xs.mergeSort le := by
  induction h generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [sortFuel,List.mergeSort]
    | cons a xs =>
      cases xs with
      | nil => simp [sortFuel,List.mergeSort]
      | cons b xs => simp only [List.length_cons,Nat.pow_zero] at hh; omega
  | succ h ih =>
    cases xs with
    | nil => simp [sortFuel,List.mergeSort]
    | cons a xs =>
      cases xs with
      | nil => simp [sortFuel,List.mergeSort]
      | cons b xs =>
        have hleft : ((a::b::xs).take (((a::b::xs).length+1)/2)).length≤2^h := by
          rw [List.length_take]
          rw [Nat.pow_succ] at hh
          omega
        have hright : ((a::b::xs).drop (((a::b::xs).length+1)/2)).length≤2^h := by
          rw [List.length_drop]
          rw [Nat.pow_succ] at hh
          omega
        simp only [sortFuel,length_value,splitAt_value,merge_value,ih _ hleft,ih _ hright]
        rw [List.mergeSort]
        simp only [List.MergeSort.Internal.splitInTwo_fst,List.MergeSort.Internal.splitInTwo_snd]

theorem sortFuel_steps (le : α→α→Bool) (h : Nat) (xs : List α) :
    (sortFuel le h xs).2≤6*xs.length*h := by
  induction h generalizing xs with
  | zero => simp [sortFuel]
  | succ h ih =>
    cases xs with
    | nil => simp [sortFuel]
    | cons a xs =>
      cases xs with
      | nil => simp [sortFuel]
      | cons b xs =>
        let p:=splitAt (((a::b::xs).length+1)/2) (a::b::xs)
        have hl:=ih p.1.1
        have hr:=ih p.1.2
        have hp: p.1.1.length+p.1.2.length=(a::b::xs).length := by
          simp only [p,splitAt_value,List.length_take,List.length_drop]
          omega
        have hm:=merge_steps le (sortFuel le h p.1.1).1 (sortFuel le h p.1.2).1
        rw [sortFuel_length,sortFuel_length,hp] at hm
        have hs:=splitAt_steps (((a::b::xs).length+1)/2) (a::b::xs)
        change p.2≤(a::b::xs).length at hs
        have hsums : 6*p.1.1.length*h+6*p.1.2.length*h=6*(a::b::xs).length*h := by
          rw [← Nat.add_mul,← Nat.mul_add,hp]
        simp only [sortFuel,length_value,length_steps]
        change (a::b::xs).length+p.2+(sortFuel le h p.1.1).2+(sortFuel le h p.1.2).2+
          (merge le (sortFuel le h p.1.1).1 (sortFuel le h p.1.2).1).2+3≤6*(a::b::xs).length*(h+1)
        rw [Nat.mul_add,Nat.mul_one]
        have hh:=Nat.add_le_add hl hr
        rw [hsums] at hh
        have hn : 2≤(a::b::xs).length := by simp
        omega

def sort (le : α→α→Bool) : List α→List α×Nat
  | [] => ([],0)
  | a::xs =>
    let ln:=length (a::xs)
    let r:=sortFuel le (ln.1.log2+1) (a::xs)
    (r.1,r.2+ln.2+1)

theorem sort_value (le : α→α→Bool) (xs : List α) : (sort le xs).1=xs.mergeSort le := by
  cases xs with
  | nil => simp [sort,List.mergeSort]
  | cons a xs =>
    simp only [sort,length_value]
    exact sortFuel_value le _ _ (Nat.le_of_lt Nat.lt_log2_self)

theorem sort_steps (le : α→α→Bool) (xs : List α) :
    (sort le xs).2≤8*xs.length*(xs.length.log2+1) := by
  cases xs with
  | nil => simp [sort]
  | cons a xs =>
    have h:=sortFuel_steps le ((a::xs).length.log2+1) (a::xs)
    have hm:=Nat.mul_le_mul_left (a::xs).length (show 1≤(a::xs).length.log2+1 by omega)
    simp only [Nat.mul_one] at hm
    simp only [sort,length_value,length_steps]
    have hp : 1≤(a::xs).length := by simp
    have he : 8*(a::xs).length*((a::xs).length.log2+1)=
        6*(a::xs).length*((a::xs).length.log2+1)+2*((a::xs).length*((a::xs).length.log2+1)) := by
      rw [← Nat.mul_assoc,← Nat.add_mul,← Nat.add_mul]
    rw [he]
    omega

end REWB.CountedSort
