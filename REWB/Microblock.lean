import REWB.FlatIndex

/-! Small-block tables. A block of text is fixed across endpoint columns;
    only its Boolean marks vary. Precompute all 2^b mark assignments once,
    rather than rebuilding an interval index for every column.
    The numeric code is computed with one pass over the bits. -/
namespace REWB.Microblock
open REWB.RangeProducts
open REWB.Spec (slice)

def patterns : Nat → List (List Bool)
  | 0 => [[]]
  | k+1 =>
    let tail := patterns k
    tail.map (false :: ·) ++ tail.map (true :: ·)

def encode : List Bool → Nat × Nat
  | [] => (0,1)
  | b::bs =>
    let p := encode bs
    (if b then p.2+p.1 else p.1,p.2+p.2)

theorem patterns_length (k : Nat) : (patterns k).length=2^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((patterns k).map (false::·) ++ (patterns k).map (true::·)).length=2^(k+1)
    rw [List.length_append,List.length_map,List.length_map,ih,Nat.pow_succ]
    omega

theorem encode_base (bs : List Bool) : (encode bs).2=2^bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (encode bs).2+(encode bs).2=2^(bs.length+1)
    rw [ih,Nat.pow_succ]
    omega

theorem encode_bound (bs : List Bool) : (encode bs).1<(encode bs).2 := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp only [encode,if_true,if_false,Bool.false_eq_true,Prod.fst,Prod.snd] <;> omega

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
    have he : (x::xs).length+i=(xs.length+i)+1 := by simp; omega
    rw [he]
    exact ih

theorem patterns_get (bs : List Bool) :
    (patterns bs.length)[(encode bs).1]?=some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hlen : ((patterns bs.length).map (false::·)).length=(encode bs).2 := by
      rw [List.length_map,patterns_length,encode_base]
    have hlt := encode_bound bs
    cases b
    · change (((patterns bs.length).map (false::·) ++
        (patterns bs.length).map (true::·))[(encode bs).1]?)=_
      rw [get_left _ _ _ (by omega),List.getElem?_map,ih]
      rfl
    · change (((patterns bs.length).map (false::·) ++
        (patterns bs.length).map (true::·))[(encode bs).2+(encode bs).1]?)=_
      rw [← hlen,get_right,List.getElem?_map,ih]
      rfl

theorem patterns_mem_length (n : Nat) (bs : List Bool)
    (h : bs∈patterns n) : bs.length=n := by
  induction n generalizing bs with
  | zero =>
    have he : bs=[] := by simpa [patterns] using h
    subst bs
    rfl
  | succ n ih =>
    change bs∈(patterns n).map (false::·) ++ (patterns n).map (true::·) at h
    rcases List.mem_append.mp h with h|h
    · obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp h
      simp [ih tail ht]
    · obtain ⟨tail,ht,rfl⟩ := List.mem_map.mp h
      simp [ih tail ht]

variable {M : Type}

def rows (o : Ops M) : List M → List (List M)
  | [] => [[o.one]]
  | x::xs => (prefixScan o o.one (x::xs)).1 :: rows o xs

theorem rows_get (o : Ops M) (xs : List M) (l : Nat) (hl : l≤xs.length) :
    (rows o xs)[l]?=some (prefixScan o o.one (xs.drop l)).1 := by
  induction xs generalizing l with
  | nil =>
    have he : l=0 := by simpa using hl
    subst l
    rfl
  | cons x xs ih =>
    cases l with
    | zero => rfl
    | succ l =>
      have hh : l≤xs.length := by simpa using hl
      exact ih l hh

def buildRanges (o : Ops M) (xs : List M) : Array (Array M) :=
  ((rows o xs).map List.toArray).toArray

def rangeAt (idx : Array (Array M)) (l r : Nat) : Option M :=
  (idx[l]?).bind (fun row=>row[r-l]?)

theorem rangeAt_correct (o : Ops M) (xs : List M) (l r : Nat)
    (hl : l≤r) (hr : r≤xs.length) :
    rangeAt (buildRanges o xs) l r=some (product o (slice xs l r)) := by
  have hk : r-l≤(xs.drop l).length := by rw [List.length_drop]; omega
  unfold rangeAt buildRanges
  simp only [List.getElem?_toArray,List.getElem?_map,rows_get o xs l (by omega),
    Option.map,Option.bind,prefix_get o o.one (xs.drop l) (r-l) hk,o.one_mul,slice]

def countedRows (o : Ops M) : List M → List (List M) × Nat
  | [] => ([[o.one]],0)
  | x::xs =>
    let row := prefixScan o o.one (x::xs)
    let rest := countedRows o xs
    (row.1::rest.1,row.2+rest.2)

theorem countedRows_correct (o : Ops M) (xs : List M) :
    (countedRows o xs).1=rows o xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (prefixScan o o.one (x::xs)).1::(countedRows o xs).1=_
    rw [ih]
    rfl

theorem countedRows_cost (o : Ops M) (xs : List M) :
    2*(countedRows o xs).2=xs.length*(xs.length+1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change 2*((prefixScan o o.one (x::xs)).2+(countedRows o xs).2)=_
    rw [prefix_cost,Nat.mul_add,ih]
    simp only [List.length_cons,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega

def buildCountedRanges (o : Ops M) (xs : List M) : Array (Array M) × Nat :=
  let r := countedRows o xs
  ((r.1.map List.toArray).toArray,r.2)

theorem buildCountedRanges_correct (o : Ops M) (xs : List M) :
    (buildCountedRanges o xs).1=buildRanges o xs := by
  change ((countedRows o xs).1.map List.toArray).toArray=((rows o xs).map List.toArray).toArray
  rw [countedRows_correct]

theorem buildCountedRanges_cost (o : Ops M) (xs : List M) :
    2*(buildCountedRanges o xs).2=xs.length*(xs.length+1) :=
  countedRows_cost o xs

variable {α : Type}

/-- Pair a fixed text block with a bit assignment; equal lengths are used
    in every valid lookup. -/
def decorate (f : α × Bool → M) : List α → List Bool → List M
  | c::cs,b::bs => f (c,b)::decorate f cs bs
  | _,_ => []

theorem decorate_length (f : α × Bool → M) (xs : List α) (bs : List Bool)
    (h : xs.length=bs.length) : (decorate f xs bs).length=xs.length := by
  induction xs generalizing bs with
  | nil => rfl
  | cons x xs ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have he : xs.length=bs.length := by simpa using h
      change (decorate f xs bs).length+1=xs.length+1
      rw [ih bs he]

theorem decorate_actual (f : α × Bool → M) (w : List (α × Bool)) :
    decorate f (w.map Prod.fst) (w.map Prod.snd)=w.map f := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c,b⟩
    change f (c,b)::decorate f (xs.map Prod.fst) (xs.map Prod.snd)=f (c,b)::xs.map f
    rw [ih]

abbrev Dictionary (M : Type) := Array (Array (Array M))

def dictionary (o : Ops M) (f : α × Bool → M) (xs : List α) : Dictionary M :=
  ((patterns xs.length).map (fun bs=>buildRanges o (decorate f xs bs))).toArray

def select (dict : Dictionary M) (bs : List Bool) : Option (Array (Array M)) :=
  dict[(encode bs).1]?

theorem select_correct (o : Ops M) (f : α × Bool → M) (xs : List α)
    (bs : List Bool) (h : xs.length=bs.length) :
    select (dictionary o f xs) bs=some (buildRanges o (decorate f xs bs)) := by
  unfold select dictionary
  rw [List.getElem?_toArray,List.getElem?_map,h,patterns_get]
  rfl

/-- A column selects a precomputed block once. Subsequent local queries use
    only the two array reads in rangeAt, with no encoding or traversal. -/
theorem select_actual (o : Ops M) (f : α × Bool → M) (w : List (α × Bool)) :
    select (dictionary o f (w.map Prod.fst)) (w.map Prod.snd)=
      some (buildRanges o (w.map f)) := by
  rw [select_correct o f _ _ (by simp),decorate_actual]

theorem dictionary_size (o : Ops M) (f : α × Bool → M) (xs : List α) :
    (dictionary o f xs).size=2^xs.length := by
  simp only [dictionary,List.size_toArray,List.length_map,patterns_length]

/-- Count the monoid products in the actual construction of all local
    interval tables. The bit enumeration and storage work are separate. -/
def collectCounted (o : Ops M) (f : α × Bool → M) (xs : List α) :
    List (List Bool) → List (Array (Array M)) × Nat
  | [] => ([],0)
  | bs::bss =>
    let head := buildCountedRanges o (decorate f xs bs)
    let rest := collectCounted o f xs bss
    (head.1::rest.1,head.2+rest.2)

theorem collect_correct (o : Ops M) (f : α × Bool → M) (xs : List α)
    (bss : List (List Bool)) :
    (collectCounted o f xs bss).1=bss.map (fun bs=>buildRanges o (decorate f xs bs)) := by
  induction bss with
  | nil => rfl
  | cons bs bss ih =>
    change (buildCountedRanges o (decorate f xs bs)).1::
      (collectCounted o f xs bss).1=_
    rw [buildCountedRanges_correct,ih]
    rfl

theorem collect_cost (o : Ops M) (f : α × Bool → M) (xs : List α)
    (bss : List (List Bool)) (h : ∀ bs,bs∈bss→bs.length=xs.length) :
    2*(collectCounted o f xs bss).2=bss.length*(xs.length*(xs.length+1)) := by
  induction bss with
  | nil => simp [collectCounted]
  | cons bs bss ih =>
    have hh := h bs (by simp)
    have hr := ih (fun x hx=>h x (by simp [hx]))
    change 2*((buildCountedRanges o (decorate f xs bs)).2+
      (collectCounted o f xs bss).2)=_
    rw [Nat.mul_add,buildCountedRanges_cost,decorate_length f xs bs hh.symm,hr]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def countedDictionary (o : Ops M) (f : α × Bool → M) (xs : List α) :
    Dictionary M × Nat :=
  let d := collectCounted o f xs (patterns xs.length)
  (d.1.toArray,d.2)

theorem countedDictionary_correct (o : Ops M) (f : α × Bool → M) (xs : List α) :
    (countedDictionary o f xs).1=dictionary o f xs := by
  change (collectCounted o f xs (patterns xs.length)).1.toArray=_
  rw [collect_correct]
  rfl

theorem countedDictionary_cost (o : Ops M) (f : α × Bool → M) (xs : List α) :
    2*(countedDictionary o f xs).2=2^xs.length*(xs.length*(xs.length+1)) := by
  change 2*(collectCounted o f xs (patterns xs.length)).2=_
  rw [collect_cost o f xs _ (fun bs hb=>patterns_mem_length xs.length bs hb),patterns_length]

end REWB.Microblock
