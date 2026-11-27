import REWB.RankIndex

/-! Enumerate every displacement/divisor incidence in O(n log n)
output size without trial-dividing every displacement. Positive candidate
periods are grouped by dyadic scales, then their multiples are emitted.
This schedule supports minimum-period tests over sampled equality strips;
it does not scan the potentially quadratic total length of all runs. -/
namespace REWB.RankIndexDivisors

def multiples (n q : Nat) : List (Nat × Nat) :=
  (List.range (n/q)).map (fun m=>(q*(m+1),q))

theorem multiples_length (n q : Nat) : (multiples n q).length=n/q := by
  simp only [multiples,List.length_map,List.length_range]

theorem multiples_mem (n q d p : Nat) (hq : 0<q) :
    (d,p)∈multiples n q ↔ p=q ∧ 0<d ∧ d≤n ∧ q∣d := by
  constructor
  · intro h
    obtain ⟨m,hm,he⟩ := List.mem_map.mp h
    have hpq := congrArg Prod.snd he
    have hdm := congrArg Prod.fst he
    dsimp only at hpq hdm
    have hm' : m+1≤n/q := by have hh:=List.mem_range.mp hm; omega
    have hprod := Nat.mul_le_mul_left q hm'
    have hdiv := Nat.div_mul_le_self n q
    rw [Nat.mul_comm (n/q) q] at hdiv
    refine ⟨hpq.symm,?_,?_,⟨m+1,hdm.symm⟩⟩
    · have hh := Nat.mul_pos hq (by omega : 0<m+1)
      omega
    · omega
  · rintro ⟨hpq,hd,hn,hdiv⟩
    subst p
    obtain ⟨m,hm⟩ := hdiv
    have hmpos : 0<m := by
      by_cases hz : m=0
      · rw [hz,Nat.mul_zero] at hm
        omega
      · omega
    have hml : m≤n/q := by
      apply (Nat.le_div_iff_mul_le hq).mpr
      rw [Nat.mul_comm,← hm]
      exact hn
    apply List.mem_map.mpr
    refine ⟨m-1,List.mem_range.mpr (by omega),?_⟩
    apply Prod.ext
    · change q*(m-1+1)=d
      rw [show m-1+1=m by omega,← hm]
    · rfl

def scale (n h : Nat) : List (Nat × Nat) :=
  (List.range (2^h)).flatMap (fun a=>multiples n (2^h+a))

theorem scale_mem (n h d q : Nat) :
    (d,q)∈scale n h ↔ 2^h≤q ∧ q<2*2^h ∧ 0<d ∧ d≤n ∧ q∣d := by
  constructor
  · intro hm
    obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hm
    have hp : 0<2^h+a := by have hh:=Nat.two_pow_pos h; omega
    obtain ⟨he,hd,hn,hdiv⟩ := (multiples_mem n (2^h+a) d q hp).mp hm
    have ha' := List.mem_range.mp ha
    refine ⟨by omega,by omega,hd,hn,?_⟩
    rwa [← he] at hdiv
  · rintro ⟨hlo,hhi,hd,hn,hdiv⟩
    have hp : 0<q := by have hh:=Nat.two_pow_pos h; omega
    apply List.mem_flatMap.mpr
    refine ⟨q-2^h,List.mem_range.mpr (by omega),?_⟩
    rw [show 2^h+(q-2^h)=q by omega]
    exact (multiples_mem n q d q hp).mpr ⟨rfl,hd,hn,hdiv⟩

private theorem flatMap_length_le {X Y : Type} (xs : List X) (f : X→List Y) (B : Nat)
    (h : ∀ x,x∈xs→(f x).length≤B) : (xs.flatMap f).length≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    exact Nat.le_trans (Nat.add_le_add (h x (by simp)) (ih (fun y hy=>h y (by simp [hy]))))
      (by omega)

/-- Each dyadic scale has at most n divisor incidences: at most 2^h
candidate periods, each with at most floor(n/2^h) multiples. -/
theorem scale_length (n h : Nat) : (scale n h).length≤n := by
  have hb := flatMap_length_le (List.range (2^h))
    (fun a=>multiples n (2^h+a)) (n/(2^h)) (fun a _=>by
      rw [multiples_length]
      exact Nat.div_le_div_left (by omega) (Nat.two_pow_pos h))
  rw [List.length_range] at hb
  have hh := Nat.div_mul_le_self n (2^h)
  rw [Nat.mul_comm] at hh
  exact Nat.le_trans hb hh

def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range (n.log2+1)).flatMap (scale n)

theorem pairs_mem (n d q : Nat) :
    (d,q)∈pairs n ↔ 0<d ∧ d≤n ∧ 0<q ∧ q∣d := by
  constructor
  · intro hm
    obtain ⟨h,hh,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨hlo,hhi,hd,hn,hdiv⟩ := (scale_mem n h d q).mp hm
    exact ⟨hd,hn,by have hp:=Nat.two_pow_pos h; omega,hdiv⟩
  · rintro ⟨hd,hn,hq,hdiv⟩
    have hqn := Nat.le_trans (Nat.le_of_dvd hd hdiv) hn
    have hpow := Nat.log2_self_le (by omega : q≠0)
    have hlog : q.log2≤n.log2 :=
      (Nat.le_log2 (by omega : n≠0)).mpr (Nat.le_trans hpow hqn)
    apply List.mem_flatMap.mpr
    refine ⟨q.log2,List.mem_range.mpr (by omega),?_⟩
    apply (scale_mem n q.log2 d q).mpr
    have hu := Nat.lt_log2_self (n:=q)
    rw [Nat.pow_succ] at hu
    exact ⟨hpow,by omega,hd,hn,hdiv⟩

theorem pairs_length (n : Nat) : (pairs n).length≤n*(n.log2+1) := by
  have hh := flatMap_length_le (List.range (n.log2+1)) (scale n) n (fun h _=>scale_length n h)
  rw [List.length_range,Nat.mul_comm] at hh
  exact hh

/-- Expanding each incidence across the same grid-anchor schedule
has the exact expected product bound, before each LCE period test. -/
def gridTests (n s : Nat) : List (Nat × Nat × Nat) :=
  (pairs n).flatMap (fun x=>(List.range (n/s+1)).map (fun a=>(a*s,x)))

theorem gridTests_length (n s : Nat) :
    (gridTests n s).length≤(n/s+1)*(n*(n.log2+1)) := by
  have hh := flatMap_length_le (pairs n)
    (fun x=>(List.range (n/s+1)).map (fun a=>(a*s,x))) (n/s+1)
    (fun _ _=>by simp only [List.length_map,List.length_range]; exact Nat.le_refl _)
  have hb := Nat.mul_le_mul_right (n/s+1) (pairs_length n)
  have he : (n*(n.log2+1))*(n/s+1)=(n/s+1)*(n*(n.log2+1)) := Nat.mul_comm _ _
  exact Nat.le_trans hh (by rwa [he] at hb)

theorem gridTests_coverage (n s d q a : Nat)
    (hd : 0<d) (hdn : d≤n) (hq : 0<q) (hdiv : q∣d) (ha : a≤n/s) :
    (a*s,(d,q))∈gridTests n s := by
  apply List.mem_flatMap.mpr
  refine ⟨(d,q),(pairs_mem n d q).mpr ⟨hd,hdn,hq,hdiv⟩,?_⟩
  exact List.mem_map.mpr ⟨a,List.mem_range.mpr (by omega),rfl⟩

def bucket (bs : Array (List Nat)) (d : Nat) : List Nat := bs[d]?.getD []

def insert (bs : Array (List Nat)) (d q : Nat) : Array (List Nat) :=
  bs.setIfInBounds d (q::bucket bs d)

theorem insert_size (bs : Array (List Nat)) (d q : Nat) : (insert bs d q).size=bs.size := by
  simp only [insert,Array.size_setIfInBounds]

theorem insert_mem (bs : Array (List Nat)) (d q x y : Nat) (hd : d<bs.size) :
    y∈bucket (insert bs d q) x ↔ y∈bucket bs x ∨ (x=d ∧ y=q) := by
  by_cases he : d=x
  · subst x
    rw [bucket,insert,Array.getElem?_setIfInBounds_self_of_lt hd]
    simp only [Option.getD_some,List.mem_cons,true_and]
    exact Or.comm
  · rw [bucket,insert,Array.getElem?_setIfInBounds_ne he]
    change y∈bucket bs x ↔ y∈bucket bs x ∨ (x=d ∧ y=q)
    simp only [show x≠d by omega,false_and,or_false]

def fill : List (Nat × Nat)→Array (List Nat)→Nat→Array (List Nat)×Nat
  | [],bs,c => (bs,c)
  | (d,q)::xs,bs,c => fill xs (insert bs d q) (c+3)

theorem fill_size (xs : List (Nat × Nat)) (bs : Array (List Nat)) (c : Nat) :
    (fill xs bs c).1.size=bs.size := by
  induction xs generalizing bs c with
  | nil => rfl
  | cons x xs ih =>
    rw [fill,ih,insert_size]

theorem fill_work (xs : List (Nat × Nat)) (bs : Array (List Nat)) (c : Nat) :
    (fill xs bs c).2=c+3*xs.length := by
  induction xs generalizing bs c with
  | nil => simp [fill]
  | cons x xs ih =>
    rw [fill,ih,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem fill_mem (xs : List (Nat × Nat)) (bs : Array (List Nat)) (c d q : Nat)
    (hb : ∀ x,x∈xs→x.1<bs.size) :
    q∈bucket (fill xs bs c).1 d ↔ q∈bucket bs d ∨ (d,q)∈xs := by
  induction xs generalizing bs c with
  | nil => simp [fill]
  | cons x xs ih =>
    rw [fill,ih (insert bs x.1 x.2) (c+3) (by
      intro y hy
      rw [insert_size]
      exact hb y (by simp [hy])),insert_mem bs x.1 x.2 d q (hb x (by simp)),
      List.mem_cons,Prod.mk.injEq]
    simp only [or_assoc]

def cellsList : List (List Nat)→Nat
  | [] => 0
  | r::rs => r.length+cellsList rs

def cells (bs : Array (List Nat)) : Nat := cellsList bs.toList

theorem cellsList_set (xs : List (List Nat)) (i q : Nat) (hi : i<xs.length) :
    cellsList (xs.set i (q::xs[i]?.getD []))=cellsList xs+1 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero => simp only [List.set_cons_zero,List.getElem?_cons_zero,Option.getD_some,cellsList,List.length_cons]; omega
    | succ i =>
      simp only [List.set_cons_succ,List.getElem?_cons_succ,cellsList]
      rw [ih i (by simp only [List.length_cons] at hi; omega)]
      omega

theorem insert_cells (bs : Array (List Nat)) (d q : Nat) (hd : d<bs.size) :
    cells (insert bs d q)=cells bs+1 := by
  have hh := cellsList_set bs.toList d q (by simpa only [Array.length_toList] using hd)
  unfold cells insert bucket
  rw [Array.toList_setIfInBounds]
  rw [Array.getElem?_toList] at hh
  exact hh

theorem fill_cells (xs : List (Nat × Nat)) (bs : Array (List Nat)) (c : Nat)
    (hb : ∀ x,x∈xs→x.1<bs.size) :
    cells (fill xs bs c).1=cells bs+xs.length := by
  induction xs generalizing bs c with
  | nil => simp [fill]
  | cons x xs ih =>
    rw [fill,ih (insert bs x.1 x.2) (c+3) (by
      intro y hy
      rw [insert_size]
      exact hb y (by simp [hy])),insert_cells bs x.1 x.2 (hb x (by simp)),List.length_cons]
    omega

def buckets (n : Nat) : Array (List Nat)×Nat := fill (pairs n) (Array.replicate (n+1) []) 0

theorem buckets_size (n : Nat) : (buckets n).1.size=n+1 := by
  rw [buckets,fill_size,Array.size_replicate]

private theorem pairs_in_bounds (n : Nat) :
    ∀ x,x∈pairs n→x.1<(Array.replicate (n+1) ([] : List Nat)).size := by
  intro x hx
  have hh := (pairs_mem n x.1 x.2).mp hx
  rw [Array.size_replicate]
  omega

theorem buckets_mem (n d q : Nat) :
    q∈bucket (buckets n).1 d ↔ 0<d ∧ d≤n ∧ 0<q ∧ q∣d := by
  rw [buckets,fill_mem _ _ _ _ _ (pairs_in_bounds n)]
  have he : bucket (Array.replicate (n+1) ([] : List Nat)) d=[] := by
    unfold bucket
    rw [Array.getElem?_replicate]
    split <;> rfl
  rw [he]
  simp only [List.not_mem_nil,false_or]
  exact pairs_mem n d q

theorem buckets_work (n : Nat) : (buckets n).2≤3*(n*(n.log2+1)) := by
  rw [buckets,fill_work,Nat.zero_add]
  exact Nat.mul_le_mul_left 3 (pairs_length n)

theorem buckets_cells (n : Nat) : cells (buckets n).1=(pairs n).length := by
  rw [buckets,fill_cells _ _ _ (pairs_in_bounds n)]
  have he : cells (Array.replicate (n+1) ([] : List Nat))=0 := by
    unfold cells
    rw [Array.toList_replicate]
    have aux : ∀ k,cellsList (List.replicate k ([] : List Nat))=0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simp only [List.replicate_succ,cellsList,List.length_nil,Nat.zero_add,ih]
    exact aux (n+1)
  rw [he,Nat.zero_add]

end REWB.RankIndexDivisors
