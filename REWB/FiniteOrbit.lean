import REWB.PeriodicFactor

/-! Exact ultimately-periodic exponent sets for finite deterministic
    transitions. The cycle search is executable; its search space depends
    on the fixed state enumeration, not on the text length. -/
namespace REWB.FiniteOrbit
open FiniteRelation
variable {S : Type}

def orbit (step : S→S) (q : S) : Nat→S
  | 0 => q
  | k+1 => step (orbit step q k)

theorem orbit_add (step : S→S) (q : S) (a b : Nat) :
    orbit step q (a+b)=orbit step (orbit step q a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change step (orbit step q (a+b))=step (orbit step (orbit step q a) b)
    rw [ih]

private def removeOne [DecidableEq S] (x : S) : List S→List S
  | [] => []
  | y::ys => if x=y then ys else y::removeOne x ys

private theorem remove_length [DecidableEq S] (x : S) (xs : List S)
    (h : x∈xs) : (removeOne x xs).length+1=xs.length := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    by_cases he : x=y
    · simp [removeOne,he]
    · have hm : x∈ys := by simpa [he] using h
      simp only [removeOne,if_neg he,List.length_cons]
      have hh := ih hm
      omega

private theorem remove_mem [DecidableEq S] (x y : S) (xs : List S)
    (hne : y≠x) (h : y∈xs) : y∈removeOne x xs := by
  induction xs with
  | nil => simp at h
  | cons z zs ih =>
    by_cases he : x=z
    · subst z
      have hm : y∈zs := by simpa [hne] using h
      simpa [removeOne] using hm
    · rw [removeOne,if_neg he]
      rcases List.mem_cons.mp h with h|h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (ih h))

/-- Pigeonhole principle for a finite explicit covering list. No
    distinctness requirement on the enumeration is needed. -/
theorem cover_collision [DecidableEq S] (xs : List S) (f : Nat→S)
    (h : ∀ k,k≤xs.length→f k∈xs) :
    ∃ i j,i<j ∧ j≤xs.length ∧ f i=f j := by
  classical
  by_cases hc : ∃ j,0<j ∧ j≤xs.length ∧ f j=f 0
  · obtain ⟨j,hj,hb,he⟩ := hc
    exact ⟨0,j,hj,hb,he.symm⟩
  · let ys := removeOne (f 0) xs
    have hl : ys.length+1=xs.length := remove_length _ _ (h 0 (Nat.zero_le _))
    have hy : ∀ k,k≤ys.length→f (k+1)∈ys := by
      intro k hk
      have hb : k+1≤xs.length := by omega
      have hn : f (k+1)≠f 0 := by
        intro he
        exact hc ⟨k+1,by omega,hb,he⟩
      exact remove_mem _ _ _ hn (h _ hb)
    have hdec : (removeOne (f 0) xs).length<xs.length := by
      change (removeOne (f 0) xs).length+1=xs.length at hl
      omega
    obtain ⟨i,j,hi,hj,he⟩ := cover_collision ys (fun k=>f (k+1)) hy
    exact ⟨i+1,j+1,by omega,by omega,he⟩
termination_by xs.length
decreasing_by omega

theorem orbit_collision [DecidableEq S] (e : Enumeration S) (step : S→S) (q : S) :
    ∃ i j,i<j ∧ j≤e.elems.length ∧ orbit step q i=orbit step q j :=
  cover_collision e.elems (orbit step q) (fun k _=>e.complete (orbit step q k))

theorem orbit_normal (step : S→S) (q : S) (i j k : Nat)
    (hij : i<j) (he : orbit step q i=orbit step q j) (hk : i≤k) :
    orbit step q k=orbit step q (i+(k-i)%(j-i)) := by
  let f := fun t=>orbit step q (i+t)
  have hp : Periodic.Period f (k-i+1) (j-i) := by
    intro t ht
    change orbit step q (i+t)=orbit step q (i+(t+(j-i)))
    rw [show i+(t+(j-i))=j+t by omega,orbit_add,orbit_add,he]
  have h := Periodic.period_residue hp (k-i) (by omega)
  change orbit step q (i+(k-i))=orbit step q (i+(k-i)%(j-i)) at h
  rwa [show i+(k-i)=k by omega] at h

/-- All possible cycle witnesses up to the number of states. -/
def pairs (n : Nat) : List (Nat×Nat) :=
  (List.range (n+1)).flatMap (fun i=>(List.range (n+1)).map (fun j=>(i,j)))

theorem pairs_mem (n i j : Nat) :
    (i,j)∈pairs n ↔ i≤n ∧ j≤n := by
  unfold pairs
  simp only [List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,rfl,rfl⟩
    exact ⟨by omega,by omega⟩
  · rintro ⟨hi,hj⟩
    exact ⟨i,by omega,j,by omega,rfl,rfl⟩

def valid [DecidableEq S] (step : S→S) (q : S) (p : Nat×Nat) : Bool :=
  decide (p.1<p.2) && decide (orbit step q p.1=orbit step q p.2)

def first (test : X→Bool) : List X→Option X
  | [] => none
  | x::xs => if test x then some x else first test xs

theorem first_sound {X : Type} (test : X→Bool) (xs : List X) (x : X)
    (h : first test xs=some x) : x∈xs ∧ test x=true := by
  induction xs with
  | nil => simp [first] at h
  | cons y ys ih =>
    cases he : test y with
    | false =>
      have hh := ih (by simpa only [first,he,Bool.false_eq_true,if_false] using h)
      exact ⟨List.mem_cons.mpr (Or.inr hh.1),hh.2⟩
    | true =>
      have hx : y=x := by simpa only [first,he,if_true,Option.some.injEq] using h
      subst x
      exact ⟨by simp,he⟩

theorem first_exists {X : Type} (test : X→Bool) (xs : List X)
    (h : ∃ x,x∈xs ∧ test x=true) : ∃ y,first test xs=some y := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases he : test x with
    | true => exact ⟨x,by simp [first,he]⟩
    | false =>
      obtain ⟨y,hy,hyes⟩ := h
      have hm : y∈xs := by
        rcases List.mem_cons.mp hy with h|h
        · subst y
          rw [he] at hyes
          contradiction
        · exact h
      obtain ⟨z,hz⟩ := ih ⟨y,hm,hyes⟩
      exact ⟨z,by simpa only [first,he,Bool.false_eq_true,if_false] using hz⟩

def findCycle [DecidableEq S] (e : Enumeration S) (step : S→S) (q : S) :
    Option (Nat×Nat) :=
  first (valid step q) (pairs e.elems.length)

theorem findCycle_spec [DecidableEq S] (e : Enumeration S) (step : S→S) (q : S) :
    ∃ i j,findCycle e step q=some (i,j) ∧
      i<j ∧ j≤e.elems.length ∧ orbit step q i=orbit step q j := by
  obtain ⟨i,j,hij,hj,he⟩ := orbit_collision e step q
  have hv : valid step q (i,j)=true := by simp [valid,hij,he]
  obtain ⟨p,hp⟩ := first_exists (valid step q) (pairs e.elems.length)
    ⟨(i,j),(pairs_mem _ _ _).mpr ⟨by omega,hj⟩,hv⟩
  have hs := first_sound _ _ p hp
  rcases p with ⟨a,b⟩
  have hm := (pairs_mem _ _ _).mp hs.1
  have hh : a<b ∧ orbit step q a=orbit step q b := by
    simpa only [valid,Bool.and_eq_true,decide_eq_true_eq] using hs.2
  exact ⟨a,b,hp,hh.1,hm.2,hh.2⟩

structure Descriptor where
  threshold : Nat
  period : Nat
  initialCounts : List Nat
  residues : List Nat
  deriving Repr

def Descriptor.test (D : Descriptor) (k : Nat) : Bool :=
  if k<D.threshold then decide (k∈D.initialCounts)
  else decide ((k-D.threshold)%D.period∈D.residues)

def describe (step : S→S) (q : S) (accept : S→Bool) (i j : Nat) : Descriptor :=
  ⟨i,j-i,(List.range i).filter (fun k=>accept (orbit step q k)),
    (List.range (j-i)).filter (fun r=>accept (orbit step q (i+r)))⟩

theorem describe_correct (step : S→S) (q : S) (accept : S→Bool)
    (i j k : Nat) (hij : i<j) (he : orbit step q i=orbit step q j) :
    (describe step q accept i j).test k=true ↔ accept (orbit step q k)=true := by
  by_cases hk : k<i
  · simp [Descriptor.test,describe,hk]
  · have hle : i≤k := by omega
    have hr : (k-i)%(j-i)<j-i := Nat.mod_lt _ (by omega)
    have hn := orbit_normal step q i j k hij he hle
    simp only [Descriptor.test,describe,hk,if_false,decide_eq_true_eq,List.mem_filter,
      List.mem_range,hr,true_and]
    rw [← hn]

def compress [DecidableEq S] (e : Enumeration S) (step : S→S)
    (q : S) (accept : S→Bool) : Option Descriptor :=
  (findCycle e step q).map (fun p=>describe step q accept p.1 p.2)

/-- The descriptor is always produced. It is bounded by the number of
    states and represents the complete infinite set of accepted counts. -/
theorem compress_spec [DecidableEq S] (e : Enumeration S) (step : S→S)
    (q : S) (accept : S→Bool) :
    ∃ D,compress e step q accept=some D ∧ 0<D.period ∧
      D.threshold+D.period≤e.elems.length ∧
      (∀ r,r∈D.residues→r<D.period) ∧
      (∀ k,D.test k=true ↔ accept (orbit step q k)=true) := by
  obtain ⟨i,j,hf,hij,hj,he⟩ := findCycle_spec e step q
  refine ⟨describe step q accept i j,?_,?_,?_,?_,?_⟩
  · simp only [compress,hf,Option.map]
  · change 0<j-i
    omega
  · change i+(j-i)≤e.elems.length
    omega
  · intro r hr
    have h := (List.mem_filter.mp hr).1
    exact List.mem_range.mp h
  · intro k
    exact describe_correct step q accept i j k hij he

/-- The infinite tail is exactly a finite union of arithmetic
    progressions of common positive step. -/
theorem descriptor_ap (D : Descriptor) (hp : 0<D.period)
    (hr : ∀ r,r∈D.residues→r<D.period) (k : Nat) :
    D.test k=true ↔
      (k<D.threshold ∧ k∈D.initialCounts) ∨
      ∃ r,r∈D.residues ∧ ∃ m,k=D.threshold+r+m*D.period := by
  by_cases hk : k<D.threshold
  · simp only [Descriptor.test,hk,if_true,decide_eq_true_eq,true_and]
    constructor
    · exact Or.inl
    · rintro (h|⟨r,hm,m,he⟩)
      · exact h
      · omega
  · have hle : D.threshold≤k := by omega
    simp only [Descriptor.test,hk,if_false,decide_eq_true_eq,false_and,false_or]
    constructor
    · intro hm
      let r := (k-D.threshold)%D.period
      let m := (k-D.threshold)/D.period
      refine ⟨r,hm,m,?_⟩
      have he := Nat.mod_add_div (k-D.threshold) D.period
      change r+D.period*m=k-D.threshold at he
      rw [Nat.mul_comm D.period m] at he
      omega
    · rintro ⟨r,hm,m,he⟩
      have hsub : k-D.threshold=r+m*D.period := by omega
      have hmod : (r+m*D.period)%D.period=r := by
        rw [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,Nat.add_zero,
          Nat.mod_mod,Nat.mod_eq_of_lt (hr r hm)]
      rwa [hsub,hmod]

end REWB.FiniteOrbit

namespace REWB.Periodic
open FiniteOrbit
variable {α : Type}

theorem run_repeat (d : DFA α) (u : Word α) (q : Fin d.stateCount) (k : Nat) :
    d.run q (repeatWord u k)=orbit (fun s=>d.run s u) q k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [repeatWord,DFA.run_append,ih]
    rfl

def factorDescriptor (d : DFA α) (f : Nat→α) (a p rho : Nat) :
    Option Descriptor :=
  compress (FiniteRelation.finEnum d.stateCount)
    (fun s=>d.run s (segment f a p)) d.initial
    (fun s=>d.final (d.run s (segment f a rho)))

/-- For a fixed starting phase and residual length, the legal repetition
    counts form an exactly represented ultimately periodic set. The
    interval-length constraint is kept separate from DFA acceptance. -/
theorem factorDescriptor_spec (d : DFA α) (f : Nat→α) (n a p rho : Nat)
    (h : Period f n p) :
    ∃ D,factorDescriptor d f a p rho=some D ∧ 0<D.period ∧
      D.threshold+D.period≤d.stateCount ∧
      (∀ r,r∈D.residues→r<D.period) ∧
      (∀ k,a+k*p+rho≤n →
        (D.test k=true ↔ d.accepts (segment f a (k*p+rho)))) := by
  obtain ⟨D,hD,hp,hb,hr,hc⟩ := compress_spec (FiniteRelation.finEnum d.stateCount)
    (fun s=>d.run s (segment f a p)) d.initial
    (fun s=>d.final (d.run s (segment f a rho)))
  refine ⟨D,hD,hp,?_,hr,?_⟩
  · simpa [FiniteRelation.finEnum] using hb
  · intro k hk
    have he : segment f a (k*p+rho)=repeatWord (segment f a p) k++segment f a rho := by
      rw [segment_append,segment_repeated h a k (by omega),
        ← segment_same_phase h a k rho hk]
    rw [he,DFA.accepts,DFA.run_append,run_repeat]
    exact hc k

end REWB.Periodic
