import REWB.BoundaryTrieSort

/-! Binary search for the end of a true prefix in a half-open interval.
Only the midpoint is probed at each step. Predicate work is accumulated
from each actual call; the loop adds eight scalar slots per probe and
one final return slot. The initial fuel is computed once. -/
namespace REWB.BoundaryTrie.Search

structure Result where
  split : Nat
  probes : Nat
  work : Nat
  deriving Repr

def go (p : Nat→Bool×Nat) : Nat→Nat→Nat→Result
  | 0,lo,_ => ⟨lo,0,1⟩
  | h+1,lo,hi =>
    if lo<hi then
      let mid:=lo+(hi-lo)/2
      let c:=p mid
      let r:=if c.1 then go p h (mid+1) hi else go p h lo mid
      ⟨r.split,r.probes+1,r.work+c.2+8⟩
    else ⟨lo,0,1⟩

def Prefix (p : Nat→Bool×Nat) (lo hi : Nat) : Prop :=
  ∀ i j,lo≤i→i≤j→j<hi→(p j).1=true→(p i).1=true

def Split (p : Nat→Bool×Nat) (lo hi s : Nat) : Prop :=
  lo≤s ∧ s≤hi ∧ ∀ j,lo≤j→j<hi→((p j).1=true↔j<s)

theorem prefix_sub (p : Nat→Bool×Nat) (lo hi a b : Nat)
    (hp : Prefix p lo hi) (ha : lo≤a) (hb : b≤hi) : Prefix p a b := by
  intro i j hai hij hjb ht
  exact hp i j (by omega) hij (by omega) ht

theorem mid_bounds (lo hi : Nat) (h : lo<hi) :
    lo≤lo+(hi-lo)/2 ∧ lo+(hi-lo)/2<hi := by omega

theorem half_fuel (lo hi h : Nat) (hlo : lo≤hi) (hh : hi-lo<2^(h+1)) :
    (lo+(hi-lo)/2)-lo<2^h ∧ hi-((lo+(hi-lo)/2)+1)<2^h := by
  rw [Nat.pow_succ] at hh
  omega

theorem go_bounds (p : Nat→Bool×Nat) (h lo hi : Nat) (hlo : lo≤hi) :
    lo≤(go p h lo hi).split ∧ (go p h lo hi).split≤hi := by
  induction h generalizing lo hi with
  | zero => exact ⟨Nat.le_refl _,hlo⟩
  | succ h ih =>
    rw [go]
    split
    · rename_i hn
      have hm:=mid_bounds lo hi hn
      dsimp only
      split
      · have hr:=ih (lo+(hi-lo)/2+1) hi (by omega)
        exact ⟨by omega,hr.2⟩
      · have hr:=ih lo (lo+(hi-lo)/2) hm.1
        exact ⟨hr.1,by omega⟩
    · exact ⟨Nat.le_refl _,hlo⟩

theorem go_correct (p : Nat→Bool×Nat) (h lo hi : Nat) (hlo : lo≤hi)
    (hh : hi-lo<2^h) (hp : Prefix p lo hi) :
    Split p lo hi (go p h lo hi).split := by
  induction h generalizing lo hi with
  | zero =>
    have he : lo=hi := by simp only [Nat.pow_zero] at hh; omega
    subst hi
    exact ⟨Nat.le_refl _,Nat.le_refl _,fun j hj hj' => by omega⟩
  | succ h ih =>
    by_cases hn : lo<hi
    · let mid:=lo+(hi-lo)/2
      have hm : lo≤mid ∧ mid<hi := mid_bounds lo hi hn
      have hf:=half_fuel lo hi h hlo hh
      change mid-lo<2^h ∧ hi-(mid+1)<2^h at hf
      rw [go,if_pos hn]
      change Split p lo hi
        (if (p mid).1 then go p h (mid+1) hi else go p h lo mid).split
      by_cases ht : (p mid).1=true
      · rw [if_pos ht]
        have hr:=ih (mid+1) hi (by omega) hf.2
          (prefix_sub p lo hi (mid+1) hi hp (by omega) (Nat.le_refl _))
        refine ⟨by have hh:=hr.1; omega,hr.2.1,?_⟩
        intro j hj hj'
        by_cases hjm : j≤mid
        · have hjt:=hp j mid hj hjm hm.2 ht
          constructor
          · intro _
            have hh:=hr.1
            omega
          · intro _
            exact hjt
        · exact hr.2.2 j (by omega) hj'
      · rw [if_neg ht]
        have hr:=ih lo mid hm.1 hf.1
          (prefix_sub p lo hi lo mid hp (Nat.le_refl _) (by omega))
        refine ⟨hr.1,by have hh:=hr.2.1; omega,?_⟩
        intro j hj hj'
        by_cases hjm : j<mid
        · exact hr.2.2 j hj hjm
        · constructor
          · intro hjt
            exact False.elim (ht (hp mid j hm.1 (by omega) hj' hjt))
          · intro hjs
            have hh:=hr.2.1
            omega
    · have he : lo=hi := by omega
      subst hi
      rw [go,if_neg (by omega : ¬lo<lo)]
      exact ⟨Nat.le_refl _,Nat.le_refl _,fun j hj hj' => by omega⟩

theorem go_probes (p : Nat→Bool×Nat) (h lo hi : Nat) :
    (go p h lo hi).probes≤h := by
  induction h generalizing lo hi with
  | zero => exact Nat.le_refl _
  | succ h ih =>
    rw [go]
    split
    · dsimp only
      split
      · exact Nat.add_le_add_right (ih _ _) 1
      · exact Nat.add_le_add_right (ih _ _) 1
    · exact Nat.zero_le _

theorem go_work (p : Nat→Bool×Nat) (C : Nat) (hc : ∀ i,(p i).2≤C)
    (h lo hi : Nat) : (go p h lo hi).work≤(C+8)*h+1 := by
  induction h generalizing lo hi with
  | zero => simp [go]
  | succ h ih =>
    rw [go]
    split
    · have hm:=hc (lo+(hi-lo)/2)
      dsimp only
      split
      · have hr:=ih (lo+(hi-lo)/2+1) hi
        rw [Nat.mul_add,Nat.mul_one]
        omega
      · have hr:=ih lo (lo+(hi-lo)/2)
        rw [Nat.mul_add,Nat.mul_one]
        omega
    · exact Nat.le_add_left 1 _

/-- Setup adds three scalar slots for the initial length, logarithm,
and fuel increment. No logarithm or power is computed inside `go`. -/
def run (p : Nat→Bool×Nat) (lo hi : Nat) : Result :=
  let r:=go p ((hi-lo).log2+1) lo hi
  ⟨r.split,r.probes,r.work+3⟩

theorem run_bounds (p : Nat→Bool×Nat) (lo hi : Nat) (hlo : lo≤hi) :
    lo≤(run p lo hi).split ∧ (run p lo hi).split≤hi := go_bounds p _ lo hi hlo

theorem run_correct (p : Nat→Bool×Nat) (lo hi : Nat) (hlo : lo≤hi)
    (hp : Prefix p lo hi) : Split p lo hi (run p lo hi).split :=
  go_correct p _ lo hi hlo (Nat.lt_log2_self (n:=hi-lo)) hp

theorem run_probes (p : Nat→Bool×Nat) (lo hi : Nat) :
    (run p lo hi).probes≤(hi-lo).log2+1 := go_probes p _ lo hi

theorem run_work (p : Nat→Bool×Nat) (C : Nat) (hc : ∀ i,(p i).2≤C)
    (lo hi : Nat) :
    (run p lo hi).work≤(C+8)*((hi-lo).log2+1)+4 := by
  have hh:=go_work p C hc ((hi-lo).log2+1) lo hi
  change (go p ((hi-lo).log2+1) lo hi).work+3≤_
  omega

/-- This adapter performs one actual array read per predicate probe.
The fallback is never used when the requested interval is in bounds. -/
def probeArray {α : Type} (xs : Array α) (fallback : α)
    (test : α→Bool×Nat) (i : Nat) : Bool×Nat :=
  let c:=test (xs[i]?.getD fallback)
  (c.1,c.2+1)

theorem probeArray_in_bounds {α : Type} (xs : Array α) (fallback : α)
    (test : α→Bool×Nat) (i : Nat) (hi : i<xs.size) :
    probeArray xs fallback test i=((test xs[i]).1,(test xs[i]).2+1) := by
  simp only [probeArray,Array.getElem?_eq_getElem hi,Option.getD_some]

def array {α : Type} (xs : Array α) (fallback : α)
    (test : α→Bool×Nat) (lo hi : Nat) : Result :=
  run (probeArray xs fallback test) lo hi

theorem array_correct {α : Type} (xs : Array α) (fallback : α)
    (test : α→Bool×Nat) (lo hi : Nat) (hlo : lo≤hi)
    (hp : Prefix (probeArray xs fallback test) lo hi) :
    Split (probeArray xs fallback test) lo hi (array xs fallback test lo hi).split :=
  run_correct _ lo hi hlo hp

theorem array_partition {α : Type} (xs : Array α) (fallback : α)
    (test : α→Bool×Nat) (lo hi : Nat) (hlo : lo≤hi) (hhi : hi≤xs.size)
    (hp : Prefix (probeArray xs fallback test) lo hi) :
    lo≤(array xs fallback test lo hi).split ∧
      (array xs fallback test lo hi).split≤hi ∧
      ∀ j,lo≤j→(hj : j<hi)→
        ((test (xs[j]'(by omega))).1=true↔j<(array xs fallback test lo hi).split) := by
  have hs:=array_correct xs fallback test lo hi hlo hp
  refine ⟨hs.1,hs.2.1,?_⟩
  intro j hj hj'
  have hh:=hs.2.2 j hj hj'
  rw [probeArray_in_bounds xs fallback test j (by omega)] at hh
  exact hh

theorem array_probes {α : Type} (xs : Array α) (fallback : α)
    (test : α→Bool×Nat) (lo hi : Nat) :
    (array xs fallback test lo hi).probes≤(hi-lo).log2+1 := run_probes _ lo hi

theorem array_work {α : Type} (xs : Array α) (fallback : α)
    (test : α→Bool×Nat) (C : Nat) (hc : ∀ a,(test a).2≤C) (lo hi : Nat) :
    (array xs fallback test lo hi).work≤(C+9)*((hi-lo).log2+1)+4 := by
  have hh:=run_work (probeArray xs fallback test) (C+1)
    (fun i=>Nat.add_le_add_right (hc _) 1) lo hi
  exact hh

end REWB.BoundaryTrie.Search
