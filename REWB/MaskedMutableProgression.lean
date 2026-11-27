import REWB.MaskedMutableProgressionKey
import REWB.MaskedOrderedSchedule

/-! A mutable-source progression index represented by persistent sparse
position trees. Construction reads each physical position once; the step
does not determine any loop bound. No target count array is modified.
All counters use the same unit Nat/array-access model as MaskedProgression.
The logarithm is charged once by a height-sized scalar allowance. -/
namespace REWB.MaskedMutableProgression
open MaskedOrdered

structure Index where
  base : Nat
  len : Nat
  step : Nat
  levels : Nat
  capacity : Nat
  tree : Tree levels
  deriving Repr

def Index.Valid (idx : Index) : Prop :=
  idx.capacity=2^idx.levels ∧ idx.tree.Good ∧ idx.tree.Fits 0 ∧
  ∀key,key∈idx.tree.entries→∃i,i<idx.len ∧ key=encode idx.len idx.step i

/-- Physical source membership in the current persistent version. -/
def Index.Live (idx : Index) (p : Nat) : Prop :=
  idx.base≤p ∧ p<idx.base+idx.len ∧
  encode idx.len idx.step (p-idx.base)∈idx.tree.entries

structure Built where
  index : Index
  work : Nat
  deriving Repr

def fill {h : Nat} (mask : Array Bool) (base len step capacity : Nat) :
    Nat→Nat→Tree h→Nat→Tree h×Nat
  | 0,_,t,work => (t,work+1)
  | remaining+1,i,t,work =>
    if MaskedProgression.readMask mask (base+i) then
      let r:=Tree.insert t capacity (encode len step i)
      fill mask base len step capacity remaining (i+1) r.1 (work+r.2+12)
    else fill mask base len step capacity remaining (i+1) t (work+5)

theorem fill_work {h : Nat} (mask : Array Bool) (base len step capacity remaining i : Nat)
    (t : Tree h) (work : Nat) :
    (fill mask base len step capacity remaining i t work).2≤
      work+remaining*(10*h+14)+1 := by
  induction remaining generalizing i t work with
  | zero => simp [fill]
  | succ remaining ih =>
    simp only [fill]
    split
    · have hh:=ih (i+1) (Tree.insert t capacity (encode len step i)).1
        (work+(Tree.insert t capacity (encode len step i)).2+12)
      have hw:=Tree.insert_work t capacity (encode len step i)
      rw [Nat.succ_mul]
      omega
    · have hh:=ih (i+1) t (work+5)
      rw [Nat.succ_mul]
      omega

theorem fill_good {h : Nat} (mask : Array Bool) (base len step capacity remaining i : Nat)
    (t : Tree h) (work : Nat) (hg : t.Good) :
    (fill mask base len step capacity remaining i t work).1.Good := by
  induction remaining generalizing i t work with
  | zero => exact hg
  | succ remaining ih =>
    simp only [fill]
    split
    · exact ih _ _ _ (Tree.insert_good t capacity _ hg)
    · exact ih _ _ _ hg

theorem fill_fits {h : Nat} (mask : Array Bool) (base len step capacity remaining i : Nat)
    (t : Tree h) (work : Nat) (hf : t.Fits 0) (hc : capacity=2^h)
    (hkeys : ∀j,j<len→encode len step j<2^h) (hr : i+remaining≤len) :
    (fill mask base len step capacity remaining i t work).1.Fits 0 := by
  induction remaining generalizing i t work with
  | zero => exact hf
  | succ remaining ih =>
    simp only [fill]
    split
    · exact ih _ _ _ (Tree.insert_fits t capacity _ hf hc (hkeys i (by omega))) (by omega)
    · exact ih _ _ _ hf (by omega)

theorem fill_mem {h : Nat} (mask : Array Bool) (base len step capacity remaining i : Nat)
    (t : Tree h) (work : Nat) (hf : t.Fits 0) (hc : capacity=2^h)
    (hkeys : ∀j,j<len→encode len step j<2^h) (hr : i+remaining≤len) (key : Nat) :
    key∈(fill mask base len step capacity remaining i t work).1.entries ↔
      key∈t.entries ∨ ∃j,i≤j ∧ j<i+remaining ∧
        MaskedProgression.readMask mask (base+j)=true ∧ key=encode len step j := by
  induction remaining generalizing i t work with
  | zero => simp [fill]; omega
  | succ remaining ih =>
    simp only [fill]
    split
    next hm =>
      rw [ih _ _ _ (Tree.insert_fits t capacity _ hf hc (hkeys i (by omega))) (by omega),
        Tree.insert_mem t capacity _ key hf hc (hkeys i (by omega))]
      constructor
      · rintro ((he|hold)|⟨j,hlo,hhi,hmask,he⟩)
        · exact Or.inr ⟨i,Nat.le_refl _,by omega,hm,he⟩
        · exact Or.inl hold
        · exact Or.inr ⟨j,by omega,by omega,hmask,he⟩
      · rintro (hold|⟨j,hlo,hhi,hmask,he⟩)
        · exact Or.inl (Or.inr hold)
        · by_cases hj : j=i
          · subst j; exact Or.inl (Or.inl he)
          · exact Or.inr ⟨j,by omega,by omega,hmask,he⟩
    next hm =>
      rw [ih _ _ _ hf (by omega)]
      constructor
      · rintro (hold|⟨j,hlo,hhi,hmask,he⟩)
        · exact Or.inl hold
        · exact Or.inr ⟨j,by omega,by omega,hmask,he⟩
      · rintro (hold|⟨j,hlo,hhi,hmask,he⟩)
        · exact Or.inl hold
        · have hj : j≠i := by intro he; subst j; exact hm hmask
          exact Or.inr ⟨j,by omega,by omega,hmask,he⟩

def buildAt (mask : Array Bool) (base len step h : Nat) : Built :=
  let c:=MaskedOrdered.capacity h
  let r:=fill mask base len step c.1 len 0 (.empty : Tree h) 0
  ⟨⟨base,len,step,h,c.1,r.1⟩,c.2+r.2+h+8⟩

def build (mask : Array Bool) (base len step : Nat) : Built :=
  buildAt mask base len step (height len)

theorem build_base (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).index.base=base := rfl
theorem build_len (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).index.len=len := rfl
theorem build_step (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).index.step=step := rfl
theorem build_levels (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).index.levels=height len := rfl

theorem build_mem (mask : Array Bool) (base len step key : Nat) :
    key∈(build mask base len step).index.tree.entries ↔
      ∃i,i<len ∧ MaskedProgression.readMask mask (base+i)=true ∧ key=encode len step i := by
  have hh:=fill_mem mask base len step (MaskedOrdered.capacity (height len)).1 len 0
    (.empty : Tree (height len)) 0 True.intro (MaskedOrdered.capacity_value _)
    (encode_capacity len step) (by omega) key
  simpa only [build,buildAt,Tree.entries,List.not_mem_nil,false_or,Nat.zero_add,Nat.zero_le,true_and] using hh

theorem build_valid (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).index.Valid := by
  refine ⟨MaskedOrdered.capacity_value _,?_,?_,?_⟩
  · exact fill_good mask base len step _ len 0 .empty 0 True.intro
  · exact fill_fits mask base len step _ len 0 .empty 0 True.intro
      (MaskedOrdered.capacity_value _) (encode_capacity len step) (by omega)
  · intro key hk
    obtain ⟨i,hi,_,he⟩:=(build_mem mask base len step key).mp hk
    exact ⟨i,hi,he⟩

theorem build_live (mask : Array Bool) (base len step p : Nat) :
    (build mask base len step).index.Live p ↔
      base≤p ∧ p<base+len ∧ MaskedProgression.readMask mask p=true := by
  change (base≤p ∧ p<base+len ∧ encode len step (p-base)∈
    (build mask base len step).index.tree.entries) ↔ _
  rw [build_mem]
  constructor
  · rintro ⟨hlo,hhi,i,hi,hm,he⟩
    have he':=encode_injective len step (p-base) i (by omega) hi he
    have hp : base+i=p := by omega
    exact ⟨hlo,hhi,by rw [hp] at hm; exact hm⟩
  · rintro ⟨hlo,hhi,hm⟩
    refine ⟨hlo,hhi,p-base,by omega,?_,rfl⟩
    simpa only [Nat.add_sub_of_le hlo] using hm

theorem build_work (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).work≤len*(10*height len+14)+2*height len+10 := by
  have hh:=fill_work mask base len step (MaskedOrdered.capacity (height len)).1 len 0
    (.empty : Tree (height len)) 0
  have hc:=MaskedOrdered.capacity_work (height len)
  simp only [build,buildAt]
  omega

end REWB.MaskedMutableProgression
