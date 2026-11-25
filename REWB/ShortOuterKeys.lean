import REWB.P1ShortSources
import REWB.ArrayText

/-! A direct array of exact identifiers for every factor of length below
the short-outer threshold.  The rectangular array also has unused cells
whose endpoint is outside the text; these are harmless padded keys and
are never used as bounded factors.  No list of all endpoint pairs and no
substring comparison occurs in a query.  Each constructed key is charged
for its actual letters as well as exact-trie interning work. -/
namespace REWB.ShortOuter.Keys
open REWB.Periodic
variable {σ : Nat}

structure State (σ : Nat) where
  registry : ExactKeys.Registry σ
  ranks : Array Nat
  work : Nat

/-- Consuming the state constructor before the push allows the compiled
loop to extend the unique array instead of copying its accumulated prefix. -/
def loop (f : Nat→Fin σ) (width : Nat) : Nat→State σ→State σ
  | 0,st => st
  | fuel+1,⟨registry,ranks,work⟩ =>
    let slot:=ranks.size
    let len:=slot%width
    let assigned:=ExactKeys.assign registry (segment f (slot/width) len)
    loop f width fuel ⟨assigned.registry,ranks.push assigned.rank,
      work+assigned.work+2*len+8⟩

def Good (f : Nat→Fin σ) (width : Nat) (st : State σ) : Prop :=
  st.registry.Valid ∧
  ∀ j, j<st.ranks.size →
    ExactKeys.lookup st.registry.tree (segment f (j/width) (j%width))=
      some (st.ranks[j]?.getD 0)

theorem push_good (f : Nat→Fin σ) (width : Nat) (st : State σ) (h : Good f width st) :
    Good f width
      ⟨(ExactKeys.assign st.registry (segment f (st.ranks.size/width) (st.ranks.size%width))).registry,
       st.ranks.push (ExactKeys.assign st.registry
         (segment f (st.ranks.size/width) (st.ranks.size%width))).rank,
       st.work+(ExactKeys.assign st.registry
         (segment f (st.ranks.size/width) (st.ranks.size%width))).work+2*(st.ranks.size%width)+8⟩ := by
  refine ⟨ExactKeys.assign_valid _ h.1 _,?_⟩
  intro j hj
  simp only [Array.size_push] at hj
  rw [Array.getElem?_push]
  by_cases he : j=st.ranks.size
  · subst j
    rw [if_pos rfl]
    exact ExactKeys.assign_lookup _ _
  · rw [if_neg he]
    exact ExactKeys.assign_preserves _ _ _ _ (h.2 j (by omega))

theorem loop_good (f : Nat→Fin σ) (width fuel : Nat) (st : State σ)
    (h : Good f width st) : Good f width (loop f width fuel st) := by
  induction fuel generalizing st with
  | zero => exact h
  | succ fuel ih =>
    cases st with
    | mk registry ranks work =>
      rw [loop]
      exact ih _ (push_good f width _ h)

theorem loop_size (f : Nat→Fin σ) (width fuel : Nat) (st : State σ) :
    (loop f width fuel st).ranks.size=st.ranks.size+fuel := by
  induction fuel generalizing st with
  | zero => simp [loop]
  | succ fuel ih =>
    cases st
    rw [loop,ih]
    simp only [Array.size_push]
    omega

theorem loop_next (f : Nat→Fin σ) (width fuel : Nat) (st : State σ) :
    (loop f width fuel st).registry.next≤st.registry.next+fuel := by
  induction fuel generalizing st with
  | zero => simp [loop]
  | succ fuel ih =>
    cases st with
    | mk registry ranks work =>
      rw [loop]
      have hi:=ih (⟨(ExactKeys.assign registry (segment f (ranks.size/width) (ranks.size%width))).registry,
        ranks.push (ExactKeys.assign registry (segment f (ranks.size/width) (ranks.size%width))).rank,
        work+(ExactKeys.assign registry (segment f (ranks.size/width) (ranks.size%width))).work+
          2*(ranks.size%width)+8⟩ : State σ)
      have ha:=ExactKeys.intern_next_le (segment f (ranks.size/width) (ranks.size%width))
        registry.tree registry.next
      change (ExactKeys.assign registry _).registry.next≤registry.next+1 at ha
      exact Nat.le_trans hi (by dsimp; omega)

def stepBudget (σ width : Nat) : Nat := (3*σ+3)*width+9

theorem loop_work (f : Nat→Fin σ) (width fuel : Nat) (hw : 0<width) (st : State σ) :
    (loop f width fuel st).work≤st.work+fuel*stepBudget σ width := by
  induction fuel generalizing st with
  | zero => simp [loop]
  | succ fuel ih =>
    cases st with
    | mk registry ranks work =>
      rw [loop]
      apply Nat.le_trans (ih _)
      have ha:=ExactKeys.intern_cost (segment f (ranks.size/width) (ranks.size%width))
        registry.tree registry.next
      rw [segment_length] at ha
      change (ExactKeys.assign registry _).work≤(3*σ+1)*(ranks.size%width)+1 at ha
      have hm:=Nat.mod_lt ranks.size hw
      have hh:=Nat.mul_le_mul_left (3*σ+3) (Nat.le_of_lt hm)
      simp only [Nat.add_mul,Nat.one_mul] at ha hh
      simp only [stepBudget,Nat.add_mul,Nat.one_mul]
      omega

structure Index (σ : Nat) where
  length : Nat
  width : Nat
  registry : ExactKeys.Registry σ
  ranks : Array Nat
  work : Nat

def build (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) : Index σ :=
  let n:=text.size
  let width:=min limit (n+1)
  let st:=loop (ArrayText.read text fallback) width ((n+1)*width)
    ⟨ExactKeys.initial,#[],0⟩
  ⟨n,width,st.registry,st.ranks,st.work+4⟩

def get (idx : Index σ) (p len : Nat) : Nat :=
  idx.ranks[p*idx.width+len]?.getD 0

@[simp] theorem build_length (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (build text fallback limit).length=text.size := rfl

@[simp] theorem build_width (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (build text fallback limit).width=min limit (text.size+1) := rfl

theorem build_good (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    Good (ArrayText.read text fallback) (min limit (text.size+1))
      ⟨(build text fallback limit).registry,(build text fallback limit).ranks,
        (build text fallback limit).work⟩ := by
  have h:=loop_good (ArrayText.read text fallback) (min limit (text.size+1))
    ((text.size+1)*min limit (text.size+1))
    ⟨ExactKeys.initial,#[],0⟩ ⟨ExactKeys.initial_valid,by intro j hj; simp at hj⟩
  exact h

theorem build_size (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (build text fallback limit).ranks.size=(text.size+1)*min limit (text.size+1) := by
  simp only [build,loop_size,Array.size_empty,Nat.zero_add]

theorem build_next (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (build text fallback limit).registry.next≤(text.size+1)*min limit (text.size+1) := by
  simpa only [build,ExactKeys.initial,Nat.zero_add] using
    loop_next (ArrayText.read text fallback) (min limit (text.size+1))
      ((text.size+1)*min limit (text.size+1)) ⟨ExactKeys.initial,#[],0⟩

theorem slot_bound (n width p len : Nat) (hp : p≤n) (hl : len<width) :
    p*width+len<(n+1)*width := by
  have h1:=Nat.add_lt_add_left hl (p*width)
  have h2:=Nat.mul_le_mul_right width (show p+1≤n+1 by omega)
  rw [Nat.add_mul,Nat.one_mul] at h2
  omega

theorem slot_div (width p len : Nat) (hl : len<width) :
    (p*width+len)/width=p := by
  rw [Nat.mul_comm p width,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hl,Nat.add_zero]

theorem slot_mod (width p len : Nat) (hl : len<width) :
    (p*width+len)%width=len := by
  rw [Nat.mul_comm p width,Nat.mul_add_mod,Nat.mod_eq_of_lt hl]

theorem get_lookup (text : Array (Fin σ)) (fallback : Fin σ) (limit p len : Nat)
    (hp : p≤text.size) (hl : len<min limit (text.size+1)) :
    ExactKeys.lookup (build text fallback limit).registry.tree
      (segment (ArrayText.read text fallback) p len)=
      some (get (build text fallback limit) p len) := by
  have hh:=(build_good text fallback limit).2 (p*min limit (text.size+1)+len)
    (by rw [build_size]; exact slot_bound _ _ _ _ hp hl)
  rwa [slot_div _ _ _ hl,slot_mod _ _ _ hl] at hh

theorem get_bound (text : Array (Fin σ)) (fallback : Fin σ) (limit p len : Nat)
    (hp : p≤text.size) (hl : len<min limit (text.size+1)) :
    get (build text fallback limit) p len<(build text fallback limit).registry.next :=
  (build_good text fallback limit).1.1 _ _ (get_lookup text fallback limit p len hp hl)

theorem get_eq_iff (text : Array (Fin σ)) (fallback : Fin σ) (limit p q len : Nat)
    (hp : p≤text.size) (hq : q≤text.size) (hl : len<min limit (text.size+1)) :
    get (build text fallback limit) p len=get (build text fallback limit) q len ↔
      segment (ArrayText.read text fallback) p len=segment (ArrayText.read text fallback) q len :=
  ExactKeys.rank_eq_iff _ (build_good text fallback limit).1 _ _ _ _
    (get_lookup text fallback limit p len hp hl) (get_lookup text fallback limit q len hq hl)

theorem get_eq_general (text : Array (Fin σ)) (fallback : Fin σ) (limit p q len other : Nat)
    (hp : p≤text.size) (hq : q≤text.size)
    (hl : len<min limit (text.size+1)) (ho : other<min limit (text.size+1)) :
    get (build text fallback limit) p len=get (build text fallback limit) q other ↔
      segment (ArrayText.read text fallback) p len=segment (ArrayText.read text fallback) q other :=
  ExactKeys.rank_eq_iff _ (build_good text fallback limit).1 _ _ _ _
    (get_lookup text fallback limit p len hp hl) (get_lookup text fallback limit q other hq ho)

theorem build_work (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (build text fallback limit).work≤
      ((text.size+1)*min limit (text.size+1))*stepBudget σ (min limit (text.size+1))+4 := by
  by_cases hw : min limit (text.size+1)=0
  · simp [build,hw,loop]
  · have hh:=loop_work (ArrayText.read text fallback) (min limit (text.size+1))
      ((text.size+1)*min limit (text.size+1)) (by omega) ⟨ExactKeys.initial,#[],0⟩
    change _+4≤_
    simpa only [Nat.zero_add] using Nat.add_le_add_right hh 4

end REWB.ShortOuter.Keys
