import REWB.MaskedThresholdQueue

namespace REWB.MaskedThresholdQueue
variable {α : Type}

structure Taken (α : Type) where
  item : Option (Entry α)
  rest : Tree α
  work : Nat
  deriving Repr

def takeMax : Nat → Tree α → Taken α
  | h,t =>
    if count t=0 then ⟨none,t,2⟩ else
    match h with
    | 0 => match bucketValues t with
      | [] => ⟨none,t,4⟩
      | x::xs => ⟨some x,.bucket (count t-1) xs,6⟩
    | h+1 =>
      if 0<count (right t) then
        let found:=takeMax h (right t)
        ⟨found.item,join (left t) found.rest,found.work+10⟩
      else
        let found:=takeMax h (left t)
        ⟨found.item,join found.rest (right t),found.work+10⟩

def Removal (before : Tree α) (out : Taken α) : Prop :=
  match out.item with
  | none => entries before=[] ∧ out.rest=before
  | some x => (x::entries out.rest).Perm (entries before) ∧
      count out.rest+1=count before ∧ ∀y,y∈entries before → y.key≤x.key

theorem empty_of_count (h lo : Nat) (t : Tree α) (hg : Good h lo t) (hz : count t=0) :
    entries t=[] := List.length_eq_zero_iff.mp ((good_count h lo t hg).symm.trans hz)

theorem takeMax_spec (h lo : Nat) (t : Tree α) (hg : Good h lo t) :
    Good h lo (takeMax h t).rest ∧ Removal t (takeMax h t) ∧ (takeMax h t).work≤10*h+6 := by
  induction h generalizing lo t with
  | zero =>
    by_cases hz : count t=0
    · simp only [takeMax,if_pos hz]
      exact ⟨hg,⟨empty_of_count _ _ _ hg hz,rfl⟩,by omega⟩
    · have ht:=good_zero lo t hg
      cases hs : bucketValues t with
      | nil =>
        rw [hs] at ht
        exact False.elim (hz ht.1)
      | cons x xs =>
        have hc : count t=xs.length+1 := by simpa only [hs,List.length_cons] using ht.1
        have hk : ∀y,y∈x::xs → y.key=lo := by simpa only [hs] using ht.2.2
        have he : entries t=x::xs := ht.2.1.trans hs
        simp only [takeMax,if_neg hz,hs,Removal]
        refine ⟨⟨by omega,fun y hy=>hk y (List.mem_cons_of_mem x hy)⟩,
          ?_,by omega⟩
        refine ⟨by rw [entries,he],?_,?_⟩
        · change count t-1+1=count t
          omega
        · intro y hy
          have hy':=hk y (by rwa [he] at hy)
          have hx:=hk x List.mem_cons_self
          omega
  | succ h ih =>
    by_cases hz : count t=0
    · simp only [takeMax,if_pos hz]
      exact ⟨hg,⟨empty_of_count _ _ _ hg hz,rfl⟩,by omega⟩
    · have hc:=good_children h lo t hg
      by_cases hr : 0<count (right t)
      · have ht:=ih (lo+2^h) (right t) hc.2.1
        cases he : (takeMax h (right t)).item with
        | none =>
          have hm:=ht.2.1
          simp only [Removal,he] at hm
          have hh:=good_count h (lo+2^h) (right t) hc.2.1
          rw [hm.1] at hh
          simp only [List.length_nil] at hh
          omega
        | some x =>
          have hm:=ht.2.1
          simp only [Removal,he] at hm
          have hx : x∈entries (right t) := hm.1.mem_iff.mp List.mem_cons_self
          have hxb:=good_bounds h (lo+2^h) (right t) hc.2.1 x hx
          simp only [takeMax,if_neg hz,if_pos hr]
          refine ⟨join_good h lo _ _ hc.1 ht.1,?_,by have hh:=ht.2.2; omega⟩
          simp only [Removal,he]
          refine ⟨?_,?_,?_⟩
          · change (x::(entries (left t)++entries (takeMax h (right t)).rest)).Perm (entries t)
            rw [hc.2.2.2]
            exact List.perm_middle.symm.trans (hm.1.append_left (entries (left t)))
          · change count (left t)+count (takeMax h (right t)).rest+1=count t
            rw [hc.2.2.1]
            have hh:=hm.2.1
            omega
          · intro y hy
            rw [hc.2.2.2,List.mem_append] at hy
            rcases hy with hy|hy
            · have hyb:=good_bounds h lo (left t) hc.1 y hy
              omega
            · exact hm.2.2 y hy
      · have hl : 0<count (left t) := by have hh:=hc.2.2.1; omega
        have ht:=ih lo (left t) hc.1
        have hright : entries (right t)=[] := empty_of_count h (lo+2^h) (right t) hc.2.1 (by omega)
        cases he : (takeMax h (left t)).item with
        | none =>
          have hm:=ht.2.1
          simp only [Removal,he] at hm
          have hh:=good_count h lo (left t) hc.1
          rw [hm.1] at hh
          simp only [List.length_nil] at hh
          omega
        | some x =>
          have hm:=ht.2.1
          simp only [Removal,he] at hm
          simp only [takeMax,if_neg hz,if_neg hr]
          refine ⟨join_good h lo _ _ ht.1 hc.2.1,?_,by have hh:=ht.2.2; omega⟩
          simp only [Removal,he]
          refine ⟨?_,?_,?_⟩
          · change (x::(entries (takeMax h (left t)).rest++entries (right t))).Perm (entries t)
            rw [hc.2.2.2]
            simpa only [List.cons_append] using hm.1.append_right (entries (right t))
          · change count (takeMax h (left t)).rest+count (right t)+1=count t
            rw [hc.2.2.1]
            have hh:=hm.2.1
            omega
          · intro y hy
            rw [hc.2.2.2,hright,List.append_nil] at hy
            exact hm.2.2 y hy

theorem takeMax_none (h lo : Nat) (t : Tree α) (hg : Good h lo t) :
    (takeMax h t).item=none ↔ count t=0 := by
  constructor
  · intro he
    have hh:=(takeMax_spec h lo t hg).2.1
    simp only [Removal,he] at hh
    rw [good_count h lo t hg,hh.1]
    rfl
  · intro hz
    cases h <;> simp only [takeMax,if_pos hz]

end REWB.MaskedThresholdQueue
