import REWB.MaskedRunCatalog

/-! Exact run IDs and immutable target-count identity for the actual
array-fold catalog builder. Distinct bounded run triples have distinct
fixed-width keys; every returned ID addresses the original run array. -/
namespace REWB.MaskedRunCatalog
open REWB.RunGeometry REWB.ExactKeys
open REWB.MaskedPeriodic.Batch (span totalSpan)

/-- A proof-only correspondence between sparse keys and stored entries. -/
def Good (n h : Nat) (out : Acc) : Prop :=
  ∀R id,RunDedup.Bounded n R→
    (ExactKeys.lookup out.tree (RunDedup.key h R)=some id ↔
      (out.entries[id]?).map Entry.run=some R)

theorem initial_good (n h : Nat) : Good n h {} := by
  intro R id _
  rw [show ({} : Acc).tree=ExactKeys.empty from rfl,ExactKeys.lookup_empty]
  simp only [show ({} : Acc).entries=#[] from rfl,Array.getElem?_empty,Option.map_none',reduceCtorEq]

theorem run_mem_of_get (entries : Array Entry) (id : Nat) (R : Bounds)
    (he : (entries[id]?).map Entry.run=some R) : R∈entries.toList.map Entry.run := by
  apply List.mem_of_getElem? (i:=id)
  simpa only [List.getElem?_map,Array.getElem?_toList] using he

theorem step_good (n h : Nat) (target : Array Bool) (K : Nat) (out : Acc) (R : Bounds)
    (hn : n<2^h) (hg : Good n h out) (hR : RunDedup.Bounded n R)
    (hf : R∉out.entries.toList.map Entry.run) : Good n h (step target K h out R) := by
  intro S id hS
  simp only [step_tree,Map.put_lookup,RunDedup.key_exact h n S R hn hS hR,step_entries]
  by_cases he : S=R
  · subst S
    by_cases hi : id=out.entries.size
    · subst id
      simp only [if_pos rfl,ite_true,Array.getElem?_push_eq,Option.map_some',entry]
    · have hx : (out.entries[id]?).map Entry.run≠some R := fun hh=>hf (run_mem_of_get _ _ _ hh)
      simp only [if_pos rfl,ite_true,Option.some.injEq,Ne.symm hi,Array.getElem?_push,if_neg hi,hx]
  · rw [if_neg he,hg S id hS,Array.getElem?_push]
    by_cases hi : id=out.entries.size
    · subst id
      rw [if_pos rfl,Array.getElem?_eq_none (Nat.le_refl _)]
      simp only [Option.map_none',Option.map_some',entry,Option.some.injEq,Ne.symm he,reduceCtorEq]
    · rw [if_neg hi]

theorem fold_good (n h : Nat) (target : Array Bool) (K : Nat) (Rs : List Bounds) (out : Acc)
    (hn : n<2^h) (hg : Good n h out)
    (hb : ∀R,R∈Rs→RunDedup.Bounded n R)
    (hd : (out.entries.toList.map Entry.run++Rs).Nodup) :
    Good n h (Rs.foldl (step target K h) out) := by
  induction Rs generalizing out with
  | nil => exact hg
  | cons R Rs ih =>
    have hf : R∉out.entries.toList.map Entry.run := by
      intro hm
      exact (List.pairwise_append.mp hd).2.2 R hm R List.mem_cons_self rfl
    rw [List.foldl_cons]
    apply ih (step target K h out R) (step_good n h target K out R hn hg (hb R List.mem_cons_self) hf)
      (fun S hS=>hb S (List.mem_cons_of_mem _ hS))
    simpa only [step_entries,Array.push_toList,List.map_append,List.map_cons,List.map_nil,
      entry,List.append_assoc,List.singleton_append] using hd

@[simp] theorem build_length (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) :
    (build n target K runs).length=n := rfl
@[simp] theorem build_width (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) :
    (build n target K runs).width=width n := rfl
@[simp] theorem build_modulus (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) :
    (build n target K runs).modulus=K := rfl
@[simp] theorem build_runs (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) :
    (build n target K runs).runs=runs := rfl

theorem build_map (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds)
    (hb : ∀R,R∈runs.toList→RunDedup.Bounded n R) (hd : runs.toList.Nodup)
    (R : Bounds) (id : Nat) (hR : RunDedup.Bounded n R) :
    ExactKeys.lookup (build n target K runs).tree (RunDedup.key (width n) R)=some id ↔
      runs[id]?=some R := by
  have hh:=fold_good n (width n) target K runs.toList {} (width_capacity n) (initial_good _ _) hb
    (by simpa only [Array.toList_empty,List.map_nil,List.nil_append] using hd)
  have hm:=hh R id hR
  rw [Array.foldl_toList] at hm
  have he : ((build n target K runs).entries[id]?).map Entry.run=runs[id]? := by
    rw [build_get]
    cases runs[id]? <;> rfl
  change ExactKeys.lookup (build n target K runs).tree (RunDedup.key (width n) R)=some id ↔
    ((build n target K runs).entries[id]?).map Entry.run=some R at hm
  rw [he] at hm
  exact hm

theorem lookupId_correct (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds)
    (hb : ∀R,R∈runs.toList→RunDedup.Bounded n R) (hd : runs.toList.Nodup) (R : Bounds) (id : Nat) :
    (lookupId (build n target K runs) R).1=some id ↔ runs[id]?=some R := by
  by_cases hR : RunDedup.Bounded n R
  · have hR' : R.lo≤n ∧ R.hi≤n ∧ R.period≤n := hR
    simp only [lookupId,build_length,build_width,if_pos hR',Map.read_value,Map.key_value]
    exact build_map n target K runs hb hd R id hR
  · have hn : ¬(R.lo≤n ∧ R.hi≤n ∧ R.period≤n) := hR
    simp only [lookupId,build_length,if_neg hn,reduceCtorEq,false_iff]
    intro he
    exact hR (hb R (List.mem_of_getElem? (by simpa only [Array.getElem?_toList] using he)))

theorem lookup_found (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds)
    (hb : ∀R,R∈runs.toList→RunDedup.Bounded n R) (hd : runs.toList.Nodup)
    (R : Bounds) (id : Nat) (value : Entry) :
    (lookup (build n target K runs) R).1=some ⟨id,value⟩ ↔
      runs[id]?=some R ∧ value=entry target K R := by
  unfold lookup
  dsimp only
  cases ho : (lookupId (build n target K runs) R).1 with
  | none =>
    simp only [ho,reduceCtorEq,false_iff]
    rintro ⟨hr,_⟩
    have hi:=(lookupId_correct n target K runs hb hd R id).mpr hr
    rw [ho] at hi
    contradiction
  | some actual =>
    have ha:=(lookupId_correct n target K runs hb hd R actual).mp ho
    simp only [ho,build_get,ha,Option.map_some',Option.some.injEq,Found.mk.injEq]
    constructor
    · rintro ⟨rfl,hv⟩
      exact ⟨ha,hv.symm⟩
    · rintro ⟨hid,hv⟩
      have hh:=(lookupId_correct n target K runs hb hd R id).mpr hid
      have he : actual=id := Option.some.inj (ho.symm.trans hh)
      exact ⟨he,hv.symm⟩

theorem lookup_complete (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds)
    (hb : ∀R,R∈runs.toList→RunDedup.Bounded n R) (hd : runs.toList.Nodup)
    (R : Bounds) (id : Nat) (hr : runs[id]?=some R) :
    (lookup (build n target K runs) R).1=some ⟨id,entry target K R⟩ :=
  (lookup_found n target K runs hb hd R id _).mpr ⟨hr,rfl⟩

end REWB.MaskedRunCatalog
