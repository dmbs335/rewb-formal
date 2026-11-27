import REWB.MaskedTraversalDirtyEvents
import REWB.MaskedTraversalBankReadySemantics

/-! Applying a deduplicated reset set uses two actual passes. First all
selected anchor slots are set to the current complete-class length.
Only then are the selected banks compiled, so every incoming predecessor
read observes the final anchor array. Retired leaders are cleared by the
same direct slot operation. No bank is built during an equal-depth merge.

This module implements the reset pass. Successor-only context refreshes
must retain their own anchor and run metadata; they are a separate pass,
not recursive resets of the successor chain. Completeness of the dirty
set and the global aggregate/frontier invariant remain separate proofs.
-/
namespace REWB.MaskedTraversalRepair
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalBankReady
variable {α : Type} {h h' n : Nat}

def anchorsLoop (L : Nat) : List Nat→Array (Option Nat)→Nat→Array (Option Nat)×Nat
  | [],anchors,work => (anchors,work+1)
  | p::ps,anchors,work => anchorsLoop L ps (resetAnchor anchors p L) (work+4)

theorem anchorsLoop_work (L : Nat) (ps : List Nat) (anchors : Array (Option Nat)) (work : Nat) :
    (anchorsLoop L ps anchors work).2=work+4*ps.length+1 := by
  induction ps generalizing anchors work with
  | nil => simp [anchorsLoop]
  | cons p ps ih => rw [anchorsLoop,ih,List.length_cons]; omega

theorem anchorsLoop_size (L : Nat) (ps : List Nat) (anchors : Array (Option Nat)) (work : Nat) :
    (anchorsLoop L ps anchors work).1.size=anchors.size := by
  induction ps generalizing anchors work with
  | nil => rfl
  | cons p ps ih => rw [anchorsLoop,ih]; exact Array.size_setIfInBounds

theorem read_reset (anchors : Array (Option Nat)) (first p L : Nat) :
    readAnchor (resetAnchor anchors first L) p L=
      if first=p then L else readAnchor anchors p L := by
  by_cases he : first=p
  · subst p
    simp only [if_pos rfl]
    by_cases hb : first<anchors.size
    · exact resetAnchor_read anchors first L hb
    · simp only [readAnchor,resetAnchor,Array.getElem?_setIfInBounds_self]
      rw [if_neg hb]
      rfl
  · simp only [if_neg he,readAnchor,resetAnchor,Array.getElem?_setIfInBounds_ne he]

theorem anchorsLoop_read (L : Nat) (ps : List Nat) (anchors : Array (Option Nat)) (work p : Nat) :
    readAnchor (anchorsLoop L ps anchors work).1 p L=
      if p∈ps then L else readAnchor anchors p L := by
  induction ps generalizing anchors work with
  | nil => simp [anchorsLoop]
  | cons q ps ih =>
    rw [anchorsLoop,ih,read_reset]
    by_cases hp : p∈ps <;> by_cases he : q=p <;> simp_all [eq_comm]

def banksLoop (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) : List Nat→Mutable.Store.State C E→Mutable.Store.State C E
  | [],st => {st with repairWork:=st.repairWork+1}
  | p::ps,st =>
    let next:=write C E book prepared ci ei partition capacity p current anchors window catalog classes target st
    banksLoop C E book prepared ci ei partition capacity current anchors window catalog classes target ps
      {next with repairWork:=next.repairWork+3}

theorem banksLoop_sources (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (ps : List Nat) (st : Mutable.Store.State C E) :
    (banksLoop C E book prepared ci ei partition capacity current anchors window catalog classes target ps st).sources=st.sources := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih => rw [banksLoop,ih]; rfl

theorem banksLoop_size (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (ps : List Nat) (st : Mutable.Store.State C E) :
    (banksLoop C E book prepared ci ei partition capacity current anchors window catalog classes target ps st).slots.size=st.slots.size := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih => rw [banksLoop,ih]; exact Array.size_setIfInBounds

theorem banksLoop_other (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (ps : List Nat) (st : Mutable.Store.State C E) (p : Nat) (hp : p∉ps) :
    (banksLoop C E book prepared ci ei partition capacity current anchors window catalog classes target ps st).slots[p]?=st.slots[p]? := by
  induction ps generalizing st with
  | nil => rfl
  | cons q qs ih =>
    have hq : q≠p := by intro he; apply hp; simp [he]
    have ht : p∉qs := by intro hm; exact hp (List.mem_cons_of_mem q hm)
    rw [banksLoop,ih _ ht]
    exact write_other C E book prepared ci ei partition capacity q current p anchors window catalog classes target st hq

theorem banksLoop_selected (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (ps : List Nat) (st : Mutable.Store.State C E) (p : Nat)
    (hp : p∈ps) (hb : p<st.slots.size) :
    (banksLoop C E book prepared ci ei partition capacity current anchors window catalog classes target ps st).slots[p]?=
      some (compile C E book prepared ci ei partition capacity p current anchors window catalog classes st.sources target).1 := by
  induction ps generalizing st with
  | nil => cases hp
  | cons q qs ih =>
    let next:=write C E book prepared ci ei partition capacity q current anchors window catalog classes target st
    rw [banksLoop]
    by_cases ht : p∈qs
    · have hsize : p<({next with repairWork:=next.repairWork+3} : Mutable.Store.State C E).slots.size := by
        change p<(st.slots.setIfInBounds q _).size
        simpa only [Array.size_setIfInBounds] using hb
      exact ih {next with repairWork:=next.repairWork+3} ht hsize
    · rw [banksLoop_other C E book prepared ci ei partition capacity current anchors window catalog classes target qs _ p ht]
      have he : p=q := (List.mem_cons.mp hp).resolve_right ht
      subst q
      exact write_selected C E book prepared ci ei partition capacity p current anchors window catalog classes target st hb

structure Reset (C E : DFA α) where
  anchors : Array (Option Nat)
  store : Mutable.Store.State C E
  work : Nat

/-- `keys.positions` is the sparse set's maintained deduplicated list;
there is no conversion/scan of its position tree. -/
def reset (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (keys : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E) : Reset C E :=
  let fresh:=anchorsLoop current keys.keys.positions anchors 0
  let oldWork:=st.repairWork
  let done:=banksLoop C E book prepared ci ei partition capacity current fresh.1 window catalog classes target keys.keys.positions st
  ⟨fresh.1,done,fresh.2+(done.repairWork-oldWork)+4⟩

end REWB.MaskedTraversalRepair
