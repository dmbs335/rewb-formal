import REWB.MaskedTraversalAggregateShorten

/-! Actual per-frontier bank coherence. A model entry has the current
length and its actual compiled bank. The shared raw slot has the same
descriptor/anchor/context/run/window fields, but may retain an older
length. Normalizing that raw configuration must recover the model one.
This records exactly the invariant needed by current-length erasure.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h : Nat}

structure EntryState (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old first : Nat)
    (entry : Mutable.Store.Entry C E) : Prop where
  descriptor : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some entry.config.descriptor
  current : entry.config.length=old
  compiled : (Clip.compiled env st entry.config).1=some entry.bank
  raw : ∃before,st.slots[first]?.join=some before ∧ withLength before.config old=entry.config

def Coherent (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (entries : List (Option (Mutable.Store.Entry C E))) : Prop :=
  ∀first entry,entries[first]?=some (some entry)→EntryState env st partition capacity old first entry

theorem EntryState.shortened (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old first : Nat)
    (entry : Mutable.Store.Entry C E) (hh : EntryState env st partition capacity old first entry)
    (w : Word α) (representative fresh : Nat)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hnew : fresh≤old) (hH : old≤entry.config.anchor)
    (hrep : representative+old≤w.length) (hstart : entry.config.descriptor.first+entry.config.anchor≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=
      Spec.slice w entry.config.descriptor.first (entry.config.descriptor.first+old)) :
    EntryState env st partition capacity fresh first
      ⟨withLength entry.config fresh,
        (Counted.reindex (bankAction (ReplayMaps.word C E (Spec.slice w (representative+fresh) (representative+old)))) entry.bank).1⟩ := by
  refine ⟨hh.descriptor,rfl,?_,?_⟩
  · have hcur : (Mutable.Store.compile C E env.book env.prepared (BoundaryApplication.Range.build C w)
        (BoundaryApplication.Range.build E w) st.sources env.target entry.config).1=some entry.bank := by
      simpa only [Clip.compiled,hc,he] using hh.compiled
    have hshort:=store_reindex C E env.book env.prepared w st.sources env.target entry.config representative fresh
      (by rw [hh.current]; exact hnew) (by rw [hh.current]; exact hH)
      (by rw [hh.current]; exact hrep) hstart (by simpa only [hh.current] using hcopy)
    rw [hcur] at hshort
    simpa only [Clip.compiled,hc,he,Option.map,hh.current] using hshort.symm
  · obtain ⟨before,hs,hn⟩:=hh.raw
    refine ⟨before,hs,?_⟩
    rw [←hn]
    rfl

theorem Coherent.shortened (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (entries : List (Option (Mutable.Store.Entry C E))) (hh : Coherent env st partition capacity old entries)
    (w : Word α) (representative fresh : Nat)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hnew : fresh≤old) (hrep : representative+old≤w.length)
    (anchors : ∀(first : Nat) (entry : Mutable.Store.Entry C E),entries[first]?=some (some entry)→
      old≤entry.config.anchor ∧ entry.config.descriptor.first+entry.config.anchor≤w.length)
    (copies : ∀(first : Nat) (entry : Mutable.Store.Entry C E),entries[first]?=some (some entry)→
      Spec.slice w representative (representative+old)=
        Spec.slice w entry.config.descriptor.first (entry.config.descriptor.first+old)) :
    Coherent env st partition capacity fresh
      (entries.map (reindexedEntry (ReplayMaps.word C E (Spec.slice w (representative+fresh) (representative+old))) fresh)) := by
  intro first entry hentry
  cases hs : entries[first]? with
  | none => simp only [List.getElem?_map,hs,Option.map] at hentry; cases hentry
  | some value =>
    cases value with
    | none => simp only [List.getElem?_map,hs,Option.map,reindexedEntry,Option.some.injEq] at hentry; cases hentry
    | some before =>
      simp only [List.getElem?_map,hs,Option.map,reindexedEntry,Option.some.injEq] at hentry
      subst entry
      exact EntryState.shortened env st partition capacity old first before (hh first before hs) w representative fresh
        hc he hnew (anchors first before hs).1 hrep (anchors first before hs).2 (copies first before hs)

end REWB.MaskedTraversalAggregate.Cells
