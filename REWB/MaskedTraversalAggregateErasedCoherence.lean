import REWB.MaskedTraversalAggregateCoherence

/-! Erasing a source preserves the actual active-frontier bank model,
including after lazy shortening. Completeness refers only to actual
leaders of this frontier, not to every slot of the shared global store.
The changed compiler result is obtained by executing the current-length
repair; other banks are proved unchanged by actual descriptor ownership.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h : Nat}

def CompleteModel (partition : MaskedClusterLeaders.State h)
    (entries : List (Option (Mutable.Store.Entry C E))) : Prop :=
  ∀first,first∈partition.leaders.entries→∃entry,entries[first]?=some (some entry)

def erasedEntries (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) : List (Option (Mutable.Store.Entry C E)) :=
  match (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none=>entries
  | some first=>entries.set first ((eraseCurrent env partition capacity old p st tree).store.slots[first]?.join)

theorem refreshCurrent_other (env : Clip.Env C E) (first old other : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) (hne : first≠other) :
    (refreshCurrent env first old st tree).store.slots[other]?=st.slots[other]? := by
  unfold refreshCurrent
  split
  · rfl
  · dsimp only
    split
    · rfl
    · exact Array.getElem?_setIfInBounds_ne hne

theorem eraseCurrent_other (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p other : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (hne : (MaskedClusterDescriptor.locate partition capacity p).1≠some other) :
    (eraseCurrent env partition capacity old p st tree).store.slots[other]?=st.slots[other]? := by
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none=>simp only [eraseCurrent,ho]
  | some first=>
    simp only [eraseCurrent,ho]
    apply refreshCurrent_other env first old other
    intro he
    subst first
    exact hne ho

theorem EntryState.erased_away (env : Clip.Env C E) (st next : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old first p : Nat)
    (entry : Mutable.Store.Entry C E) (hh : EntryState env st partition capacity old first entry)
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (n base : Nat)
    (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hne : (MaskedClusterDescriptor.locate partition capacity p).1≠some first)
    (hs : next.sources=MaskedMutableProgression.Batch.eraseSource p st.sources)
    (hr : next.slots[first]?=st.slots[first]?) :
    EntryState env next partition capacity old first entry := by
  refine ⟨hh.descriptor,hh.current,?_,?_⟩
  · change (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      next.sources env.target entry.config).1=some entry.bank
    rw [hs,Mutable.Store.erased_other_compile C E env.book env.prepared env.cRanges env.eRanges
      partition capacity old hi hc f n base hfull source removed st.sources hv env.target
      first entry.config hh.descriptor p hne]
    exact hh.compiled
  · obtain ⟨before,hbefore,hcfg⟩:=hh.raw
    exact ⟨before,by rw [hr]; exact hbefore,hcfg⟩

theorem eraseCurrent_ready (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) :
    (eraseCurrent env partition capacity old p st tree).ready=true := by
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none=>simp only [eraseCurrent,ho]
  | some first=>
    have hleader:=((MaskedClusterDescriptor.locate_correct partition capacity old p first hi hc).mp ho).2.1
    obtain ⟨entry,he⟩:=complete first hleader
    have hh:=coherent first entry he
    obtain ⟨before,hs,hn⟩:=hh.raw
    have hp:=Mutable.Store.compile_presence_erase C E env.book env.prepared env.cRanges env.eRanges
      source removed st.sources hv env.target entry.config p
    change (Clip.compiled env {st with sources:=MaskedMutableProgression.Batch.eraseSource p st.sources}
      entry.config).1.isSome=(Clip.compiled env st entry.config).1.isSome at hp
    rw [hh.compiled] at hp
    simp only [eraseCurrent,ho,refreshCurrent,hs,hn]
    cases hb : (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
        (MaskedMutableProgression.Batch.eraseSource p st.sources) env.target entry.config).1 with
    | none=>simp only [Clip.compiled,hb,Option.isSome_none,Option.isSome_some] at hp; cases hp
    | some bank=>simp only [Clip.compiled,hb]

theorem eraseCurrent_coherent (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (n base : Nat)
    (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) :
    Coherent env (eraseCurrent env partition capacity old p st tree).store partition capacity old
      (erasedEntries env partition capacity old p st tree entries) := by
  intro first entry he
  by_cases ho : (MaskedClusterDescriptor.locate partition capacity p).1=some first
  · have hleader:=((MaskedClusterDescriptor.locate_correct partition capacity old p first hi hc).mp ho).2.1
    obtain ⟨previous,hprev⟩:=complete first hleader
    have hh:=coherent first previous hprev
    have hbound:=(List.getElem?_eq_some_iff.mp hprev).1
    let mid : Mutable.Store.State C E := {st with
      sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
      repairWork:=st.repairWork+(MaskedClusterDescriptor.locate partition capacity p).2+2}
    have hok : (refreshCurrent env first old mid tree).ready=true := by
      simpa only [eraseCurrent,ho] using eraseCurrent_ready env partition capacity old p st tree entries hi hc
        coherent complete source removed hv
    obtain ⟨before,bank,hbefore,hbank,hslot,_⟩:=refreshCurrent_selected env first old mid tree hok
    have hs : (eraseCurrent env partition capacity old p st tree).store.slots[first]?.join=
        some ⟨withLength before.config old,bank⟩ := by simpa only [eraseCurrent,ho] using hslot
    simp only [erasedEntries,ho,List.getElem?_set_self hbound,hs,Option.some.injEq] at he
    subst entry
    obtain ⟨raw,hraw,hcfg⟩:=hh.raw
    have hraw' : before=raw := Option.some.inj (hbefore.symm.trans hraw)
    subst before
    refine ⟨?_,rfl,?_,?_⟩
    · change (MaskedClusterDescriptor.describeLeader partition capacity first).1=
        some (withLength raw.config old).descriptor
      rw [hcfg]
      exact hh.descriptor
    · change (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
        (eraseCurrent env partition capacity old p st tree).store.sources env.target (withLength raw.config old)).1=some bank
      rw [eraseCurrent_sources]
      exact hbank
    · exact ⟨⟨withLength raw.config old,bank⟩,hs,rfl⟩
  · have heold : entries[first]?=some (some entry) := by
      cases hk : (MaskedClusterDescriptor.locate partition capacity p).1 with
      | none=>simpa only [erasedEntries,hk] using he
      | some owner=>
        have hne : owner≠first := by intro hh; subst owner; exact ho hk
        simpa only [erasedEntries,hk,List.getElem?_set_ne hne] using he
    exact EntryState.erased_away env st _ partition capacity old first p entry (coherent first entry heold)
      hi hc f n base hfull source removed hv ho (eraseCurrent_sources env partition capacity old p st tree)
      (eraseCurrent_other env partition capacity old p first st tree ho)

theorem eraseCurrent_complete (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) :
    CompleteModel partition (erasedEntries env partition capacity old p st tree entries) := by
  intro first hleader
  obtain ⟨entry,he⟩:=complete first hleader
  have hbound:=(List.getElem?_eq_some_iff.mp he).1
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none=>exact ⟨entry,by simpa only [erasedEntries,ho] using he⟩
  | some owner=>
    by_cases hh : owner=first
    · subst owner
      have hok : (refreshCurrent env first old {st with
          sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
          repairWork:=st.repairWork+(MaskedClusterDescriptor.locate partition capacity p).2+2} tree).ready=true := by
        simpa only [eraseCurrent,ho] using eraseCurrent_ready env partition capacity old p st tree entries hi hc
          coherent complete source removed hv
      obtain ⟨before,bank,_,_,hs,_⟩:=refreshCurrent_selected env first old _ tree hok
      refine ⟨⟨withLength before.config old,bank⟩,?_⟩
      simp only [erasedEntries,ho,List.getElem?_set_self hbound,eraseCurrent,ho,hs]
    · exact ⟨entry,by simpa only [erasedEntries,ho,List.getElem?_set_ne hh] using he⟩

end REWB.MaskedTraversalAggregate.Cells
