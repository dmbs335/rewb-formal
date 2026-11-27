import REWB.MaskedTraversalAggregateMeaning

/-! Bank refreshes after source erasure retain every current configuration
field. Lazy shortening changes only its length. Thus actual anchor,
incoming cursor and immutable run/target metadata remain linked.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h : Nat}

theorem erasedEntries_config (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (first : Nat) (entry : Mutable.Store.Entry C E)
    (he : (erasedEntries env partition capacity old p st tree entries)[first]?=some (some entry)) :
    ∃before,entries[first]?=some (some before) ∧ entry.config=before.config := by
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
    obtain ⟨before,bank,hbefore,_,hslot,_⟩:=refreshCurrent_selected env first old mid tree hok
    have hs : (eraseCurrent env partition capacity old p st tree).store.slots[first]?.join=
        some ⟨withLength before.config old,bank⟩ := by simpa only [eraseCurrent,ho] using hslot
    simp only [erasedEntries,ho,List.getElem?_set_self hbound,hs,Option.some.injEq] at he
    subst entry
    obtain ⟨raw,hraw,hcfg⟩:=hh.raw
    have hraw' : before=raw := Option.some.inj (hbefore.symm.trans hraw)
    subst before
    exact ⟨previous,hprev,hcfg⟩
  · refine ⟨entry,?_,rfl⟩
    cases hk : (MaskedClusterDescriptor.locate partition capacity p).1 with
    | none=>simpa only [erasedEntries,hk] using he
    | some owner=>
      have hne : owner≠first := by intro hh; subst owner; exact ho hk
      simpa only [erasedEntries,hk,List.getElem?_set_ne hne] using he

theorem eraseCurrent_linked (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (anchors : Array (Option Nat)) (entries : List (Option (Mutable.Store.Entry C E)))
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) :
    LinkedEntries env (eraseCurrent env partition capacity old p st tree).store partition capacity old anchors
      (erasedEntries env partition capacity old p st tree entries) := by
  intro first entry he
  obtain ⟨before,hbefore,hcfg⟩:=erasedEntries_config env partition capacity old p st tree entries hi hc
    coherent complete source removed hv first entry he
  rw [hcfg]
  have hh:=linked first before hbefore
  refine ⟨hh.anchor,hh.incoming,hh.enabled,?_⟩
  rw [eraseCurrent_sources]
  exact MaskedTraversalContext.runBacked_erase st.sources env.target env.prepared.K p before.config hh.run

theorem shorten_linked (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old fresh : Nat) (anchors : Array (Option Nat))
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (f : Nat→α) (n : Nat) (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (ha : MaskedTraversalRetained.Away partition capacity f n old anchors [])
    (z : ReplayMaps.Value C.stateCount E.stateCount) :
    LinkedEntries env st partition capacity fresh anchors (entries.map (reindexedEntry z fresh)) := by
  intro first entry he
  cases hs : entries[first]? with
  | none=>simp only [List.getElem?_map,hs,Option.map] at he; cases he
  | some value=>
    cases value with
    | none=>simp only [List.getElem?_map,hs,Option.map,reindexedEntry,Option.some.injEq] at he; cases he
    | some before=>
      simp only [List.getElem?_map,hs,Option.map,reindexedEntry,Option.some.injEq] at he
      subst entry
      exact Linked.at_length env st partition capacity old fresh first anchors before.config
        (linked first before hs) f n hi hc ha (coherent first before hs).descriptor

end REWB.MaskedTraversalAggregate.Cells
