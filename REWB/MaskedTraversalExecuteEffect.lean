import REWB.MaskedTraversalExecuteBand

/-! A proof-only footprint for sequential use of the single global store.
It records the actual source erasures and actual unchanged raw/anchor
slots outside the current subtree. The runtime executor stores no such
list and never recompiles a suspended disjoint sibling.
-/
namespace REWB.MaskedTraversalExecute
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalRepairCoherence
variable {α : Type} {C E : DFA α} {h : Nat}

structure Effect (positions : List Nat) (before after : Global C E) : Prop where
  slots : ∀p,p∉positions→after.store.slots[p]?=before.store.slots[p]?
  anchors : ∀p,p∉positions→after.anchors[p]?=before.anchors[p]?
  erases : ∃ps,after.store.sources=MaskedMutableProgression.Batch.eraseMany ps before.store.sources ∧
    after.answers.history=ps.reverse++before.answers.history ∧ ∀p,p∈ps→p∈positions

theorem Effect.refl (positions : List Nat) (global : Global C E) : Effect positions global global :=
  ⟨by intros; rfl,by intros; rfl,[],rfl,rfl,by intro p hp; cases hp⟩

theorem Effect.mono {small large : List Nat} {before after : Global C E}
    (he : Effect small before after) (hm : ∀p,p∈small→p∈large) : Effect large before after := by
  obtain ⟨ps,hs,hh,hp⟩:=he.erases
  exact ⟨fun p hn=>he.slots p (fun hp=>hn (hm p hp)),fun p hn=>he.anchors p (fun hp=>hn (hm p hp)),
    ps,hs,hh,fun p hps=>hm p (hp p hps)⟩

theorem Effect.trans {positions : List Nat} {a b c : Global C E}
    (hab : Effect positions a b) (hbc : Effect positions b c) : Effect positions a c := by
  obtain ⟨xs,hxs,hxh,hxp⟩:=hab.erases
  obtain ⟨ys,hys,hyh,hyp⟩:=hbc.erases
  refine ⟨fun p hn=>(hbc.slots p hn).trans (hab.slots p hn),
    fun p hn=>(hbc.anchors p hn).trans (hab.anchors p hn),xs++ys,?_,?_,?_⟩
  · rw [hys,hxs]
    simp only [MaskedMutableProgression.Batch.eraseMany,List.foldl_append]
  · rw [hyh,hxh,List.reverse_append,List.append_assoc]
  · intro p hp
    exact (List.mem_append.mp hp).elim (hxp p) (hyp p)

theorem Effect.history {positions : List Nat} {before after : Global C E} (he : Effect positions before after) :
    ∀p,p∈before.answers.history→p∈after.answers.history := by
  obtain ⟨ps,_,hh,_⟩:=he.erases
  intro p hp
  rw [hh]
  exact List.mem_append.mpr (Or.inr hp)

variable {σ : Nat} {B C E : DFA (Fin σ)}

theorem Effect.saved (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size))
    (saved : MaskedClusterLeaders.State h) (capacity L : Nat) (st : State C E h) (after : Global C E)
    (hv : st.Valid text fallback source env saved capacity L)
    (hg : after.Valid text fallback source env) (hi : MaskedClusterLeaders.Invariant L saved) (hc : capacity=2^h)
    (positions : List Nat) (he : Effect positions st.global after)
    (hd : ∀p,p∈saved.occurrences.entries→p∉positions) :
    ({st with global:=after} : State C E h).Valid text fallback source env saved capacity L := by
  obtain ⟨entries,hr,hp,hu,hs⟩:=hv.entries
  obtain ⟨ps,hsource,_,hps⟩:=he.erases
  have hn : ∀p,p∈saved.leaders.entries→p∉positions := fun p hp=>hd p ((hi.represented p).mp hp).1
  refine ⟨hg,hv.dirty,hv.dirtySupport,hv.tree,?_,entries,hr,?_,hu,hs⟩
  · exact retained_slots saved capacity text.size L (ArrayText.read text fallback) st.global.anchors after.anchors
      st.frame.dirty.keys.positions hi hc hv.own (fun p hp=>he.anchors p (hn p hp))
  · exact Pending.transfer_erases env.repair saved capacity L st.global.store after.store st.global.anchors after.anchors
      st.frame.dirty entries source st.global.answers.history ps hi hc hp hv.global.sources hsource
      (fun p hp=>he.slots p (hn p hp)) (fun p hp=>he.anchors p (hn p hp)) hs
      (fun p hp hm=>hd p hm (hps p hp))

theorem band_effect (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity : Nat) (hc : capacity=2^h) (b : MaskedTraversalEdge.Band h) (st : State C E h)
    (hv : st.Valid text fallback source env b.snapshot capacity b.hi)
    (hm : MaskedTraversalPositiveCoverage.Metadata text fallback capacity b) :
    Effect b.snapshot.occurrences.entries st.global (band env capacity b st).global := by
  let repaired:=MaskedTraversalRepairCoherence.apply env.repair b.snapshot capacity b.hi st.global.anchors st.frame.dirty st.global.store st.frame.tree
  let collected:=Collect.run B C E env.cut env.repair.shared repaired.store b.snapshot capacity repaired.tree
    (representative b) b.lo b.hi b.hi st.global.answers
  have prepared:=band_prepared text fallback source env hs capacity hc b st hv hm
  have hpositions : ∀p,p∈collected.band.reported.starts→p∈b.snapshot.occurrences.entries := by
    intro p hp
    have hh:=Reporting.run_correct B C E env.repair.shared repaired.store b.snapshot capacity (representative b) b.hi b.lo b.hi
      repaired.anchors source st.global.answers.history repaired.tree text.toList fallback prepared.2.2
      (by simpa only [Array.length_toList] using prepared.1) hs.cRanges hs.eRanges hm.valid.bounds p
    have hm' : p∈(Reporting.run B C E (Cut.build B C E text.toList) env.repair.shared repaired.store b.snapshot capacity
        repaired.tree (representative b) b.lo b.hi b.hi).reported.starts := by
      simpa only [collected,Collect.run,hs.cut] using hp
    exact (hh.mp hm').2.1
  have outside : ∀p,p∉b.snapshot.occurrences.entries→
      repaired.store.slots[p]?=st.global.store.slots[p]? ∧ repaired.anchors[p]?=st.global.anchors[p]? := by
    intro p hp
    exact apply_disjoint_slots env.repair b.snapshot capacity b.hi st.global.anchors st.frame.dirty st.global.store st.frame.tree
      (fun q=>q∈b.snapshot.occurrences.entries) p hm.valid.invariant hc (fun _ hh=>hh) hv.dirtySupport hp
  refine ⟨?_,?_,collected.band.reported.starts,?_,?_,hpositions⟩
  · intro p hp
    change collected.band.repaired.store.slots[p]?=st.global.store.slots[p]?
    have he : collected.band.repaired.store.slots[p]?=repaired.store.slots[p]? := by
      apply Cells.eraseMany_other env.repair.shared b.snapshot capacity b.hi p collected.band.reported.starts repaired.store repaired.tree
      intro q _ hq
      have leader:=((MaskedClusterDescriptor.locate_correct b.snapshot capacity b.hi q p hm.valid.invariant hc).mp hq).2.1
      exact hp ((hm.valid.invariant.represented p).mp leader).1
    exact he.trans (outside p hp).1
  · intro p hp
    exact (outside p hp).2
  · change collected.band.repaired.store.sources=MaskedMutableProgression.Batch.eraseMany collected.band.reported.starts st.global.store.sources
    rw [Collect.run_sources,apply_sources]
  · exact Collect.run_history B C E env.cut env.repair.shared repaired.store b.snapshot capacity repaired.tree
      (representative b) b.lo b.hi b.hi st.global.answers

end REWB.MaskedTraversalExecute
