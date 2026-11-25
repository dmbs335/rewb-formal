import REWB.MaskedTraversalAggregateDisjoint
import REWB.MaskedTraversalRepairMaintained

/-! Support-based preservation of suspended frontiers. A child lowered
to a parent depth can be pending and need not yet be a complete class.
These lemmas preserve its raw slots, retained anchors and pending model
using only actual write locations and candidate-source support.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h g n h' : Nat}

theorem compile_eraseMany_supported (env : Clip.Env C E) (sources : Mutable.Batch.Sources)
    (cfg : Mutable.Store.Config) (source : Array Bool) (removed positions : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources)
    (hp : ∀p,p∈positions→¬Mutable.Batch.Candidates cfg.descriptor.first cfg.descriptor.period cfg.descriptor.repetitions p) :
    (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      (MaskedMutableProgression.Batch.eraseMany positions sources) env.target cfg).1=
    (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges sources env.target cfg).1 := by
  induction positions generalizing sources removed with
  | nil=>rfl
  | cons p ps ih=>
    change (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      (MaskedMutableProgression.Batch.eraseMany ps (MaskedMutableProgression.Batch.eraseSource p sources)) env.target cfg).1=_
    rw [ih _ (p::removed) (MaskedMutableProgression.Batch.eraseSource_valid hv p)
      (fun q hq=>hp q (List.mem_cons_of_mem p hq))]
    exact Mutable.Store.compile_erase C E env.book env.prepared env.cRanges env.eRanges source removed sources hv env.target cfg p
      (fun hcan=>False.elim (hp p List.mem_cons_self hcan))

theorem incoming_slots (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (before after : Array (Option Nat)) (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hs : ∀p,p∈partition.leaders.entries→after[p]?=before[p]?) :
    incoming partition capacity first L after=incoming partition capacity first L before := by
  unfold incoming
  cases hprev : (MaskedOrdered.Tree.pred partition.leaders capacity first).1 with
  | none=>simp only [hprev]
  | some p=>
    simp only [hprev]
    cases hd : (describeLeader partition capacity p).1 with
    | none=>simp only [hd]
    | some d=>
      have hh:=describeLeader_sound partition capacity L p hi hc d hd
      have hm : p∈partition.leaders.entries := by simpa only [hh.1] using hh.2.firstLeader
      simp only [hd,readAnchor,hs p hm]

theorem Pending.transfer (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (before after : Mutable.Store.State C E) (anchors nextAnchors : Array (Option Nat))
    (dirty : MaskedTraversalDirty.Marked h) (entries : List (Option (Mutable.Store.Entry C E)))
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hp : Pending env partition capacity L anchors dirty before entries)
    (hs : after.sources=before.sources)
    (hslots : ∀p,p∈partition.leaders.entries→after.slots[p]?=before.slots[p]?)
    (ha : ∀p,p∈partition.leaders.entries→nextAnchors[p]?=anchors[p]?) :
    Pending env partition capacity L nextAnchors dirty after entries := by
  refine ⟨?_,?_,hp.complete,?_⟩
  · intro first hm hn
    obtain ⟨entry,he⟩:=hp.raw first hm hn
    refine ⟨entry,?_,he.descriptor,?_,?_⟩
    · rw [hslots first hm]; exact he.slot
    · simp only [readAnchor,ha first hm]
      exact he.anchor
    · rw [hs]; exact he.run
  · intro first hn entry he
    have hh:=hp.coherent first hn entry he
    have hd:=describeLeader_sound partition capacity L first hi hc entry.config.descriptor hh.descriptor
    have hm : first∈partition.leaders.entries := by simpa only [hd.1] using hd.2.firstLeader
    exact entry_transfer env.shared before after partition capacity L first entry hh hs (hslots first hm)
  · intro first hn hctx entry he
    have hh:=hp.linked first hn hctx entry he
    have hd:=describeLeader_sound partition capacity L first hi hc entry.config.descriptor (hp.coherent first hn entry he).descriptor
    have hm : first∈partition.leaders.entries := by simpa only [hd.1] using hd.2.firstLeader
    have hin:=incoming_slots partition capacity L first anchors nextAnchors hi hc ha
    refine ⟨?_,?_,?_,?_⟩
    · simp only [readAnchor,ha first hm]
      exact hh.anchor
    · rw [hin]; exact hh.incoming
    · rw [hin]; exact hh.enabled
    · rw [hs]; exact hh.run

theorem Pending.transfer_erases (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (before after : Mutable.Store.State C E) (anchors nextAnchors : Array (Option Nat))
    (dirty : MaskedTraversalDirty.Marked h) (entries : List (Option (Mutable.Store.Entry C E)))
    (source : Array Bool) (removed positions : List Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hp : Pending env partition capacity L anchors dirty before entries)
    (hv : MaskedMutableProgression.Batch.Valid source removed before.sources)
    (hs : after.sources=MaskedMutableProgression.Batch.eraseMany positions before.sources)
    (hslots : ∀p,p∈partition.leaders.entries→after.slots[p]?=before.slots[p]?)
    (ha : ∀p,p∈partition.leaders.entries→nextAnchors[p]?=anchors[p]?)
    (hsupport : ∀(first : Nat) (entry : Mutable.Store.Entry C E),entries[first]?=some (some entry)→
      ∀p,Mutable.Batch.Candidates entry.config.descriptor.first entry.config.descriptor.period entry.config.descriptor.repetitions p→
        p∈partition.occurrences.entries)
    (habsent : ∀p,p∈positions→p∉partition.occurrences.entries) :
    Pending env partition capacity L nextAnchors dirty after entries := by
  have hruns : after.sources.runs=before.sources.runs := by
    rw [hs,MaskedMutableProgression.Batch.eraseMany_runs]
  refine ⟨?_,?_,hp.complete,?_⟩
  · intro first hm hn
    obtain ⟨entry,he⟩:=hp.raw first hm hn
    refine ⟨entry,?_,he.descriptor,?_,?_⟩
    · rw [hslots first hm]; exact he.slot
    · simp only [readAnchor,ha first hm]
      exact he.anchor
    · simpa only [RunBacked,hruns] using he.run
  · intro first hn entry he
    have hh:=hp.coherent first hn entry he
    have hd:=describeLeader_sound partition capacity L first hi hc entry.config.descriptor hh.descriptor
    have hm : first∈partition.leaders.entries := by simpa only [hd.1] using hd.2.firstLeader
    refine ⟨hh.descriptor,hh.current,?_,?_⟩
    · change (Mutable.Store.compile C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
        after.sources env.shared.target entry.config).1=some entry.bank
      rw [hs,compile_eraseMany_supported env.shared before.sources entry.config source removed positions hv
        (fun p hm hcand=>habsent p hm (hsupport first entry he p hcand))]
      exact hh.compiled
    · obtain ⟨raw,hraw,hcfg⟩:=hh.raw
      exact ⟨raw,by rw [hslots first hm]; exact hraw,hcfg⟩
  · intro first hn hctx entry he
    have hh:=hp.linked first hn hctx entry he
    have hd:=describeLeader_sound partition capacity L first hi hc entry.config.descriptor (hp.coherent first hn entry he).descriptor
    have hm : first∈partition.leaders.entries := by simpa only [hd.1] using hd.2.firstLeader
    have hin:=incoming_slots partition capacity L first anchors nextAnchors hi hc ha
    refine ⟨?_,?_,?_,?_⟩
    · simp only [readAnchor,ha first hm]
      exact hh.anchor
    · rw [hin]; exact hh.incoming
    · rw [hin]; exact hh.enabled
    · simpa only [RunBacked,hruns] using hh.run

theorem retained_slots (partition : MaskedClusterLeaders.State h) (capacity n L : Nat) (f : Nat→α)
    (before after : Array (Option Nat)) (keys : List Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (ha : MaskedTraversalRetained.Away partition capacity f n L before keys)
    (hs : ∀p,p∈partition.leaders.entries→after[p]?=before[p]?) :
    MaskedTraversalRetained.Away partition capacity f n L after keys := by
  intro first hn d hd
  have hh:=describeLeader_sound partition capacity L first hi hc d hd
  have hm : first∈partition.leaders.entries := by simpa only [hh.1] using hh.2.firstLeader
  obtain ⟨H,hH,cert⟩:=ha first hn d hd
  exact ⟨H,by rw [hs first hm]; exact hH,cert⟩

theorem apply_disjoint_slots (env : Env C E n h') (active : MaskedClusterLeaders.State g) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked g) (st : Mutable.Store.State C E)
    (tree : BankTree C E g) (support : Nat→Prop) (first : Nat)
    (hi : MaskedClusterLeaders.Invariant L active) (hc : capacity=2^g)
    (hactive : ∀p,p∈active.occurrences.entries→support p)
    (hdirty : ∀p,p∈dirty.keys.positions→support p) (hf : ¬support first) :
    (apply env active capacity L anchors dirty st tree).store.slots[first]?=st.slots[first]? ∧
    (apply env active capacity L anchors dirty st tree).anchors[first]?=anchors[first]? := by
  have hp : first∉dirty.keys.positions := fun hh=>hf (hdirty first hh)
  have hq : first∉(contextKeys active capacity dirty).keys.positions := by
    intro hh
    have hm:=contextKeys_member active capacity L first dirty hi hc hh
    exact hf (hactive first ((hi.represented first).mp hm).1)
  refine ⟨apply_other env active capacity L first anchors dirty st tree hp hq,?_⟩
  change (MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1[first]?=anchors[first]?
  rw [MaskedTraversalRetained.anchorsLoop_slot,if_neg hp]

theorem apply_disjoint_pending (env : Env C E n h') (active : MaskedClusterLeaders.State g) (activeCapacity activeL : Nat)
    (saved : MaskedClusterLeaders.State h) (savedCapacity savedL : Nat) (anchors : Array (Option Nat))
    (activeDirty : MaskedTraversalDirty.Marked g) (savedDirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (activeTree : BankTree C E g)
    (entries : List (Option (Mutable.Store.Entry C E))) (support : Nat→Prop)
    (hai : MaskedClusterLeaders.Invariant activeL active) (hac : activeCapacity=2^g)
    (hsi : MaskedClusterLeaders.Invariant savedL saved) (hsc : savedCapacity=2^h)
    (hactive : ∀p,p∈active.occurrences.entries→support p)
    (hdirty : ∀p,p∈activeDirty.keys.positions→support p)
    (hsaved : ∀p,p∈saved.occurrences.entries→¬support p)
    (hp : Pending env saved savedCapacity savedL anchors savedDirty st entries) :
    Pending env saved savedCapacity savedL (apply env active activeCapacity activeL anchors activeDirty st activeTree).anchors
      savedDirty (apply env active activeCapacity activeL anchors activeDirty st activeTree).store entries := by
  apply Pending.transfer env saved savedCapacity savedL st _ anchors _ savedDirty entries hsi hsc hp
    (apply_sources env active activeCapacity activeL anchors activeDirty st activeTree)
  · intro p hm
    exact (apply_disjoint_slots env active activeCapacity activeL anchors activeDirty st activeTree support p hai hac hactive hdirty
      (hsaved p ((hsi.represented p).mp hm).1)).1
  · intro p hm
    exact (apply_disjoint_slots env active activeCapacity activeL anchors activeDirty st activeTree support p hai hac hactive hdirty
      (hsaved p ((hsi.represented p).mp hm).1)).2

theorem apply_disjoint_anchors (env : Env C E n h') (active : MaskedClusterLeaders.State g) (activeCapacity activeL : Nat)
    (saved : MaskedClusterLeaders.State h) (savedCapacity savedL size : Nat) (anchors : Array (Option Nat))
    (dirty : MaskedTraversalDirty.Marked g) (keys : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E g)
    (support : Nat→Prop) (f : Nat→α)
    (hai : MaskedClusterLeaders.Invariant activeL active) (hac : activeCapacity=2^g)
    (hsi : MaskedClusterLeaders.Invariant savedL saved) (hsc : savedCapacity=2^h)
    (hactive : ∀p,p∈active.occurrences.entries→support p) (hdirty : ∀p,p∈dirty.keys.positions→support p)
    (hsaved : ∀p,p∈saved.occurrences.entries→¬support p)
    (ha : MaskedTraversalRetained.Away saved savedCapacity f size savedL anchors keys) :
    MaskedTraversalRetained.Away saved savedCapacity f size savedL
      (apply env active activeCapacity activeL anchors dirty st tree).anchors keys := by
  apply retained_slots saved savedCapacity size savedL f anchors _ keys hsi hsc ha
  intro p hm
  exact (apply_disjoint_slots env active activeCapacity activeL anchors dirty st tree support p hai hac hactive hdirty
    (hsaved p ((hsi.represented p).mp hm).1)).2

end REWB.MaskedTraversalRepairCoherence
