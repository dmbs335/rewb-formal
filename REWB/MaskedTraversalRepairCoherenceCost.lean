import REWB.MaskedTraversalRepairCoherenceCorrect

/-! Cost of the whole actual reset/context/aggregate operation. Geometry
for the retained context compilers is derived from actual populated
anchors and complete descriptors. All sparse traversals, bank compiles,
slot writes and aggregate path copies are included. This is a local
per-dirty-key bound; global event attribution remains separate.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h σ : Nat}

theorem raw_geometry (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L first base n : Nat) (anchors : Array (Option Nat))
    (entry : Mutable.Store.Entry C E) (hr : RawReady env st partition capacity L first anchors entry)
    (f : Nat→β) (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : MaskedRunDiscovery.Complete f n base L partition.occurrences.entries) (hL : 0<L)
    (ha : MaskedTraversalRetained.Away partition capacity f n L anchors []) :
    Mutable.Store.Geometry (config partition capacity first L anchors entry.config) n := by
  have hg:=describeLeader_geometry partition capacity L first hi hc entry.config.descriptor hr.descriptor f n base hfull hL
  obtain ⟨H,hH,cert⟩:=ha first (by simp) entry.config.descriptor hr.descriptor
  have hin:=incoming_bound partition capacity n base L first f anchors hi hc hfull hL
    (fun p d hd=>(ha p (by simp) d hd).bounds) entry.config.descriptor hr.descriptor
  apply retained_geometry f n base entry.config.descriptor.first partition.occurrences.entries
    (MaskedTraversalRetained.copies entry.config.descriptor) (config partition capacity first L anchors entry.config) hg
  · simpa only [config,readAnchor,hH,Option.getD_some] using cert
  · exact hin

theorem raw_workReady (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L base n : Nat) (anchors : Array (Option Nat))
    (hr : RawComplete env st partition capacity L anchors) (ps : List Nat)
    (hm : ∀p,p∈ps→p∈partition.leaders.entries)
    (f : Nat→β) (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : MaskedRunDiscovery.Complete f n base L partition.occurrences.entries) (hL : 0<L)
    (ha : MaskedTraversalRetained.Away partition capacity f n L anchors []) :
    MaskedTraversalContext.Ready partition capacity L n anchors ps st := by
  intro first hp entry he
  obtain ⟨raw,hraw⟩:=hr first (hm first hp)
  have heq : raw=entry := Option.some.inj (hraw.slot.symm.trans he)
  subst raw
  exact raw_geometry env st partition capacity L first base n anchors entry hraw f hi hc hfull hL ha

def refreshBudget (C E : DFA α) (h : Nat) : Nat :=
  (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
    (2*(MaskedClusterStage.dfa C E).stateCount)+5

def repairBudget (C E : DFA α) (K n h : Nat) : Nat :=
  209*h+52*MaskedRunCatalog.width n+313+2*Mutable.Store.bankLimit C E K n+2*refreshBudget C E h

theorem apply_work (C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Setup text fallback source removed env partition capacity L base st)
    (hc : env.shared.cRanges=BoundaryApplication.Range.build C text.toList)
    (he : env.shared.eRanges=BoundaryApplication.Range.build E text.toList)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (hr : RawAway env.shared st partition capacity L anchors dirty.keys.positions)
    (ha : MaskedTraversalRetained.Away partition capacity (ArrayText.read text fallback) text.size L anchors dirty.keys.positions)
    (hb : text.size<anchors.size) :
    (apply env partition capacity L anchors dirty st tree).work≤
      repairBudget C E env.shared.prepared.K text.size h*dirty.keys.positions.length+16 := by
  let mid:=resetBanks env partition capacity L anchors dirty st
  let contexts:=contextKeys partition capacity dirty
  let done:=contextBanks env partition capacity L mid.anchors contexts.keys.positions mid.store
  let first:=refreshMany done dirty.keys.positions tree
  let second:=refreshMany done contexts.keys.positions first.1
  have hwReset : mid.work≤(85*h+52*MaskedRunCatalog.width text.size+149+
      Mutable.Store.bankLimit C E env.shared.prepared.K text.size)*dirty.keys.positions.length+6 := by
    dsimp only [mid,resetBanks]
    rw [hc,he,hs.catalog,hs.classes]
    exact MaskedTraversalRepair.reset_work C E env.shared.book env.shared.prepared hs.modulus_pos text fallback source
      env.shared.target removed partition capacity L base anchors env.window dirty st hs.sources hs.invariant hs.capacity_eq
      hs.complete hs.positive ha.bounds
  have hmeta:=successors_spec partition.leaders capacity dirty.keys.positions (MaskedTraversalDirty.empty h)
    hs.invariant.leadGood hs.invariant.leadFits hs.capacity_eq (MaskedOrdered.State.empty_valid h)
  have hcount : contexts.keys.positions.length≤dirty.keys.positions.length := by
    simpa only [contexts,contextKeys,MaskedTraversalDirty.empty,MaskedOrdered.State.empty,List.length_nil,Nat.zero_add] using hmeta.2.2.2.1
  have hwContexts : contexts.work≤(39*h+34)*dirty.keys.positions.length+2 := by
    have hh:=hmeta.2.2.2.2
    change contexts.work≤1+(39*h+34)*dirty.keys.positions.length+1 at hh
    omega
  have hraw:=setup_reset_raw text fallback source removed env partition capacity L base st hs anchors dirty hr
  have hown : MaskedTraversalRetained.Away partition capacity (ArrayText.read text fallback) text.size L mid.anchors [] :=
    MaskedTraversalRetained.reset_all partition capacity text.size base L (ArrayText.read text fallback) anchors dirty.keys.positions
      hs.invariant hs.capacity_eq hs.complete hs.positive hb ha
  have hready:=raw_workReady env.shared mid.store partition capacity L base text.size mid.anchors hraw contexts.keys.positions
    (fun p hp=>contextKeys_member partition capacity L p dirty hs.invariant hs.capacity_eq hp)
    (ArrayText.read text fallback) hs.invariant hs.capacity_eq hs.complete hs.positive hown
  have hv : MaskedMutableProgression.Batch.Valid source removed mid.store.sources := by
    dsimp only [mid]; rw [resetBanks_sources]; exact hs.valid
  have hn : mid.store.sources.n=text.toList.length := by
    dsimp only [mid]
    rw [resetBanks_sources,hs.sources,Array.length_toList]
    exact MaskedMutableProgression.Batch.eraseMany_n removed _
  have hwLoop : done.repairWork≤mid.store.repairWork+
      (85*h+130+Mutable.Store.bankLimit C E env.shared.prepared.K text.size)*contexts.keys.positions.length+1 := by
    have hh:=MaskedTraversalContext.applyLoop_work C E env.shared.book env.shared.prepared text.toList source removed
      mid.store hv hn partition capacity L mid.anchors env.shared.target contexts.keys.positions hready
    simpa only [done,contextBanks,hc,he,Array.length_toList] using hh
  have hwFirst : first.2≤dirty.keys.positions.length*refreshBudget C E h := refreshMany_work done dirty.keys.positions tree
  have hwSecond : second.2≤contexts.keys.positions.length*refreshBudget C E h := refreshMany_work done contexts.keys.positions first.1
  have hLoopCount:=Nat.mul_le_mul_left (85*h+130+Mutable.Store.bankLimit C E env.shared.prepared.K text.size) hcount
  have hTreeCount:=Nat.mul_le_mul_right (refreshBudget C E h) hcount
  rw [Nat.mul_comm dirty.keys.positions.length (refreshBudget C E h)] at hwFirst hTreeCount
  change mid.work+contexts.work+(done.repairWork-mid.store.repairWork)+first.2+second.2+7≤_
  dsimp only [repairBudget]
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at hwReset hwContexts hwLoop hLoopCount ⊢
  omega

end REWB.MaskedTraversalRepairCoherence
