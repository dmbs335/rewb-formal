import REWB.MaskedTraversalRepairMaintained
import REWB.MaskedTraversalRepairCoherenceCost

/-! The same whole-repair bound for arbitrary actual source snapshots.
Only current validity, cached size/modulus and immutable run provenance
are used. Historical erasure order and ledger equality are irrelevant.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {h σ : Nat}

theorem compile_snapshot_work (C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base first : Nat) (st : Mutable.Store.State C E)
    (hs : Snapshot text fallback source removed env partition capacity L base st)
    (hc : env.shared.cRanges=BoundaryApplication.Range.build C text.toList)
    (he : env.shared.eRanges=BoundaryApplication.Range.build E text.toList)
    (anchors : Array (Option Nat))
    (hb : AnchorBounds partition capacity text.size L anchors) (ha : readAnchor anchors first L=L) :
    (MaskedTraversalBankReady.compile C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
      partition capacity first L anchors env.window env.catalog env.classes st.sources env.shared.target).2≤
      85*h+52*MaskedRunCatalog.width text.size+137+Mutable.Store.bankLimit C E env.shared.prepared.K text.size := by
  have hp : (MaskedTraversalBankReady.prepare partition capacity first L anchors env.window env.catalog env.classes).2≤
      85*h+52*MaskedRunCatalog.width text.size+134 := by
    rw [hs.catalog,hs.classes]
    exact MaskedTraversalBankReady.prepare_work text fallback source env.shared.target env.shared.prepared.K partition capacity first L anchors env.window
  simp only [MaskedTraversalBankReady.compile]
  cases hprep : (MaskedTraversalBankReady.prepare partition capacity first L anchors env.window env.catalog env.classes).1 with
  | none => simp only [hprep]; omega
  | some cfg =>
    have hg:=prepare_reset_geometry partition capacity text.size base L first (ArrayText.read text fallback)
      anchors env.window env.catalog env.classes hs.invariant hs.capacity_eq hs.complete hs.positive hb ha cfg hprep
    have hn : st.sources.n=text.toList.length := by simpa only [Array.length_toList] using hs.size
    have hw:=Mutable.Store.compile_work C E env.shared.book env.shared.prepared text.toList source removed st.sources hs.valid hn
      env.shared.target cfg (by simpa only [Array.length_toList] using hg)
    simp only [Array.length_toList] at hw
    simp only [hprep,hc,he]
    omega

theorem reset_snapshot_work (C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Snapshot text fallback source removed env partition capacity L base st)
    (hc : env.shared.cRanges=BoundaryApplication.Range.build C text.toList)
    (he : env.shared.eRanges=BoundaryApplication.Range.build E text.toList)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (ha : MaskedTraversalRepair.AnchorBoundsAway partition capacity text.size L anchors dirty.keys.positions) :
    (resetBanks env partition capacity L anchors dirty st).work≤
      (85*h+52*MaskedRunCatalog.width text.size+149+Mutable.Store.bankLimit C E env.shared.prepared.K text.size)*
        dirty.keys.positions.length+6 := by
  let fresh:=(MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1
  have hb:=MaskedTraversalRepair.anchorsLoop_bounds partition capacity text.size base L (ArrayText.read text fallback)
    anchors dirty.keys.positions 0 hs.invariant hs.capacity_eq hs.complete hs.positive ha
  have hw : ∀p,p∈dirty.keys.positions→
      (MaskedTraversalBankReady.compile C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
        partition capacity p L fresh env.window env.catalog env.classes st.sources env.shared.target).2≤
        85*h+52*MaskedRunCatalog.width text.size+137+Mutable.Store.bankLimit C E env.shared.prepared.K text.size := by
    intro p hp
    apply compile_snapshot_work C E text fallback source removed env partition capacity L base p st hs hc he fresh hb
    change readAnchor (MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1 p L=L
    rw [MaskedTraversalRepair.anchorsLoop_read,if_pos hp]
  have hbudget:=MaskedTraversalRepair.banksLoop_budget C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity L fresh env.window env.catalog env.classes env.shared.target dirty.keys.positions st _ hw
  have hanchor:=MaskedTraversalRepair.anchorsLoop_work L dirty.keys.positions anchors 0
  dsimp only [resetBanks,MaskedTraversalRepair.reset]
  dsimp only [fresh] at hbudget
  rw [hanchor]
  have hm : (85*h+52*MaskedRunCatalog.width text.size+149+Mutable.Store.bankLimit C E env.shared.prepared.K text.size)*
        dirty.keys.positions.length=
      (85*h+52*MaskedRunCatalog.width text.size+137+Mutable.Store.bankLimit C E env.shared.prepared.K text.size+8)*
        dirty.keys.positions.length+4*dirty.keys.positions.length := by
    rw [←Nat.add_mul]
    congr 1
    omega
  rw [hm]
  omega

theorem apply_snapshot_work (C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Snapshot text fallback source removed env partition capacity L base st)
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
    exact reset_snapshot_work C E text fallback source removed env partition capacity L base st hs hc he anchors dirty ha.bounds
  have hmeta:=successors_spec partition.leaders capacity dirty.keys.positions (MaskedTraversalDirty.empty h)
    hs.invariant.leadGood hs.invariant.leadFits hs.capacity_eq (MaskedOrdered.State.empty_valid h)
  have hcount : contexts.keys.positions.length≤dirty.keys.positions.length := by
    simpa only [contexts,contextKeys,MaskedTraversalDirty.empty,MaskedOrdered.State.empty,List.length_nil,Nat.zero_add] using hmeta.2.2.2.1
  have hwContexts : contexts.work≤(39*h+34)*dirty.keys.positions.length+2 := by
    have hh:=hmeta.2.2.2.2
    change contexts.work≤1+(39*h+34)*dirty.keys.positions.length+1 at hh
    omega
  have hraw:=snapshot_reset_raw text fallback source removed env partition capacity L base st hs anchors dirty hr
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
    rw [resetBanks_sources,Array.length_toList]
    exact hs.size
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
