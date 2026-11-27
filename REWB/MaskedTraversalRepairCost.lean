import REWB.MaskedTraversalRepairCorrect

/-! Cost of the actual two-pass owned-array repair. Both list traversals,
every anchor write, automatic descriptor/catalog/neighbor preparation,
bank compilation and direct slot write are counted. There is no scan of
the full store or of a cluster's occurrences. The retained global arrays
are used under the same owned-array unit-slot model as Store; retaining
arbitrary old whole-store snapshots is not charged as a constant write.
-/
namespace REWB.MaskedTraversalRepair
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalBankReady REWB.MaskedRunDiscovery
variable {α : Type} {σ h h' n : Nat}

theorem banksLoop_counts (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (ps : List Nat) (st : Mutable.Store.State C E) :
    (banksLoop C E book prepared ci ei partition capacity current anchors window catalog classes target ps st).rebuilds=
      st.rebuilds+ps.length ∧
    (banksLoop C E book prepared ci ei partition capacity current anchors window catalog classes target ps st).writes=
      st.writes+ps.length := by
  induction ps generalizing st with
  | nil => exact ⟨rfl,rfl⟩
  | cons p ps ih =>
    let next:=write C E book prepared ci ei partition capacity p current anchors window catalog classes target st
    have ht:=ih {next with repairWork:=next.repairWork+3}
    rw [banksLoop]
    have hr : next.rebuilds=st.rebuilds+1 := rfl
    have hw : next.writes=st.writes+1 := rfl
    change _=st.rebuilds+(ps.length+1) ∧ _=st.writes+(ps.length+1)
    dsimp only [next] at ht hr hw ⊢
    constructor <;> omega

theorem banksLoop_budget (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (ps : List Nat) (st : Mutable.Store.State C E) (limit : Nat)
    (hw : ∀p,p∈ps→(compile C E book prepared ci ei partition capacity p current anchors window catalog classes st.sources target).2≤limit) :
    st.repairWork≤(banksLoop C E book prepared ci ei partition capacity current anchors window catalog classes target ps st).repairWork ∧
    (banksLoop C E book prepared ci ei partition capacity current anchors window catalog classes target ps st).repairWork≤
      st.repairWork+(limit+8)*ps.length+1 := by
  induction ps generalizing st with
  | nil => simp [banksLoop]
  | cons p ps ih =>
    let next:=write C E book prepared ci ei partition capacity p current anchors window catalog classes target st
    have hs : ({next with repairWork:=next.repairWork+3} : Mutable.Store.State C E).sources=st.sources := rfl
    have ht:=ih {next with repairWork:=next.repairWork+3} (by
      intro q hq
      rw [hs]
      exact hw q (List.mem_cons_of_mem p hq))
    have hp:=hw p List.mem_cons_self
    have hn : next.repairWork=st.repairWork+
        (compile C E book prepared ci ei partition capacity p current anchors window catalog classes st.sources target).2+5 := rfl
    rw [banksLoop]
    change st.repairWork≤_ ∧ _≤st.repairWork+(limit+8)*(ps.length+1)+1
    rw [Nat.mul_succ]
    dsimp only [next] at ht hn ⊢
    constructor <;> omega

theorem reset_work (C E : DFA (Fin σ)) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (hK : 0<prepared.K)
    (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (removed : List Nat)
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow) (keys : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E)
    (hsrc : st.sources=MaskedMutableProgression.Batch.run text fallback source prepared.K removed)
    (hi : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (hfull : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (hL : 0<L) (haway : AnchorBoundsAway partition capacity text.size L anchors keys.keys.positions) :
    (reset C E book prepared (BoundaryApplication.Range.build C text.toList)
      (BoundaryApplication.Range.build E text.toList) partition capacity L anchors window
      (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source prepared.K))
      (MaskedSuffixClass.prepare text fallback) target keys st).work≤
      (85*h+52*MaskedRunCatalog.width text.size+149+Mutable.Store.bankLimit C E prepared.K text.size)*
        keys.keys.positions.length+6 := by
  let fresh:=(anchorsLoop L keys.keys.positions anchors 0).1
  have hb:=anchorsLoop_bounds partition capacity text.size base L (ArrayText.read text fallback)
    anchors keys.keys.positions 0 hi hcap hfull hL haway
  have hw : ∀p,p∈keys.keys.positions→
      (compile C E book prepared (BoundaryApplication.Range.build C text.toList)
        (BoundaryApplication.Range.build E text.toList) partition capacity p L fresh window
        (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source prepared.K))
        (MaskedSuffixClass.prepare text fallback) st.sources target).2≤
        85*h+52*MaskedRunCatalog.width text.size+137+Mutable.Store.bankLimit C E prepared.K text.size := by
    intro p hp
    rw [hsrc]
    apply compile_reset_work C E book prepared hK text fallback source target removed partition capacity L p base
      fresh window hi hcap hfull hL hb
    change readAnchor (anchorsLoop L keys.keys.positions anchors 0).1 p L=L
    rw [anchorsLoop_read,if_pos hp]
  have hs:=banksLoop_budget C E book prepared (BoundaryApplication.Range.build C text.toList)
    (BoundaryApplication.Range.build E text.toList) partition capacity L fresh window
    (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source prepared.K))
    (MaskedSuffixClass.prepare text fallback) target keys.keys.positions st _ hw
  have ha:=anchorsLoop_work L keys.keys.positions anchors 0
  dsimp only [reset]
  dsimp only [fresh] at hs
  rw [ha]
  have hm : (85*h+52*MaskedRunCatalog.width text.size+149+Mutable.Store.bankLimit C E prepared.K text.size)*
        keys.keys.positions.length=
      (85*h+52*MaskedRunCatalog.width text.size+137+Mutable.Store.bankLimit C E prepared.K text.size+8)*
        keys.keys.positions.length+4*keys.keys.positions.length := by
    rw [←Nat.add_mul]
    congr 1
    omega
  rw [hm]
  omega

end REWB.MaskedTraversalRepair
