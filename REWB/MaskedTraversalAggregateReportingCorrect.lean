import REWB.MaskedTraversalAggregateReporting
import REWB.MaskedTraversalCompleteCorrect

/-! Reporting is instantiated with the actual proved cross-cluster
query. Every eligible current source is reported once, removed from the
real mutable indexes, and cannot be reported by a later query of this
band. There is no supplied query-answer contract in these theorems.
-/
namespace REWB.MaskedTraversalAggregate.Reporting
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedTraversalComplete
variable {α : Type} {h : Nat}

theorem ask_correct (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat) (tree : BankTree C E h)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source removed st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi) :
    MaskedReporting.QueryCorrect (ask B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old)
      (BandGood B C E w partition capacity lengthLo lengthHi source removed env.target) := by
  obtain ⟨hv,hn,hK,hg,entries,hr,hco,hcp,hl,hu⟩:=hm
  intro lo hi
  exact queryWindow_iff B env st partition capacity base old lengthLo lengthHi lo hi anchors tree hg entries hr hco hcp hl
    w fallback geometry hu source removed hv hn hK hc he hlength

theorem run_correct (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat) (tree : BankTree C E h)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source removed st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi) (p : Nat) :
    p∈(run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old).reported.starts ↔
      BandGood B C E w partition capacity lengthLo lengthHi source removed env.target p := by
  have hquery:=ask_correct B C E env st partition capacity base old lengthLo lengthHi anchors source removed tree
    w fallback geometry hm hc he hlength
  have hband:=geometry lengthLo (Nat.le_refl _) hlength
  rw [run,MaskedReporting.report_correct _ _ hquery]
  constructor
  · exact fun hh=>hh.2.2
  · intro hh
    exact ⟨Nat.zero_le _,(MaskedOrdered.Tree.within partition.occurrences 0 hband.oldInvariant.occFits p hh.2.1).2,hh⟩

theorem run_sound (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat) (tree : BankTree C E h)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source removed st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi) (p : Nat)
    (hp : p∈(run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old).reported.starts) :
    Mutable.Batch.currentBit source removed p=true ∧
      Spec.maskedStart B C E w (MaskedProgression.readMask env.target) p := by
  obtain ⟨hbit,hp,L,hlo,hhi,j,hj,ht,_,horder,hbound,hB,hC,hE⟩:=(run_correct B C E env st partition capacity base old
    lengthLo lengthHi anchors source removed tree w fallback geometry hm hc he hlength p).mp hp
  refine ⟨hbit,p+L,j,j+L,by omega,horder,by omega,hbound,ht,?_,hB,hC,hE⟩
  exact (class_slice w fallback partition capacity base old L anchors (geometry L hlo hhi) p hp).trans
    (class_slice w fallback partition capacity base old L anchors (geometry L hlo hhi) j hj).symm

theorem run_calls (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat) (tree : BankTree C E h)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source removed st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi) :
    let out:=run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old
    out.reported.calls≤1+2*h*out.reported.starts.length :=
  MaskedReporting.report_calls _ _ (ask_correct B C E env st partition capacity base old lengthLo lengthHi anchors source removed
    tree w fallback geometry hm hc he hlength) h 0

theorem run_exhausts (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat) (tree : BankTree C E h)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source removed st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi) (p : Nat) :
    let out:=run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old
    ¬BandGood B C E w partition capacity lengthLo lengthHi source (out.reported.starts.reverse++removed) env.target p := by
  dsimp only
  rintro ⟨hbit,hp,hrest⟩
  have hb : MaskedProgression.readMask source p=true ∧
      p∉(run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old).reported.starts.reverse++removed := by
    simpa only [Mutable.Batch.currentBit,Bool.and_eq_true,decide_eq_true_eq] using hbit
  have hnot : p∉removed := by intro hx; exact hb.2 (List.mem_append.mpr (Or.inr hx))
  have hold : BandGood B C E w partition capacity lengthLo lengthHi source removed env.target p := by
    refine ⟨?_,hp,hrest⟩
    simp only [Mutable.Batch.currentBit,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hb.1,hnot⟩
  have reported:=(run_correct B C E env st partition capacity base old lengthLo lengthHi anchors source removed tree
    w fallback geometry hm hc he hlength p).mpr hold
  exact hb.2 (List.mem_append.mpr (Or.inl (List.mem_reverse.mpr reported)))

theorem run_charged (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat) (tree : BankTree C E h)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source removed st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi) :
    let out:=run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old
    let A:=queryBudget B C E env.prepared.K h w.length
    let R:=11*h+25+Mutable.Store.bankLimit C E env.prepared.K w.length+
      (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)+
      MaskedMutableProgression.Batch.requestBudget w.length
    MaskedReporting.totalWork out.reported+out.repaired.work+out.repaired.store.sources.updateWork+
      st.sources.delivered*MaskedMutableProgression.Batch.rowBudget w.length≤
      st.sources.updateWork+(A+1)+((2*A+3)*h+R)*out.reported.starts.length+
        out.repaired.store.sources.delivered*MaskedMutableProgression.Batch.rowBudget w.length := by
  have hquery:=ask_correct B C E env st partition capacity base old lengthLo lengthHi anchors source removed tree
    w fallback geometry hm hc he hlength
  have hband:=geometry lengthLo (Nat.le_refl _) hlength
  have hr:=MaskedReporting.report_totalWork _ _ hquery (queryBudget B C E env.prepared.K h w.length)
    (fun lo hi=>ask_work B C E env st partition capacity base old lengthLo lengthLo lengthHi lo hi anchors source removed tree
      w fallback hband hm hc he) h 0
  have hd:=eraseMany_charged env partition capacity base old lengthLo anchors source removed
    (run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old).reported.starts
    st tree w fallback hband hm hc he
  dsimp only [run] at hr hd ⊢
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] at hr hd ⊢
  omega

end REWB.MaskedTraversalAggregate.Reporting
