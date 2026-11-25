import REWB.MaskedTraversalAggregateReportingCorrect
import REWB.MaskedTraversalAnswers

/-! One executable band transaction: query/report, erase the actual
mutable sources and repair their banks, then write only the new physical
answer bits. Source validity and the output history refer to exactly the
same deletion set. Previously reported positions cannot be emitted again.
-/
namespace REWB.MaskedTraversalAggregate.Collect
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedTraversalComplete
open MaskedProgression (readMask)
variable {α : Type} {h : Nat}

structure Result (C E : DFA α) (h : Nat) where
  band : Reporting.Result C E h
  answers : MaskedTraversalAnswers.State

def run (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) (answers : MaskedTraversalAnswers.State) : Result C E h :=
  let band:=Reporting.run B C E cut env st partition capacity tree base lengthLo lengthHi old
  ⟨band,MaskedTraversalAnswers.push band.reported.starts answers⟩

theorem run_history (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) (answers : MaskedTraversalAnswers.State) :
    let out:=run B C E cut env st partition capacity tree base lengthLo lengthHi old answers
    out.answers.history=out.band.reported.starts.reverse++answers.history :=
  MaskedTraversalAnswers.push_history _ _

theorem run_sources (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) (answers : MaskedTraversalAnswers.State) :
    let out:=run B C E cut env st partition capacity tree base lengthLo lengthHi old answers
    out.band.repaired.store.sources=MaskedMutableProgression.Batch.eraseMany out.band.reported.starts st.sources :=
  eraseMany_sources env partition capacity old _ st tree

theorem run_runs (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) (answers : MaskedTraversalAnswers.State) :
    (run B C E cut env st partition capacity tree base lengthLo lengthHi old answers).band.repaired.store.sources.runs=st.sources.runs := by
  rw [run_sources,MaskedMutableProgression.Batch.eraseMany_runs]

theorem run_maintained (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi n : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (tree : BankTree C E h) (answers : MaskedTraversalAnswers.State)
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (hm : Maintained env partition capacity old n anchors source answers.history st tree) :
    let out:=run B C E cut env st partition capacity tree base lengthLo lengthHi old answers
    out.band.repaired.ready=true ∧ Maintained env partition capacity old n anchors source
      out.answers.history out.band.repaired.store out.band.repaired.tree := by
  have hh:=Reporting.run_maintained B C E cut env st partition capacity base old lengthLo lengthHi n
    anchors source answers.history tree hi hc f hfull hm
  dsimp only
  rw [run_history]
  exact hh

theorem run_answers_valid (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (tree : BankTree C E h) (answers : MaskedTraversalAnswers.State)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source answers.history st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi)
    (ha : MaskedTraversalAnswers.Valid w.length (fun p=>readMask source p=true ∧ Spec.maskedStart B C E w (readMask env.target) p) answers) :
    MaskedTraversalAnswers.Valid w.length (fun p=>readMask source p=true ∧ Spec.maskedStart B C E w (readMask env.target) p)
      (run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old answers).answers := by
  apply MaskedTraversalAnswers.push_valid _ _ _ answers ha
    (Reporting.run_nodup B C E _ env st partition capacity tree base lengthLo lengthHi old)
  intro p hp
  obtain ⟨hb,hw⟩:=Reporting.run_sound B C E env st partition capacity base old lengthLo lengthHi anchors source answers.history tree
    w fallback geometry hm hc he hlength p hp
  have hbit : readMask source p=true ∧ p∉answers.history := by
    simpa only [Mutable.Batch.currentBit,Bool.and_eq_true,decide_eq_true_eq] using hb
  refine ⟨?_,⟨hbit.1,hw⟩,hbit.2⟩
  obtain ⟨a,j,t,hpa,haj,hjt,htn,_⟩:=hw
  omega

theorem run_count (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (tree : BankTree C E h) (answers : MaskedTraversalAnswers.State)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source answers.history st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi)
    (ha : MaskedTraversalAnswers.Valid w.length (fun p=>readMask source p=true ∧ Spec.maskedStart B C E w (readMask env.target) p) answers) :
    (run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old answers).answers.count≤w.length+1 :=
  (run_answers_valid B C E env st partition capacity base old lengthLo lengthHi anchors source tree answers w fallback geometry hm hc he hlength ha).count_le

theorem run_read (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (tree : BankTree C E h) (answers : MaskedTraversalAnswers.State)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source answers.history st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi) (hs : answers.bits.size=w.length+1) (p : Nat) :
    readMask (run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old answers).answers.bits p=true ↔
      readMask answers.bits p=true ∨ BandGood B C E w partition capacity lengthLo lengthHi source answers.history env.target p := by
  change readMask (MaskedTraversalAnswers.push _ answers).bits p=true ↔ _
  rw [MaskedTraversalAnswers.push_read,Reporting.run_correct B C E env st partition capacity base old lengthLo lengthHi
    anchors source answers.history tree w fallback geometry hm hc he hlength]
  constructor
  · rintro (ho|⟨hn,_⟩)
    · exact Or.inl ho
    · exact Or.inr hn
  · rintro (ho|hn)
    · exact Or.inl ho
    · refine Or.inr ⟨hn,?_⟩
      obtain ⟨_,_,L,_,_,j,_,_,_,horder,hbound,_⟩:=hn
      rw [hs]
      omega

theorem run_added_work (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) (answers : MaskedTraversalAnswers.State) :
    let out:=run B C E cut env st partition capacity tree base lengthLo lengthHi old answers
    out.answers.work=answers.work+6*out.band.reported.starts.length :=
  MaskedTraversalAnswers.push_work _ _

end REWB.MaskedTraversalAggregate.Collect
