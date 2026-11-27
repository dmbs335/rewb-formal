import REWB.MaskedTraversalAggregateClipCost
import REWB.MaskedTraversalAggregateSequence

/-! Actual arbitrary source-window query: identify at most two boundary
leaders, recompile those stored banks with a source window, and make one
shared-length cut query on the temporary persistent aggregate. Targets
and the permanent source/aggregate state remain unchanged by construction.
-/
namespace REWB.MaskedTraversalAggregate
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {h : Nat}

def rejectedBand : BandResult := ⟨false,0,0,0,0,0,0⟩

structure WindowResult where
  band : BandResult
  clippingWork : Nat
  bankCalls : Nat
  queries : Nat
  deriving Repr

def queryWindow (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h)
    (capacity : Nat) (tree : BankTree C E h)
    (lo hi representative lengthLo lengthHi old : Nat) : WindowResult :=
  let clipped:=Clip.window env st partition capacity old lo hi tree
  if clipped.update.ready then
    ⟨queryBand B C E cut clipped.update.tree clipped.lower hi representative lengthLo lengthHi old,
      clipped.work+2,clipped.update.calls,1⟩
  else ⟨rejectedBand,clipped.work+2,clipped.update.calls,0⟩

theorem queryWindow_selected (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h)
    (capacity : Nat) (tree : BankTree C E h)
    (lo hi representative lengthLo lengthHi old : Nat) :
    (queryWindow B C E cut env st partition capacity tree lo hi representative lengthLo lengthHi old).band.answer=true ↔
      let clipped:=Clip.window env st partition capacity old lo hi tree
      clipped.update.ready=true ∧
        (queryBand B C E cut clipped.update.tree clipped.lower hi representative lengthLo lengthHi old).answer=true := by
  unfold queryWindow
  dsimp only
  split <;> simp_all only [rejectedBand,Bool.false_eq_true,and_self,and_false,true_and,false_and]

theorem queryWindow_correct (B C E : DFA α) (w : Word α) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h)
    (capacity : Nat) (tree : BankTree C E h) (hg : tree.Good)
    (lo hi representative lengthLo lengthHi old : Nat)
    (hl : lengthLo≤lengthHi) (hh : lengthHi≤old) (hn : representative+old≤w.length) :
    (queryWindow B C E (Cut.build B C E w) env st partition capacity tree
      lo hi representative lengthLo lengthHi old).band.answer=true ↔
      let clipped:=Clip.window env st partition capacity old lo hi tree
      clipped.update.ready=true ∧ ∃L,lengthLo≤L ∧ L≤lengthHi ∧
        B.accepts (Spec.slice w representative (representative+L)) ∧
        ∃q : Fin E.stateCount,E.final q=true ∧
          Chain (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+L) (representative+old))))
            (regionCells clipped.update.tree.leaves clipped.lower hi)
            (code _ false (MaskedClusterStage.encode C E .waiting))
            (code _ false (MaskedClusterStage.encode C E (.suffix q))) := by
  rw [queryWindow_selected]
  exact and_congr_right fun _=>queryBand_correct B C E w _
    (Clip.window_good env st partition capacity old lo hi tree hg) _ hi
    representative lengthLo lengthHi old hl hh hn

theorem queryWindow_counts (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h)
    (capacity : Nat) (tree : BankTree C E h)
    (lo hi representative lengthLo lengthHi old : Nat) :
    let out:=queryWindow B C E cut env st partition capacity tree lo hi representative lengthLo lengthHi old
    out.bankCalls≤2 ∧ out.queries≤1 ∧
      out.clippingWork=(Clip.window env st partition capacity old lo hi tree).work+2 := by
  have hc:=Clip.window_calls env st partition capacity old lo hi tree
  unfold queryWindow
  dsimp only
  split
  · exact ⟨hc,Nat.le_refl 1,rfl⟩
  · exact ⟨hc,Nat.zero_le 1,rfl⟩

theorem queryWindow_clipping_work (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h)
    (capacity : Nat) (tree : BankTree C E h)
    (lo hi representative lengthLo lengthHi old : Nat)
    (w : Word α) (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hg : ∀first,first∈(Clip.plan partition.leaders capacity lo hi).keys→
      ∀entry,st.slots[first]?.join=some entry→
        Mutable.Store.Geometry (Clip.config entry.config old lo hi) w.length) :
    (queryWindow B C E cut env st partition capacity tree lo hi representative lengthLo lengthHi old).clippingWork≤
      14*h+17+2*(Mutable.Store.bankLimit C E env.prepared.K w.length+
        (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
          (2*(MaskedClusterStage.dfa C E).stateCount)+10) := by
  rw [(queryWindow_counts B C E cut env st partition capacity tree lo hi representative lengthLo lengthHi old).2.2]
  have hw:=Clip.window_work env st partition capacity old lo hi tree w source removed hv hn hc he hg
  omega

theorem queryWindow_band_counters (B C E : DFA α) (w : Word α) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h)
    (capacity : Nat) (tree : BankTree C E h)
    (lo hi representative lengthLo lengthHi old : Nat) :
    let out:=(queryWindow B C E (Cut.build B C E w) env st partition capacity tree
      lo hi representative lengthLo lengthHi old).band
    out.closureProbes≤ReplayMaps.count C.stateCount E.stateCount*(E.stateCount+1) ∧
    out.cutProducts≤3 ∧ out.cutVisits≤3*(Nat.log2 w.length+2) ∧
    out.cutProbes≤(MaskedCut.DFAIndex.jointEnum B C E).elems.length*(MaskedCut.DFAIndex.jointEnum B C E).elems.length ∧
    out.arithmetic≤11 := by
  have hw:=queryBand_counters B C E w (Clip.window env st partition capacity old lo hi tree).update.tree
    (Clip.window env st partition capacity old lo hi tree).lower hi representative lengthLo lengthHi old
  unfold queryWindow
  dsimp only
  split
  · exact ⟨Nat.le_of_eq hw.1,hw.2⟩
  · exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩

end REWB.MaskedTraversalAggregate
