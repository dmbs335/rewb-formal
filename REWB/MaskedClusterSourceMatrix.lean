import REWB.MaskedClusterSourceCell

/-! Shared materialization for actual answer-producing cells and the
    source-clipped one-jump matrix. No deferred relation closure remains
    in the returned matrix. The bound is instantiated with the proved
    cell counter, rather than with a supplied query-cost oracle.
-/
namespace REWB.MaskedCluster
open REWB.MaskedFiniteAction REWB.BoundaryIndex.Counted
variable {α : Type}

def materialize {m : Nat} (f : Fin m→Fin m→MaskedProgression.Answer) : MatrixResult m :=
  let results:=Vector.ofFn fun i=>Vector.ofFn fun j=>let a:=f i j; (a.answer,a.slots+a.arithmetic)
  ⟨Vector.ofFn (fun i=>Vector.ofFn (fun j=>((results.get i).get j).1)),
    (List.ofFn (fun i=>rowWork (results.get i))).sum⟩

theorem materialize_get {m : Nat} (f : Fin m→Fin m→MaskedProgression.Answer) (i j : Fin m) :
    (((materialize f).cells.get i).get j)=(f i j).answer := by
  simp only [materialize,BoundaryIndex.Table.get_ofFn]

theorem materialize_work {m : Nat} (f : Fin m→Fin m→MaskedProgression.Answer) (budget : Nat)
    (h : ∀ i j,(f i j).slots+(f i j).arithmetic≤budget) :
    (materialize f).work≤m*(m*(budget+1)) := by
  apply sum_ofFn_le
  intro i
  apply rowWork_le
  intro j
  simpa only [BoundaryIndex.Table.get_ofFn] using h i j

def filteredMatrix (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat) (window : SourceWindow) :
    MatrixResult (MaskedClusterStage.dfa C E).stateCount :=
  materialize fun i j=>filteredCell C E prepared maps tail lo hi sourceCounts targetCounts base q s window
    (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)

theorem filteredMatrix_get (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    (((filteredMatrix C E prepared maps tail lo hi sourceCounts targetCounts base q s window).cells.get i).get j)=
      (filteredCell C E prepared maps tail lo hi sourceCounts targetCounts base q s window
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)).answer := by
  exact materialize_get _ _ _

theorem filteredMatrix_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat) (window : SourceWindow) :
    (filteredMatrix C E prepared maps tail lo hi sourceCounts targetCounts base q s window).work≤
      (1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(cellBudget C E prepared.K+1)) := by
  rw [←MaskedClusterStage.dfa_size C E]
  exact materialize_work _ _ (fun i j=>filteredCell_work C E prepared maps tail lo hi sourceCounts
    targetCounts base q s window _ _)

end REWB.MaskedCluster
