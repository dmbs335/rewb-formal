import REWB.ShortOuterRegression
import REWB.MaskedTraversalIncomingRegression
import REWB.BoundaryRangeCacheRegression
import REWB.MaskedTraversalRetainedRegression
import REWB.MaskedTraversalNeighborRegression
import REWB.ShortOuterBandRegression
import REWB.MaskedTraversalContextRegression
import REWB.OneUseRangeCacheRegression
import REWB.OneUseRangeBorderRegression
import REWB.ResidualDispatchRegression
import REWB.OneUseRangeFarAggregateRegression
import REWB.MaskedTraversalRepairRegression
import REWB.ResidualStripScheduleRegression
import REWB.MaskedTraversalBankReadyRegression
import REWB.BoundaryRangeNearIndexBorderRegression
import REWB.ResidualSeparatedRegression
import REWB.MaskedTraversalDriverRegression
import REWB.MaskedRunCatalogRegression
import REWB.BoundaryRangeNearIndexRegression
import REWB.BoundaryRangeFarIndexRegression
import REWB.MaskedTraversalEdgeRegression
import REWB.BoundaryBorderRegularRegression
import REWB.BoundaryRangeRegression
import REWB.BoundaryBorderWindowRegression
import REWB.MaskedSuffixClassRegression
import REWB.MaskedClusterMutableStoreRegression
import REWB.MaskedClusterDescriptorRegression
import REWB.BoundaryBorderRegression
import REWB.BoundaryApplicationSeparatedRegression
import REWB.MaskedClusterCutRegression
import REWB.MaskedMutableProgressionRegression
import REWB.MaskedSourceFanoutRegression
import REWB.MaskedClusterLeaderRegression
import REWB.MaskedClusterMutableRegression
import REWB.MaskedMutableProgressionBatchRegression
import REWB.MaskedEmptyRegression
import REWB.MaskedEmptyBatchRegression
import REWB
import REWB.ShortSourceRegression
import REWB.BoundaryIndexRegression
import REWB.BoundaryIndexCutsRegression
import REWB.BoundaryIndexMergeRegression
import REWB.BoundaryIndexMixedRegression
import REWB.MaskedFiniteActionRegression
import REWB.MaskedProgressionRegression
import REWB.MaskedCutRegression
import REWB.BoundaryTrieRegression
import REWB.MaskedRunDiscoveryRegression
import REWB.BoundaryApplicationRegression
import REWB.MaskedPeriodicRegression
import REWB.MaskedOrderedRegression
import REWB.MaskedPeriodicTextRegression
import REWB.MaskedOrderedOwnerRegression
import REWB.BoundaryApplicationHeavyRegression
import REWB.MaskedClusterRegression
import REWB.MaskedPeriodicBatchRegression

import REWB.BoundaryApplicationStartRegression

import REWB.MaskedClusterCursorRegression

import REWB.MaskedThresholdRegression

import REWB.MaskedDensityChargeRegression

import REWB.MaskedClusterBankRegression

open REWB

-- Executable semantics, including empty captures and nested overwriting.
example : (State.execute (State.initial ([] : Word Nat))
    (Witness.nested1Trace [] [1] [0] [2] [3] [4] [])).map State.output =
      some [1,0,2,1,3,4,2,1,3] := by decide

example : (State.execute (State.initial ([] : Word Nat))
    (Witness.nested2Trace [] [2] [1] [0] [3] [4] [])).map State.output =
      some [2,1,0,1,3,4,2,1,0,1,3] := by decide

example : (State.execute (State.initial ([] : Word Nat))
    (Witness.independentTrace [] [1] [] [] [] [] [])).map State.uses = some 2 := by decide

example : (State.execute (State.initial ([] : Word Nat)) [.closeCap]).isNone = true := by decide

#print axioms REWB.State.execute_uses
#print axioms REWB.Witness.same_iff
#print axioms REWB.Witness.independent_iff
#print axioms REWB.Witness.nested1_iff
#print axioms REWB.Witness.nested2_iff
#print axioms REWB.classify_distinct_suppliers
#print axioms REWB.regionP1_iff_boundary
#print axioms REWB.regionP2_iff_boundary
#print axioms REWB.regionP1_sound
#print axioms REWB.regionP2_sound
#print axioms REWB.Cost.p1Phase_le
#print axioms REWB.Cost.p2Phase_le


-- Small executable regression examples; all proof terms use kernel reduction.
def allWords : DFA Nat :=
  ⟨1, ⟨0, by decide⟩, fun _ _ => ⟨0, by decide⟩, fun _ => true⟩

def onlyEmpty : DFA Nat :=
  ⟨2, ⟨0, by decide⟩, fun _ _ => ⟨1, by decide⟩, fun q => q.val == 0⟩

def nonEmpty : DFA Nat :=
  ⟨2, ⟨0, by decide⟩, fun _ _ => ⟨1, by decide⟩, fun q => q.val == 1⟩

def cubePattern : FiveDFA Nat :=
  ⟨onlyEmpty, nonEmpty, onlyEmpty, onlyEmpty, onlyEmpty⟩

def nestedPattern : SevenDFA Nat :=
  ⟨onlyEmpty, nonEmpty, onlyEmpty, onlyEmpty, onlyEmpty, onlyEmpty, onlyEmpty⟩

example : Reference.same cubePattern [1,1,1] = true := by decide
example : Reference.same cubePattern [1,2,1] = false := by decide
example : Reference.nested1 nestedPattern [1,1,1] = true := by decide
example : Reference.nested1 nestedPattern [1,1] = false := by decide
example : Reference.nested2 nestedPattern [1,2,1,2] = true := by decide
example : Reference.nested2 nestedPattern [1,2,2,1] = false := by decide
example : MarkedDP.reachEnd onlyEmpty true [] onlyEmpty.initial = true := by decide
example : MarkedDP.reachEnd onlyEmpty false [] onlyEmpty.initial = false := by decide
example : (MarkedDP.summarize nonEmpty nonEmpty false [(1,false),(2,true)]).canSwitch
    nonEmpty.initial = true := by decide
example : (MarkedDP.summarize nonEmpty nonEmpty false [(1,true),(2,false)]).canSwitch
    nonEmpty.initial = false := by decide

#print axioms REWB.TraceOf.executes_balanced
#print axioms REWB.isKUse_iff_traceCount
#print axioms REWB.State.output_without_recall
#print axioms REWB.Reference.same_correct
#print axioms REWB.Reference.independent_correct
#print axioms REWB.Reference.nested1_correct
#print axioms REWB.Reference.nested2_correct
#print axioms REWB.MarkedDP.reachEnd_correct
#print axioms REWB.MarkedDP.canSwitch_correct

-- The maximum includes the nonoverlap limit even for a repeated character.
example : OuterColumn.maxCommon ([1,1,1,1] : Word Nat) 3 4 3 = 1 := by decide
example : OuterColumn.maxCommon ([1,2,1,2] : Word Nat) 2 4 2 = 2 := by decide
example : OuterColumn.maxCommon ([1,2,3,4] : Word Nat) 2 4 2 = 0 := by decide
#print axioms REWB.OuterColumn.common_transport
#print axioms REWB.OuterColumn.maxCommon_isMax
#print axioms REWB.OuterColumn.anchored_iff
#print axioms REWB.OuterColumn.active_succ
#print axioms REWB.OuterColumn.column_correct

-- The terminal mark is independent of the characters inside the queried slice.
example : MarkedTransfer.queryMarkedCut nonEmpty nonEmpty false
    (MarkedTransfer.buildMarkedCut nonEmpty nonEmpty
      [(1,false)] [(2,true)]).1 0 2 (.inl nonEmpty.initial) = some true := by decide
example : MarkedTransfer.queryMarkedCut nonEmpty nonEmpty false
    (MarkedTransfer.buildMarkedCut nonEmpty nonEmpty
      [(1,true)] [(2,false)]).1 0 2 (.inl nonEmpty.initial) = some false := by decide
example : MarkedTransfer.queryMarkedCut onlyEmpty onlyEmpty true
    (MarkedTransfer.buildMarkedCut onlyEmpty onlyEmpty [] []).1
      0 0 (.inl onlyEmpty.initial) = some true := by decide
example : MarkedTransfer.queryMarkedCut onlyEmpty onlyEmpty false
    (MarkedTransfer.buildMarkedCut onlyEmpty onlyEmpty [] []).1
      0 0 (.inl onlyEmpty.initial) = some false := by decide
#print axioms REWB.NestedColumns.nested1_reduced
#print axioms REWB.NestedColumns.nested2_reduced
#print axioms REWB.RangeProducts.queryCut_correct
#print axioms REWB.RangeProducts.cut_cost
#print axioms REWB.FiniteRelation.comp_assoc
#print axioms REWB.MarkedTransfer.run_correct
#print axioms REWB.MatrixTable.denote_product
#print axioms REWB.MarkedTransfer.queryMarkedCut_switch

-- General interval and clipped common suffix regressions.
def wordOps : RangeProducts.Ops (List Nat) :=
  ⟨[], List.append, List.nil_append, List.append_nil, List.append_assoc⟩

def rangeSample : List (List Nat) := [[1],[2],[3],[4],[5]]

example : (DyadicIndex.query wordOps
    (DyadicIndex.buildFor wordOps rangeSample).1 1 4).answer =
    some [2,3,4] := by
  rw [(DyadicIndex.queryFor_spec wordOps rangeSample 1 4 (by decide) (by decide)).1] <;> decide
example : (DyadicIndex.query wordOps
    (DyadicIndex.buildFor wordOps rangeSample).1 4 5).answer =
    some [5] := by
  rw [(DyadicIndex.queryFor_spec wordOps rangeSample 4 5 (by decide) (by decide)).1] <;> decide
example : (DyadicIndex.query wordOps
    (DyadicIndex.buildFor wordOps rangeSample).1 5 5).answer =
    some [] := by
  rw [(DyadicIndex.queryFor_spec wordOps rangeSample 5 5 (by decide) (by decide)).1] <;> decide

-- Runtime regression checks are separate from the kernel proofs above.
#guard (DyadicIndex.query wordOps (DyadicIndex.buildFor wordOps rangeSample).1 1 4).answer == some [2,3,4]
#guard (DyadicIndex.query wordOps (DyadicIndex.buildFor wordOps rangeSample).1 4 5).answer == some [5]
#guard (DyadicIndex.query wordOps (DyadicIndex.buildFor wordOps rangeSample).1 5 5).answer == some []
#guard (DyadicIndex.buildFor wordOps rangeSample).2 == 15

example : LCSTable.commonAt (LCSTable.buildLCS ([1,1,1,1] : Word Nat)).1 4 3 4 =
    some 1 := by decide
example : LCSTable.commonAt (LCSTable.buildLCS ([1,2,1,2] : Word Nat)).1 4 2 4 =
    some 2 := by decide
example : LCSTable.commonAt (LCSTable.buildLCS ([1,2,3,4] : Word Nat)).1 4 2 4 =
    some 0 := by decide
example : (LCSTable.buildLCS ([1,2,1,2] : Word Nat)).2 = 16 := by decide

def markedSample : MarkedDP.MarkedWord Nat :=
  [(0,false),(1,false),(2,true),(0,false)]

example : (IndexedMarked.query nonEmpty nonEmpty false
    (IndexedMarked.build nonEmpty nonEmpty markedSample).1
    1 3 (.inl nonEmpty.initial)).answer = some true := by
  rw [IndexedMarked.query_correct nonEmpty nonEmpty false markedSample 1 3
    (.inl nonEmpty.initial) (by decide) (by decide), MarkedTransfer.run_left] <;> decide
example : (IndexedMarked.query onlyEmpty onlyEmpty true
    (IndexedMarked.build onlyEmpty onlyEmpty ([] : MarkedDP.MarkedWord Nat)).1
    0 0 (.inl onlyEmpty.initial)).answer = some true := by
  rw [IndexedMarked.query_correct onlyEmpty onlyEmpty true [] 0 0
    (.inl onlyEmpty.initial) (by decide) (by decide), MarkedTransfer.run_left] <;> decide
#guard (IndexedMarked.query nonEmpty nonEmpty false
    (IndexedMarked.build nonEmpty nonEmpty markedSample).1
    1 3 (.inl nonEmpty.initial)).answer == some true
#guard (IndexedMarked.query onlyEmpty onlyEmpty true
    (IndexedMarked.build onlyEmpty onlyEmpty ([] : MarkedDP.MarkedWord Nat)).1
    0 0 (.inl onlyEmpty.initial)).answer == some true

#print axioms REWB.DyadicIndex.queryFor_spec
#print axioms REWB.DyadicIndex.build_cells
#print axioms REWB.DyadicIndex.buildFor_cost
#print axioms REWB.LCSTable.commonAt_correct
#print axioms REWB.LCSTable.lcs_comparisons
#print axioms REWB.LCSTable.build_cells
#print axioms REWB.IndexedMarked.p2_query

-- P1: the first marked switch may occur before, at, or after the A reset.
def beforeReset : SevenDFA Nat :=
  ⟨onlyEmpty,nonEmpty,nonEmpty,nonEmpty,onlyEmpty,onlyEmpty,onlyEmpty⟩
def atReset : SevenDFA Nat :=
  ⟨onlyEmpty,nonEmpty,nonEmpty,onlyEmpty,onlyEmpty,onlyEmpty,onlyEmpty⟩
def afterReset : SevenDFA Nat :=
  ⟨nonEmpty,nonEmpty,nonEmpty,onlyEmpty,onlyEmpty,onlyEmpty,onlyEmpty⟩
def markOne : Nat → Bool := fun i => i==1
def markTwo : Nat → Bool := fun i => i==2
#guard P1Index.query beforeReset (P1Index.build beforeReset
    (IndexedMarked.decorate markOne 0 [1,2,3])) false 0 2 3 beforeReset.A.initial == some true
#guard P1Index.query atReset (P1Index.build atReset
    (IndexedMarked.decorate markOne 0 [1,2])) false 0 1 2 atReset.A.initial == some true
#guard P1Index.query afterReset (P1Index.build afterReset
    (IndexedMarked.decorate markTwo 0 [1,2,3])) false 0 1 3 afterReset.A.initial == some true
#guard P1Index.query afterReset (P1Index.build afterReset
    (IndexedMarked.decorate (fun _ => false) 0 [1,2,3])) false 0 1 3 afterReset.A.initial == some false
def emptyP1 : SevenDFA Nat :=
  ⟨onlyEmpty,onlyEmpty,onlyEmpty,onlyEmpty,onlyEmpty,onlyEmpty,onlyEmpty⟩
#guard P1Index.query emptyP1 (P1Index.build emptyP1 []) true 0 0 0 emptyP1.A.initial == some true
#guard P1Index.query emptyP1 (P1Index.build emptyP1 []) false 0 0 0 emptyP1.A.initial == some false

#print axioms REWB.OrderedExit.Machine.run_left
#print axioms REWB.TensorRelation.tensor_comp
#print axioms REWB.P1Index.whole_indices
#print axioms REWB.P1Index.p1_query
#print axioms REWB.MaskScan.readyRow_correct
#print axioms REWB.MaskScan.forward_correct
#print axioms REWB.MaskScan.first2Row_correct


-- Integrated decisions have no oracle parameters. Check both nested forms
-- with nonempty and empty captures and compare against the slow reference.
#guard Integrated.match1 nestedPattern [1,1,1] == true
#guard Integrated.match1 nestedPattern [1,2,1] == false
#guard Integrated.match2 nestedPattern [1,2,1,2] == true
#guard Integrated.match2 nestedPattern [1,2,2,1] == false
#guard Integrated.match1 emptyP1 [] == true
#guard Integrated.match2 emptyP1 [] == true
#guard Integrated.match1 emptyP1 [1] == false
#guard Integrated.match2 emptyP1 [1] == false

def twoNonempty : SevenDFA Nat :=
  ⟨onlyEmpty,nonEmpty,nonEmpty,onlyEmpty,onlyEmpty,onlyEmpty,onlyEmpty⟩
#guard Integrated.match1 twoNonempty [1,0,1,1] == true
#guard Integrated.match2 twoNonempty [0,1,1,0,1,1] == true

def binaryWords : Nat → List (Word Nat)
  | 0 => [[]]
  | n+1 => [] :: ((binaryWords n).flatMap (fun w => [0::w,1::w]))

#guard (binaryWords 3).all (fun w =>
  Integrated.match1 twoNonempty w == Reference.nested1 twoNonempty w &&
  Integrated.match2 twoNonempty w == Reference.nested2 twoNonempty w)

#print axioms REWB.IntervalDFA.lookup_correct
#print axioms REWB.IntervalDFA.countedBuild_cost
#print axioms REWB.SeedBuckets.build_correct
#print axioms REWB.OuterTables.column_correct
#print axioms REWB.OuterTables.readyAt_correct
#print axioms REWB.Integrated.match1_correct
#print axioms REWB.Integrated.match2_correct

#guard (EndpointCounts.match1 twoNonempty [1,0,1,1]).1 == true
#guard (EndpointCounts.match2 twoNonempty [0,1,1,0,1,1]).1 == true
#print axioms REWB.EndpointCounts.match1_spec
#print axioms REWB.EndpointCounts.match2_spec


-- Direct-addressed blocks: test noncommutative products, truncated and
-- empty final blocks, and both integrated decisions.
def markedLetter (x : Nat × Bool) : List Nat :=
  [x.1 + (if x.2 then 10 else 0)]

def blockSample := BlockIndex.prepare wordOps markedLetter [1,2,3,4,5] 2
def blockSampleCol := BlockIndex.buildColumn wordOps blockSample markTwo
#guard BlockIndex.query wordOps blockSample blockSampleCol 0 5 == some [1,2,13,4,5]
#guard BlockIndex.query wordOps blockSample blockSampleCol 1 4 == some [2,13,4]
#guard BlockIndex.query wordOps blockSample blockSampleCol 2 3 == some [13]
#guard BlockIndex.query wordOps blockSample blockSampleCol 5 5 == some []
def exactBlockSample := BlockIndex.prepare wordOps markedLetter [1,2,3,4] 2
def exactBlockCol := BlockIndex.buildColumn wordOps exactBlockSample markTwo
#guard BlockIndex.query wordOps exactBlockSample exactBlockCol 0 4 == some [1,2,13,4]
#guard BlockIndex.query wordOps exactBlockSample exactBlockCol 4 4 == some []

#guard BlockMatcher.match1With twoNonempty [1,0,1,1] 2 == true
#guard BlockMatcher.match2With twoNonempty [0,1,1,0,1,1] 2 == true
#guard BlockMatcher.match1 emptyP1 [] == true
#guard BlockMatcher.match2 emptyP1 [] == true
#guard (binaryWords 3).all (fun w =>
  BlockMatcher.match1With twoNonempty w 2 == Reference.nested1 twoNonempty w &&
  BlockMatcher.match2With twoNonempty w 2 == Reference.nested2 twoNonempty w)

#print axioms REWB.FlatIndex.query_correct
#print axioms REWB.Microblock.countedDictionary_cost
#print axioms REWB.BlockIndex.query_correct
#print axioms REWB.BlockMatcher.match1_correct
#print axioms REWB.BlockMatcher.match2_correct


-- Backward liveness through overwrite, nesting, and a repeated capture.
def overwritePlan : Plan Nat :=
  .seq (.cap (.literal [7]))
    (.seq (.cap (.literal [1])) (.seq (.cap (.seq .recall (.literal [2]))) .recall))

#guard (overwritePlan.prune false).2.caps == 2
#guard (overwritePlan.prune false).2.refs == 2
#guard (overwritePlan.prune false).2.eval [] == overwritePlan.eval []
-- In this example the outgoing value also happens to be unchanged,
-- because the last event reads the last retained capture.
#guard ((overwritePlan.prune false).2.code.filterMap controlOf).length == 6

def starExpr : Expr Nat := .star (.capture (.atom allWords)) ⋙ .reference
def starPlan : Plan Nat :=
  .seq (.seq (.cap (.literal [7])) (.seq (.cap (.literal [1])) .nil)) .recall

theorem starPlan_derivation : PlanOf starExpr starPlan := by
  exact .seq (.starCons (.capture (.atom allWords [7] (by rfl)))
    (.starCons (.capture (.atom allWords [1] (by rfl))) (.starNil _))) .reference

#guard (starPlan.prune false).2.caps == 1
#guard (starPlan.prune false).2.eval [] == ([7,1,1],[1])

example : LiveCompiler.denote (LiveCompiler.compiled starExpr)
    [.inl 7,.inr .openCap,.inl 1,.inr .closeCap,.inr .recall] := by
  apply (LiveCompiler.compiled_correct _ _).mpr
  exact ⟨false,starPlan,starPlan_derivation,rfl,rfl⟩

example : MatchesWithin starExpr [7,1,1] 1 := by
  apply (matches_iff_plan _ _ _).mpr
  exact ⟨starPlan,starPlan_derivation,by decide,rfl⟩

#print axioms REWB.Plan.execute_events
#print axioms REWB.Plan.prune_eval
#print axioms REWB.Plan.prune_budget
#print axioms REWB.matches_iff_pruned
#print axioms REWB.matches_iff_skeletons
#print axioms REWB.LiveLanguage.shape_iff_walk
#print axioms REWB.LiveCompiler.compile_correct
#print axioms REWB.LiveCompiler.match_compiled


-- Period/phase and finite-orbit compression.
def twoPhaseText (i : Nat) : Nat := i%2

example : Periodic.Period twoPhaseText 8 2 := by
  intro i hi
  unfold twoPhaseText
  omega

#guard Periodic.segment twoPhaseText 1 7 ==
  Periodic.repeatWord (Periodic.segment twoPhaseText 1 2) 3 ++ [1]

def parityDFA : DFA Nat :=
  ⟨2,⟨0,by decide⟩,fun q _=>⟨(q.val+1)%2,by omega⟩,fun q=>q.val==0⟩

def parityDescriptor := Periodic.factorDescriptor parityDFA (fun _=>0) 0 1 0
#guard (parityDescriptor.map (fun d=>(d.threshold,d.period,d.initialCounts,d.residues))) ==
  some (0,2,[],[0])
#guard (parityDescriptor.map (fun d=>d.test 100)) == some true
#guard (parityDescriptor.map (fun d=>d.test 101)) == some false
#guard (FiniteOrbit.compress (FiniteRelation.finEnum 3)
  (fun q : Fin 3 => if q.val==0 then ⟨1,by decide⟩ else ⟨2,by decide⟩)
  (⟨0,by decide⟩ : Fin 3) (fun q=>q.val==0 || q.val==2)).map
    (fun d=>(d.threshold,d.period,d.initialCounts,d.residues)) == some (2,1,[0],[0])

#print axioms REWB.Periodic.fineWilf
#print axioms REWB.Periodic.overlap_shift_multiple
#print axioms REWB.Periodic.maximal_equality_run
#print axioms REWB.Periodic.compress_factor
#print axioms REWB.Periodic.compressed_dfa
#print axioms REWB.FiniteOrbit.compress_spec
#print axioms REWB.FiniteOrbit.descriptor_ap
#print axioms REWB.Periodic.factorDescriptor_spec
#print axioms REWB.Periodic.dense_consecutive_gap
#print axioms REWB.Periodic.separated_cluster_gap
#print axioms REWB.Periodic.equal_long_factor_same_phase


#print axioms REWB.Periodic.coordinate_length
#print axioms REWB.Periodic.coordinate_descriptor
#print axioms REWB.Periodic.factor_equality
#print axioms REWB.Periodic.regularCode_iff
#print axioms REWB.Periodic.equalityCode_iff
#print axioms REWB.Periodic.system_iff
#print axioms REWB.Periodic.contextual_accepts


-- Integer projection. No enumeration of the numeric RHS range.
namespace ProjectionRegression
open REWB.AffineProjection

def evenEquation (v : Int) : Formula :=
  [[.le ((Aff.scale 2 (.var 0)).sub (.lit v)),
    .le ((Aff.lit v).sub (.scale 2 (.var 0)))]]
#guard solve 1 (evenEquation 1000000) [] == true
#guard solve 1 (evenEquation 1000001) [] == false
#guard solve 1 (evenEquation (-1000000)) [] == true
#guard solve 1 (evenEquation (-1000001)) [] == false

def upperOnly : Formula :=
  [[.le (.add (.var 0) (.lit 1000000)),
    .dvd 3 ((Aff.var 0).sub (.lit 1))]]
#guard solve 1 upperOnly [] == true

def relation : Formula :=
  [[.le (((Aff.var 0).sub (.var 1)).sub (.lit 1)),
    .le ((Aff.lit 1).sub ((Aff.var 0).sub (.var 1))),
    .dvd 2 (.var 0)]]
def projected : Formula := project 1 relation
#guard decideFormula projected [2] == false
#guard decideFormula projected [3] == true
#guard decideFormula projected [-3] == true

def demoDescriptor : FiniteOrbit.Descriptor := ⟨2,3,[1],[1]⟩
def demoFormula := descriptorFormula demoDescriptor (.var 0)
#guard decideFormula demoFormula [1] == true
#guard decideFormula demoFormula [2] == false
#guard decideFormula demoFormula [3] == true
#guard decideFormula demoFormula [6] == true
#guard decideFormula demoFormula [7] == false

end ProjectionRegression

#print axioms REWB.IntegerProjection.finite_elimination
#print axioms REWB.IntegerProjection.candidates_length
#print axioms REWB.AffineProjection.Norm.eliminate_correct
#print axioms REWB.AffineProjection.Norm.eliminate_length
#print axioms REWB.AffineProjection.normalize_correct
#print axioms REWB.AffineProjection.eliminateConj_correct
#print axioms REWB.AffineProjection.project_correct
#print axioms REWB.AffineProjection.solve_correct
#print axioms REWB.AffineProjection.descriptorFormula_correct


-- Fixed phase constraint regression. These tests evaluate the generated
-- DNF at selected coordinates, not the full eight-variable elimination.
namespace FixedPhaseRegression
open REWB.PhaseSolver REWB.AffineProjection

def a0 : Endpoint := (.var 0,0)
def b0 : Endpoint := (.var 1,0)
def c1 : Endpoint := (.var 2,1)
def d1 : Endpoint := (.var 3,1)
def c0 : Endpoint := (.var 2,0)
def d0 : Endpoint := (.var 3,0)

#guard decideFormula (orderFormula 2 8 a0 b0) [1,2] == true
#guard decideFormula (orderFormula 2 8 a0 b0) [2,1] == false
#guard decideFormula (orderFormula 2 8 a0 b0) [-1,1] == false
#guard decideFormula (orderFormula 2 8 a0 b0) [0,5] == false

#guard decideFormula (equalFormula 2 8 twoPhaseText a0 b0 c0 d0) [0,1,2,3] == true
#guard decideFormula (equalFormula 2 8 twoPhaseText a0 b0 c0 d0) [0,1,2,4] == false
#guard decideFormula (equalFormula 2 8 twoPhaseText a0 b0 c1 d1) [0,1,2,3] == false
#guard decideFormula (equalFormula 2 8 twoPhaseText a0 b0 c1 d1) [0,0,1,1] == true

#guard (P2Periodic.choices 2).length == 32
#guard (P2Periodic.choices 3).length == 243

-- P2 witness: a single-symbol inner capture, then its copy, and a
-- length-two outer capture copied once. Both copies have phase zero.
def testP2 : SevenDFA Nat :=
  ⟨onlyEmpty,onlyEmpty,nonEmpty,onlyEmpty,onlyEmpty,onlyEmpty,onlyEmpty⟩

def sampleLayout : P2Periodic.Layout Nat := ⟨0,0,1,1,2,2,2,4⟩
def sampleFormula :=
  compileSystem 1 4 (fun _=>1) (P2Periodic.constraints testP2 1 4 [] []
    (P2Periodic.endpoints (P2Periodic.phaseOf 1 sampleLayout)))
#guard decideFormula sampleFormula (P2Periodic.envOf 1 sampleLayout) == true
#guard decideFormula sampleFormula [0,0,1,1,2,2,2,3] == false

#guard (project 1 (ProjectionRegression.evenEquation 1000000)).length ==
  (project 1 (ProjectionRegression.evenEquation (-1000001))).length

end FixedPhaseRegression

#print axioms REWB.PhaseSolver.Endpoint.bound_correct
#print axioms REWB.PhaseSolver.order_iff
#print axioms REWB.PhaseSolver.regularFormula_correct
#print axioms REWB.PhaseSolver.equalityCore_correct
#print axioms REWB.PhaseSolver.solveSystem_correct
#print axioms REWB.P2Periodic.plain_iff
#print axioms REWB.P2Periodic.solveAt_correct
#print axioms REWB.P2Periodic.solveAt_sound
#print axioms REWB.P2Periodic.solveAt_complete
#print axioms REWB.P2Periodic.choices_length
#print axioms REWB.P2Periodic.phase_family
#print axioms REWB.P2Periodic.solveFamily_sound
#print axioms REWB.P2Periodic.solveFamily_complete_long
#print axioms REWB.AffineProjection.LiteralShape.project_branches


namespace PeriodicJoinRegression
open REWB.AffineProjection REWB.PhaseSolver

def cache := PeriodicCache.build parityDFA twoPhaseText 2

#guard cache.2 == 8
#guard (PeriodicCache.descriptor parityDFA cache.1 2 1 1).map (fun d=>d.test 100) == some false
#guard (PeriodicCache.descriptor parityDFA cache.1 2 1 0).map (fun d=>d.test 100) == some true

def sourcePattern : SevenDFA Nat :=
  ⟨allWords,nonEmpty,onlyEmpty,onlyEmpty,onlyEmpty,onlyEmpty,onlyEmpty⟩
def sourceFormula := P1Source.formula sourcePattern (fun _=>1) 4 1 4 0 0 [] []
#guard decideFormula sourceFormula [3] == true
#guard decideFormula sourceFormula [5] == false

-- Join a residue class with a singleton. Large constants do not enlarge
-- the candidate set of a one-variable projection.
def evenCounts : Formula := [progression (.var 0) 0 2]
#guard P1Join.join evenCounts [exactCount (.var 0) 1000000] == true
#guard P1Join.join evenCounts [exactCount (.var 0) 1000001] == false

end PeriodicJoinRegression

#print axioms REWB.PeriodicCache.build_cost
#print axioms REWB.PeriodicCache.lookup_correct
#print axioms REWB.PeriodicCache.descriptor_correct
#print axioms REWB.CachedP2.solveFamily_eq
#print axioms REWB.P1Target.projection_correct
#print axioms REWB.P1Target.projected_join_sound
#print axioms REWB.P1Source.source_sound
#print axioms REWB.P1Source.join_sources
#print axioms REWB.P1Join.join_correct
#print axioms REWB.P1Join.decidePair_sound
#print axioms REWB.P2Periodic.fixed_formula_bound


-- Residue intervals, exact-key joins and chronological cut checks.
namespace BatchJoinRegression
open REWB.AffineProjection

def evens : Formula := [progression (.var 0) 0 2]
def million : Formula := [exactCount (.var 0) 1000000]
def oddMillion : Formula := [exactCount (.var 0) 1000001]

#guard (KeyedJoin.batch 2 1000001 [⟨7,evens⟩] [⟨7,million⟩]).1 == true
#guard (KeyedJoin.batch 2 1000001 [⟨7,evens⟩] [⟨8,million⟩]).1 == false
#guard (KeyedJoin.batch 2 1000001 [⟨7,evens⟩] [⟨7,oddMillion⟩]).1 == false
#guard (KeyedJoin.batch 2 999999 [⟨7,evens⟩] [⟨7,million⟩]).1 == false
#guard (IntervalSweep.batch [⟨10,2⟩,⟨-5,4⟩,⟨15,25⟩] [⟨9,14⟩]).1 == false
#guard (IntervalSweep.batch [⟨15,25⟩,⟨-5,4⟩] [⟨25,26⟩]).1 == true

def s (a : Nat) : TimedJoin.TimedEntry := ⟨a,⟨7,evens⟩⟩
def t (a : Nat) : TimedJoin.TimedEntry := ⟨a,⟨7,million⟩⟩

#guard (TimedJoin.cross onlyEmpty [1,2] [3] 2 1000001 [s 2] [t 2]).1 == true
#guard (TimedJoin.cross onlyEmpty [1,2] [3] 2 1000001 [s 1] [t 2]).1 == false
#guard (TimedJoin.cross nonEmpty [1,2] [3] 2 1000001 [s 1] [t 2]).1 == true
#guard (TimedJoin.cross nonEmpty [1,2] [3] 2 1000001 [s 2] [t 3]).1 == true
#guard (TimedJoin.cross nonEmpty [1,2] [3] 2 1000001 [s 2] [t 2]).1 == false

end BatchJoinRegression

#print axioms REWB.ExponentIntervals.clip_correct
#print axioms REWB.ExponentIntervals.windows_correct
#print axioms REWB.ExponentIntervals.allWindows_length
#print axioms REWB.IntervalSweep.batch_correct
#print axioms REWB.IntervalSweep.batch_cost
#print axioms REWB.KeyedJoin.batch_correct
#print axioms REWB.KeyedJoin.batch_cost
#print axioms REWB.DFACut.crossing_accepts
#print axioms REWB.TimedJoin.cross_correct
#print axioms REWB.TimedJoin.cross_cost
#print axioms REWB.TimedJoin.split_cover


-- Maximal runs and their primitive-square occurrence charges.
namespace RunCoverageRegression
open REWB.RunGeometry REWB.RunExtension REWB.RunBudget

def alternating : Nat→Nat := fun i=>i%2
def twoRuns : Nat→Nat := fun i=>if i<4 then 0 else 1

#guard squareTest alternating 8 2 2 == true
#guard squareTest alternating 8 0 4 == false
#guard squareTest alternating 8 5 2 == false
#guard extend alternating 8 2 2 == (⟨0,8,2⟩ : Bounds)
#guard enumerate alternating 8 == ([⟨0,8,2⟩] : List Bounds)
#guard (enumerate twoRuns 8).length == 2
#guard totalMass (enumerate alternating 8) == 5
#guard totalMass (enumerate twoRuns 8) == 6
#guard GridCoverage.regionLeft alternating 2 5 == 0
#guard GridCoverage.regionEnd alternating 8 2 5 == 6
#guard (GridCoverage.probes 100 10).length == 1111

end RunCoverageRegression

#print axioms REWB.RunGeometry.least_factor
#print axioms REWB.RunGeometry.unique_overlap
#print axioms REWB.RunGeometry.square_start_unique
#print axioms REWB.RunExtension.extend_valid
#print axioms REWB.RunExtension.enumerate_correct
#print axioms REWB.RunExtension.dedup_nodup
#print axioms REWB.GridCoverage.probes_length
#print axioms REWB.GridCoverage.run_grid
#print axioms REWB.RunGeometry.three_squares
#print axioms REWB.RunBudget.totalMass_bound
#print axioms REWB.RunBudget.cubic_phase_bound
#print axioms REWB.RunBudget.low_exponent_equality

-- Bounded-period enumeration, cached boundaries, and uniform projection.
namespace SmallPeriodRegression
open REWB.RunGeometry RunCoverageRegression

#guard (SmallPeriodRuns.enumerate alternating 8 0).1 == []
#guard (SmallPeriodRuns.enumerate alternating 8 1).1 == []
#guard (SmallPeriodRuns.enumerate alternating 8 2).1 == ([⟨0,8,2⟩] : List Bounds)
#guard (SmallPeriodRuns.enumerate alternating 8 8).1 == ([⟨0,8,2⟩] : List Bounds)
#guard (SmallPeriodRuns.enumerate twoRuns 8 1).1 == ([⟨0,4,1⟩,⟨4,8,1⟩] : List Bounds)
#guard (SmallPeriodRuns.enumerate alternating 0 4).1 == []
#guard (SmallPeriodRuns.cubic alternating 4 2).isEmpty
#guard (SmallPeriodRuns.cubic alternating 6 2) == ([⟨0,6,2⟩] : List Bounds)
#guard (SmallPeriodRuns.ends alternating 2 0 6).1 == [6,6,6,6,6,6,6]
#guard (SmallPeriodRuns.ends twoRuns 1 0 7).1 == [3,3,3,3,7,7,7,7]
#guard (PhaseEqualityCache.build alternating 2).2 == 8
#guard (BoundaryContexts.build nestedPattern [1,2,1,2]).2 == 15
#guard (SmallPeriodP2.solve nestedPattern alternating 0 0).accepted == false

end SmallPeriodRegression

#print axioms REWB.ControlShapes.prune_check
#print axioms REWB.ControlShapes.matches_iff_shapes
#print axioms REWB.ControlShapes.matches_iff_shaped_codes
#print axioms REWB.UniformPhaseBounds.p2_all_stages_bound
#print axioms REWB.UniformPhaseBounds.p2_projection_bound
#print axioms REWB.UniformPhaseBounds.p1Modulus_pos
#print axioms REWB.UniformPhaseBounds.p1_source_compatible
#print axioms REWB.UniformPhaseBounds.p1_target_compatible
#print axioms REWB.UniformPhaseBounds.p1_target_windows
#print axioms REWB.UniformJoin.localSource_with_gap
#print axioms REWB.UniformJoin.run_correct
#print axioms REWB.UniformJoin.run_counts
#print axioms REWB.PhaseEqualityCache.build_cost
#print axioms REWB.PhaseEqualityCache.equalFormula_eq
#print axioms REWB.FullyCachedP2.solveFamily_eq
#print axioms REWB.FullyCachedP2.countedPhases_cost
#print axioms REWB.BoundaryContexts.prepareAt_correct
#print axioms REWB.BoundaryContexts.countedPrepareAt_cost
#print axioms REWB.SmallPeriodRuns.enumerate_mem
#print axioms REWB.SmallPeriodRuns.enumerate_nodup
#print axioms REWB.SmallPeriodRuns.enumerate_cost
#print axioms REWB.SmallPeriodRuns.cubic_phase_bound
#print axioms REWB.SmallPeriodP2.solve_sound
#print axioms REWB.SmallPeriodP2.solve_complete
#print axioms REWB.SmallPeriodP2.solve_counts

-- Complete source-language decisions and actual exact-word identifiers.
namespace CompletedPipelineRegression

#guard FullMatcher.run [CompleteNormalization.Form.regular allWords] [1,2,3]
#guard FullMatcher.run [CompleteNormalization.Form.once onlyEmpty nonEmpty onlyEmpty onlyEmpty] [1,1]
#guard !(FullMatcher.run [CompleteNormalization.Form.once onlyEmpty nonEmpty onlyEmpty onlyEmpty] [1,2])
#guard ArrayText.read ([1,2,3] : Word Nat).toArray 99 10 == 99
#guard Periodic.segment (ArrayText.read ([1,2,3] : Word Nat).toArray 99) 0 3 == [1,2,3]

def bit0 : Fin 2 := ⟨0,by decide⟩
def bit1 : Fin 2 := ⟨1,by decide⟩
def assigned0 := ExactKeys.assign (ExactKeys.initial : ExactKeys.Registry 2) [bit0,bit1]
def assigned1 := ExactKeys.assign assigned0.registry [bit0,bit1]
def assigned2 := ExactKeys.assign assigned1.registry [bit1,bit0]

#guard assigned0.rank == assigned1.rank
#guard assigned0.registry.next == assigned1.registry.next
#guard assigned1.rank != assigned2.rank
#guard ExactKeys.lookup assigned2.registry.tree [bit0,bit1] == some assigned0.rank
#guard (P1PhaseFamily.targets 2 5).length == 48
#guard (P1SourceFamily.choices 2 5).length == 12
#guard P1SourceFamily.residue 3 8 1 == 1

end CompletedPipelineRegression

#print axioms REWB.RegularDFA.compile_correct
#print axioms REWB.CompleteNormalization.normalization
#print axioms REWB.CompleteNormalization.pieces_normal
#print axioms REWB.FullMatcher.correctMatcher
#print axioms REWB.FullMatcher.compile_correct
#print axioms REWB.ExactKeys.internMany_exact
#print axioms REWB.ExactKeys.internMany_cost
#print axioms REWB.ExactKeys.buildRunTables_key
#print axioms REWB.ExactKeys.keyCode_exact
#print axioms REWB.ExactKeys.buildRunTables_cubic_cost
#print axioms REWB.CountedProjection.solve_uniform_steps
#print axioms REWB.CountedProjection.search_value
#print axioms REWB.CountedProjection.search_uniform_steps
#print axioms REWB.SmallPeriodP2.solve_projection_steps
#print axioms REWB.ProjectionMagnitude.p2_all_stage_bits
#print axioms REWB.P1SourceFamily.long_source_complete
#print axioms REWB.P1GlobalJoin.long_complete
#print axioms REWB.P1Events.code_exact
#print axioms REWB.P1Events.generated_sizes
#print axioms REWB.P1Events.generated_counts
#print axioms REWB.P1Events.generated_key_work
#print axioms REWB.SmallPeriodP1.solve_sound
#print axioms REWB.SmallPeriodP1.solve_complete_long
#print axioms REWB.SmallPeriodP1.solve_counts
#print axioms REWB.ArrayText.solveWord_sound
#print axioms REWB.ArrayText.solveWord_projection_steps
#print axioms REWB.ProjectionMagnitude.p1_target_all_stage_bits
#print axioms REWB.ProjectionMagnitude.p1_cached_source_bits_at
#print axioms REWB.CountedSort.sort_value
#print axioms REWB.CountedSort.sort_steps
#print axioms REWB.CountedJoin.run_value
#print axioms REWB.CountedJoin.run_steps
#print axioms REWB.CountedSmallPeriodP1.solve_sound
#print axioms REWB.CountedSmallPeriodP1.solve_complete_long
#print axioms REWB.CountedSmallPeriodP1.solve_prepare_counts
#print axioms REWB.CountedSmallPeriodP1.solve_sort_steps
#print axioms REWB.CountedSmallPeriodP1.solve_modulus
#print axioms REWB.CountedSmallPeriodP1.solve_modulus_steps_bound

#guard (CountedSort.sort (fun a b : Nat=>a≤b) [7,1,5,1,9,0,2]).1 == [0,1,1,2,5,7,9]
#guard (CountedSort.sort (fun a b : Nat=>a≤b) [7,1,5,1,9,0,2]).2 == 85

#print axioms REWB.P1ShortBranch.solve_sound
#print axioms REWB.P1ShortBranch.solve_complete
#print axioms REWB.P1Cubic.solve_sound
#print axioms REWB.P1Cubic.solve_complete
#print axioms REWB.ActualModulus.build_pos
#print axioms REWB.ActualModulus.build_good
#print axioms REWB.ActualModulus.build_le
#print axioms REWB.ActualModulus.build_steps_bound
#print axioms REWB.CountedShortBranch.solve_sound
#print axioms REWB.CountedShortBranch.solve_complete
#print axioms REWB.CountedP1Cubic.solve_sound
#print axioms REWB.CountedP1Cubic.solve_complete
#print axioms REWB.ThresholdBudget.rounded_lower
#print axioms REWB.ThresholdBudget.rounded_upper
#print axioms REWB.ThresholdBudget.ledger_target

#guard (ActualModulus.formula [[.dvd 6 (.lit 0),.dvd 6 (.lit 0),.dvd 4 (.lit 0)]]).1 == 12
#guard (ActualModulus.formula (List.replicate 1000 [])).2 == 2001
#guard AffineProjection.multiplier [.le (.scale 2 (.var 0)),.le (.scale 2 (.var 0))] == 2

#print axioms REWB.PeriodicAccounting.measured_target
#print axioms REWB.SmallPeriodP2.phases_eq_phasesTR
#print axioms REWB.SmallPeriodP2.runs_eq_runsTR
#print axioms REWB.GlobalSemanticCoverage.p1_cover
#print axioms REWB.GlobalSemanticCoverage.p2_cover
#print axioms REWB.MaskedReporting.report_correct
#print axioms REWB.MaskedReporting.report_calls
#print axioms REWB.MaskedReporting.report_totalWork
#print axioms REWB.MaskedReporting.reportMasked_exhausts
#print axioms REWB.MaskedReporting.SharedTargetRegression.three_sources
#print axioms REWB.MaskedEventBudget.insert_edge_repair
#print axioms REWB.MaskedEventBudget.build_balance
#print axioms REWB.MaskedEventBudget.transfer_bound
#print axioms REWB.MaskedEventBudget.records_bound
#print axioms REWB.MaskedEventBudget.oneShot_bound
#print axioms REWB.MaskedEventBudget.unaryRebuild_quadratic
#print axioms REWB.BoundaryIndex.Tree.recolor_good
#print axioms REWB.BoundaryIndex.Tree.recolor_steps
#print axioms REWB.BoundaryIndex.Tree.replace_leaves
#print axioms REWB.BoundaryIndex.Tree.queryPrefix_correct
#print axioms REWB.BoundaryIndex.Tree.queryPrefix_steps
#print axioms REWB.BoundaryIndex.TokenIndex.queryFor_correct
#print axioms REWB.BoundaryIndex.TokenIndex.buildFor_steps
#print axioms REWB.BoundaryIndex.Cuts.query_correct
#print axioms REWB.BoundaryIndex.Cuts.query_bounds
#print axioms REWB.BoundaryIndex.FixedEnd.reverse_query_correct
#print axioms REWB.BoundaryIndex.MergeSchedule.execute_active
#print axioms REWB.BoundaryIndex.MergeSchedule.execute_transfers
#print axioms REWB.BoundaryIndex.MergeBuild.run_active
#print axioms REWB.BoundaryIndex.MergeBuild.run_trans
#print axioms REWB.BoundaryIndex.MergeBuild.run_auto_steps
#print axioms REWB.BoundaryIndex.Regression.fresh_color_survives
#print axioms REWB.BoundaryIndex.MergeRegression.overlapping_positions
#print axioms REWB.BoundaryIndex.MergeRegression.prior_version
#print axioms REWB.RankIndex.pairBits_exact
#print axioms REWB.RankIndex.build_row
#print axioms REWB.RankIndex.build_work
#print axioms REWB.LCEIndex.lceMeasured_correct
#print axioms REWB.LCEIndex.lcsMeasured_correct
#print axioms REWB.LCEIndex.lceMeasured_work
#print axioms REWB.LCEIndexArray.lceWord_correct
#print axioms REWB.LCEIndexArray.lcsWord_correct
#print axioms REWB.IndexedGrid.generate_sound
#print axioms REWB.IndexedGrid.generate_complete
#print axioms REWB.IndexedGrid.generate_counts
#print axioms REWB.IndexedGridAccounting.measured_target
#print axioms REWB.RankIndexDivisors.pairs_mem
#print axioms REWB.RankIndexDivisors.pairs_length
#print axioms REWB.RankIndexDivisors.buckets_mem
#print axioms REWB.RankIndexDivisors.buckets_work
#print axioms REWB.RankIndexPeriod.fromStrip_spec
#print axioms REWB.RankIndexPeriod.fromStrip_work
#print axioms REWB.RankIndexRuns.generate_complete
#print axioms REWB.RankIndexRuns.generate_counts
#print axioms REWB.RunDedup.run_mem
#print axioms REWB.RunDedup.run_nodup
#print axioms REWB.RunDedup.run_work
#print axioms REWB.RunDedup.run_rank_bound
#print axioms REWB.RankIndexSchedule.totalMass_bound
#print axioms REWB.RankIndexSchedule.low_bound
#print axioms REWB.RankIndexSchedule.large_bound
#print axioms REWB.RankIndexScheduleAccounting.measured_target
#print axioms REWB.IndexedGlobalCoverage.p1_cover
#print axioms REWB.IndexedGlobalCoverage.p2_cover
#print axioms REWB.IntervalDFA.countedPrefix_eq_countedPrefixTR
#print axioms REWB.BoundaryContexts.suffix_eq_suffixTR
#print axioms REWB.BoundaryIndex.Mixed.execute_mass
#print axioms REWB.BoundaryIndex.Mixed.execute_transfers
#print axioms REWB.BoundaryIndex.Mixed.lightHeight_bound
#print axioms REWB.BoundaryIndex.Mixed.run_active
#print axioms REWB.BoundaryIndex.Mixed.run_trans
#print axioms REWB.BoundaryIndex.Mixed.run_auto_steps
#print axioms REWB.BoundaryIndex.MixedRegression.mass_drives_choice
#print axioms REWB.MaskedFiniteAction.View.reindex_comp
#print axioms REWB.MaskedFiniteAction.View.reindex_product
#print axioms REWB.MaskedFiniteAction.Tree.reindex_good
#print axioms REWB.MaskedFiniteAction.Tree.reindex_steps
#print axioms REWB.MaskedFiniteAction.Tree.replace_leaves
#print axioms REWB.MaskedFiniteAction.Tree.replace_steps
#print axioms REWB.MaskedFiniteAction.Tree.queryPrefix_correct
#print axioms REWB.MaskedFiniteAction.Tree.queryPrefix_steps
#print axioms REWB.MaskedFiniteAction.Tree.querySuffix_correct
#print axioms REWB.MaskedFiniteAction.Tree.querySuffix_steps
#print axioms REWB.MaskedFiniteAction.Tree.queryRange_correct
#print axioms REWB.MaskedFiniteAction.Tree.queryRange_steps
#print axioms REWB.MaskedFiniteAction.Regression.interval_order
#print axioms REWB.MaskedFiniteAction.Maps.count_eq
#print axioms REWB.MaskedFiniteAction.Maps.decode_encode
#print axioms REWB.MaskedFiniteAction.Maps.localAnchor_shortening
#print axioms REWB.MaskedProgression.build_correct
#print axioms REWB.MaskedProgression.build_slots_exact
#print axioms REWB.MaskedProgression.build_arithmetic_exact
#print axioms REWB.MaskedProgression.build_counts_le
#print axioms REWB.MaskedProgression.grid_build_correct
#print axioms REWB.MaskedProgression.ap_build_correct
#print axioms REWB.MaskedProgression.ap_work
#print axioms REWB.MaskedProgression.Regression.ap_eq_direct
#print axioms REWB.MaskedCut.mul_assoc
#print axioms REWB.MaskedCut.trace_strict
#print axioms REWB.MaskedCut.trace_closed
#print axioms REWB.MaskedCut.Index.query_correct
#print axioms REWB.MaskedCut.Index.query_bounds
#print axioms REWB.MaskedCut.Rotations.batch_correct
#print axioms REWB.MaskedCut.Rotations.batch_bounds
#print axioms REWB.MaskedCut.DFAIndex.jointEnum_length
#print axioms REWB.MaskedCut.DFAIndex.query_correct
#print axioms REWB.MaskedCut.DFAIndex.queryConstrained_correct
#print axioms REWB.MaskedCut.DFAIndex.queryConstrained_bounds
#print axioms REWB.MaskedCut.Regression.query_eq_direct
#print axioms REWB.MaskedCut.Regression.correlated_cut
#print axioms REWB.BoundaryTrie.Sort.sort_sorted
#print axioms REWB.BoundaryTrie.Sort.sort_steps
#print axioms REWB.BoundaryTrie.Search.array_partition
#print axioms REWB.BoundaryTrie.prepare_sorted
#print axioms REWB.BoundaryTrie.prepare_work
#print axioms REWB.BoundaryTrie.Build.run_correct
#print axioms REWB.BoundaryTrie.Build.run_nodes
#print axioms REWB.BoundaryTrie.Build.run_paths
#print axioms REWB.BoundaryTrie.Build.run_path_lcp
#print axioms REWB.BoundaryTrie.Build.run_work
#print axioms REWB.BoundaryTrie.Tree.edge_depths
#print axioms REWB.BoundaryTrie.Tree.locus_first
#print axioms REWB.BoundaryTrie.Tree.locus_complete
#print axioms REWB.BoundaryTrie.Tree.locate_correct
#print axioms REWB.BoundaryTrie.Build.run_locus_complete
#print axioms REWB.MaskedRunDiscovery.dense_least
#print axioms REWB.MaskedRunDiscovery.candidate_dense
#print axioms REWB.MaskedRunDiscovery.discover_dense
#print axioms REWB.MaskedRunDiscovery.discover_work
#print axioms REWB.MaskedRunDiscovery.dense_primitive_square
#print axioms REWB.MaskedRunDiscovery.complete_consecutive
#print axioms REWB.MaskedRunDiscovery.completed_class_discovery
#print axioms REWB.MaskedRunDiscovery.equal_depth_skipped
#print axioms REWB.MaskedRunDiscovery.first_join_live_fresh
#print axioms REWB.MaskedRunDiscovery.first_coexistence
#print axioms REWB.MaskedRunDiscovery.first_live_generation
#print axioms REWB.MaskedRunDiscovery.completed_class_generated
#print axioms REWB.MaskedRunDiscovery.prepareSuffixes_complete
#print axioms REWB.MaskedRunDiscovery.locate_complete
#print axioms REWB.MaskedRunDiscovery.discover_locus
#print axioms REWB.MaskedRunDiscovery.prepareSuffixes_work
#print axioms REWB.MaskedRunDiscovery.Regression.partial_pair_not_consecutive
#print axioms REWB.MaskedRunDiscovery.Regression.partial_gap_not_least

-- Constructed boundary applications, actual masked periodic phases and reset geometry.
#print axioms REWB.BoundaryApplication.Range.query_correct
#print axioms REWB.BoundaryApplication.Range.query_work
#print axioms REWB.BoundaryApplication.edge_color
#print axioms REWB.BoundaryApplication.compile_active
#print axioms REWB.BoundaryApplication.compile_work
#print axioms REWB.BoundaryApplication.Versions.execute_root
#print axioms REWB.BoundaryApplication.Versions.execute_get
#print axioms REWB.BoundaryApplication.FixedEnd.trie_depth_zero
#print axioms REWB.BoundaryApplication.FixedEnd.build_mass
#print axioms REWB.BoundaryApplication.FixedEnd.build_active
#print axioms REWB.BoundaryApplication.FixedEnd.build_version_active
#print axioms REWB.BoundaryApplication.FixedEnd.build_work
#print axioms REWB.BoundaryApplication.Aggregate.queryPrefix_active
#print axioms REWB.BoundaryApplication.FixedEnd.queryPath_correct
#print axioms REWB.BoundaryApplication.FixedEnd.queryPath_work
#print axioms REWB.BoundaryApplication.Regression.root_query
#print axioms REWB.BoundaryApplication.Regression.empty_query
#print axioms REWB.BoundaryApplication.Regression.terminal_query
#print axioms REWB.BoundaryApplication.Regression.before_terminal
#print axioms REWB.MaskedPeriodic.OrbitData.descriptor_spec
#print axioms REWB.MaskedPeriodic.formula_correct
#print axioms REWB.MaskedPeriodic.projection_correct
#print axioms REWB.MaskedPeriodic.Modulus.projection_compatible
#print axioms REWB.MaskedPeriodic.Modulus.family_eq_familyTR
#print axioms REWB.MaskedPeriodic.modulus_pos
#print axioms REWB.MaskedPeriodic.projection_compatible
#print axioms REWB.MaskedPeriodic.projection_size
#print axioms REWB.MaskedPeriodic.projection_steps
#print axioms REWB.MaskedPeriodic.windows_size
#print axioms REWB.MaskedPeriodic.queryBranch_correct
#print axioms REWB.MaskedPeriodic.queryBranch_work
#print axioms REWB.MaskedPeriodic.zero_family
#print axioms REWB.MaskedPeriodic.interior_family
#print axioms REWB.MaskedPeriodic.ending_family
#print axioms REWB.MaskedPeriodic.interiorTuples_correct
#print axioms REWB.MaskedPeriodic.endingTuples_correct
#print axioms REWB.MaskedPeriodic.queryInterior_correct
#print axioms REWB.MaskedPeriodic.queryEnding_correct
#print axioms REWB.MaskedPeriodic.contexts_value
#print axioms REWB.MaskedPeriodic.contexts_bounds
#print axioms REWB.MaskedPeriodic.physical_zero
#print axioms REWB.MaskedPeriodic.physical_positive
#print axioms REWB.MaskedPeriodic.phaseQuery_correct
#print axioms REWB.MaskedPeriodic.Regression.projected_boundary_cases
#print axioms REWB.MaskedPeriodic.Regression.positive_cut_empty
#print axioms REWB.MaskedLocalAnchor.complete_least
#print axioms REWB.MaskedLocalAnchor.reset_penultimate
#print axioms REWB.MaskedLocalAnchor.reset_following
#print axioms REWB.MaskedLocalAnchor.reset
#print axioms REWB.MaskedLocalAnchor.reset_terminal
#print axioms REWB.MaskedLocalAnchor.shorten
#print axioms REWB.MaskedLocalAnchor.reset_square

-- Fast ordered occurrence sets and actual cubic-run coverage.
#print axioms REWB.MaskedRunCoverage.cubic_pair
#print axioms REWB.MaskedRunCoverage.primitive_adjacent
#print axioms REWB.MaskedRunCoverage.recover_run
#print axioms REWB.MaskedRunCoverage.exact_locus_depth
#print axioms REWB.MaskedRunCoverage.actual_suffix_coverage
#print axioms REWB.MaskedRunTrieBridge.compile_correct
#print axioms REWB.MaskedRunTrieBridge.compile_suffixes
#print axioms REWB.MaskedRunTrieBridge.suffix_positions_nodup
#print axioms REWB.MaskedRunTrieBridge.lca_split
#print axioms REWB.MaskedOrdered.Tree.pred_correct
#print axioms REWB.MaskedOrdered.Tree.succ_correct
#print axioms REWB.MaskedOrdered.insert_reference
#print axioms REWB.MaskedOrdered.insert_work
#print axioms REWB.MaskedOrdered.merge_imports
#print axioms REWB.MaskedOrdered.discarded_positions
#print axioms REWB.MaskedOrdered.merge_new_edge
#print axioms REWB.MaskedOrdered.execute_reference
#print axioms REWB.MaskedOrdered.execute_count
#print axioms REWB.MaskedOrdered.execute_imports
#print axioms REWB.MaskedOrdered.run_work_bound
#print axioms REWB.MaskedOrdered.run_events
#print axioms REWB.MaskedOrdered.run_balance

-- Materialized subset rows, full real-text queries and local jump semantics.
#print axioms REWB.BoundaryApplication.Lift.rename_view
#print axioms REWB.BoundaryApplication.Lift.rename_steps
#print axioms REWB.BoundaryApplication.Lift.importMany_valid_of_live
#print axioms REWB.BoundaryApplication.RTable.compute_correct
#print axioms REWB.BoundaryApplication.RTable.compute_bounds
#print axioms REWB.BoundaryApplication.RTable.node_correct
#print axioms REWB.BoundaryApplication.RTable.node_work
#print axioms REWB.BoundaryApplication.Subset.imported_selected
#print axioms REWB.BoundaryApplication.Subset.recolored_selected
#print axioms REWB.BoundaryApplication.Subset.node_import_selected
#print axioms REWB.MaskedPeriodic.Text.families_iff
#print axioms REWB.MaskedPeriodic.Text.actual_equal_copies
#print axioms REWB.MaskedPeriodic.Text.query_correct
#print axioms REWB.MaskedPeriodic.Text.query_run_correct
#print axioms REWB.MaskedPeriodic.Text.inRun_correct
#print axioms REWB.MaskedPeriodic.Text.witness_window
#print axioms REWB.MaskedPeriodic.Text.prepareTail_value
#print axioms REWB.MaskedPeriodic.Text.prepareTail_bounds
#print axioms REWB.MaskedPeriodic.Text.query_full_correct
#print axioms REWB.MaskedPeriodic.Text.query_full_run_correct
#print axioms REWB.MaskedClusterStage.dfa_size
#print axioms REWB.MaskedClusterStage.dfa_run
#print axioms REWB.MaskedClusterStage.dfa_decode_run
#print axioms REWB.MaskedClusterStage.jump_rank
#print axioms REWB.MaskedClusterStage.jumpVector_decode
#print axioms REWB.MaskedClusterStage.anchored_exact
#print axioms REWB.MaskedClusterStage.twoJumps_correct

-- Complete owner-event enumeration and its closed preparation/execution bound.
#print axioms REWB.MaskedOrdered.Owner.visit_at
#print axioms REWB.MaskedOrdered.Owner.visit_at_event
#print axioms REWB.MaskedOrdered.Owner.location_owner_mem
#print axioms REWB.MaskedOrdered.Owner.suffix_event_certified
#print axioms REWB.MaskedOrdered.Owner.probe_sound
#print axioms REWB.MaskedOrdered.Owner.enumerateAuto_mem
#print axioms REWB.MaskedOrdered.Owner.enumerateAuto_nodup
#print axioms REWB.MaskedOrdered.Owner.enumerateAuto_work
#print axioms REWB.MaskedRunOwnerCoverage.cubic_event
#print axioms REWB.MaskedRunOwnerCoverage.cubic_owner_record
#print axioms REWB.MaskedRunOwnerCoverage.cubic_probe
#print axioms REWB.MaskedRunOwnerCost.suffix_shape
#print axioms REWB.MaskedRunOwnerCost.suffix_execution
#print axioms REWB.MaskedRunEnumerationCost.enumerate_work

-- Constructed heavy versions, direct addresses and genuine source routes.
#print axioms REWB.BoundaryApplication.Heavy.imports_bound
#print axioms REWB.BoundaryApplication.Heavy.work_bound
#print axioms REWB.BoundaryApplication.Heavy.lightHeight_bound
#print axioms REWB.BoundaryApplication.Heavy.go_all
#print axioms REWB.BoundaryApplication.Heavy.Regression.aliased_eq_go
#print axioms REWB.BoundaryApplication.HeavyIndex.build_source
#print axioms REWB.BoundaryApplication.HeavyIndex.build_stored
#print axioms REWB.BoundaryApplication.HeavyIndex.build_rank
#print axioms REWB.BoundaryApplication.HeavyIndex.build_imports
#print axioms REWB.BoundaryApplication.HeavyIndex.build_work
#print axioms REWB.BoundaryApplication.HeavyIndex.probe_correct
#print axioms REWB.BoundaryApplication.HeavyIndex.query_bound
#print axioms REWB.BoundaryApplication.HeavyIndex.query_chain_iff
#print axioms REWB.BoundaryApplication.Address.build_source_route
#print axioms REWB.BoundaryApplication.HeavyIndex.query_route_iff

-- Real dense/singleton one-jump matrix cells from immutable masks.
#print axioms REWB.MaskedCluster.pairFormula_correct
#print axioms REWB.MaskedCluster.pairQuery_correct
#print axioms REWB.MaskedCluster.pairQuery_work
#print axioms REWB.MaskedCluster.contexts_value
#print axioms REWB.MaskedCluster.contexts_work
#print axioms REWB.MaskedCluster.replay_value
#print axioms REWB.MaskedCluster.cell_words
#print axioms REWB.MaskedCluster.cell_direct_first
#print axioms REWB.MaskedCluster.certificate_onPeriod
#print axioms REWB.MaskedCluster.cell_direct_certificate
#print axioms REWB.MaskedCluster.matrix_get
#print axioms REWB.MaskedCluster.matrix_state
#print axioms REWB.MaskedCluster.matrix_work
#print axioms REWB.MaskedCluster.pointCell_direct
#print axioms REWB.MaskedCluster.pointMatrix_get
#print axioms REWB.MaskedCluster.pointMatrix_work

-- The actual complete-run all-source periodic branch.
#print axioms REWB.MaskedPeriodic.Batch.scan_read
#print axioms REWB.MaskedPeriodic.Batch.scan_calls
#print axioms REWB.MaskedPeriodic.Batch.scan_query_work
#print axioms REWB.MaskedPeriodic.Batch.query_work
#print axioms REWB.MaskedPeriodic.Batch.runs_read
#print axioms REWB.MaskedPeriodic.Batch.solve_correct
#print axioms REWB.MaskedPeriodic.Batch.solve_sound
#print axioms REWB.MaskedPeriodic.Batch.enumerated_span
#print axioms REWB.MaskedPeriodic.Batch.solve_work
#print axioms REWB.MaskedPeriodic.Batch.Regression.full_batch_hit

-- Complete fixed-end source/target coverage of the actual heavy query.
#print axioms REWB.BoundaryApplication.Coverage.node_cut_iff
#print axioms REWB.BoundaryApplication.Coverage.lca_cut_bound
#print axioms REWB.BoundaryApplication.Coverage.normal_hit_iff
#print axioms REWB.BoundaryApplication.Coverage.import_hit_iff
#print axioms REWB.BoundaryApplication.Coverage.route_iff
#print axioms REWB.BoundaryApplication.Coverage.query_correct
#print axioms REWB.BoundaryApplication.Coverage.query_iff_cuts

-- Complete fixed-target-start queries and materialized compressed-edge ancestors.
#print axioms REWB.BoundaryApplication.StartCuts.query_correct
#print axioms REWB.BoundaryApplication.StartCuts.query_work
#print axioms REWB.BoundaryApplication.StartPartial.query_correct
#print axioms REWB.BoundaryApplication.StartSummary.build_root
#print axioms REWB.BoundaryApplication.StartSummary.build_work
#print axioms REWB.BoundaryApplication.StartStep.query_correct
#print axioms REWB.BoundaryApplication.StartStep.image_get
#print axioms REWB.BoundaryApplication.StartLocal.query_correct
#print axioms REWB.BoundaryApplication.StartPass.go_work
#print axioms REWB.BoundaryApplication.StartCoverage.query_hits
#print axioms REWB.BoundaryApplication.StartSound.go_sound
#print axioms REWB.BoundaryApplication.StartLocate.build_good
#print axioms REWB.BoundaryApplication.StartLocate.build_path
#print axioms REWB.BoundaryApplication.StartLocate.build_work
#print axioms REWB.BoundaryApplication.StartLocate.ascend_complete
#print axioms REWB.BoundaryApplication.StartLocate.cut_unique
#print axioms REWB.BoundaryApplication.StartLocate.query_located
#print axioms REWB.BoundaryApplication.StartLocate.query_correct
#print axioms REWB.BoundaryApplication.StartLocate.query_work
#print axioms REWB.BoundaryApplication.StartLocate.query_zero
#print axioms REWB.BoundaryApplication.StartLocate.bounded_build_work
#print axioms REWB.BoundaryApplication.StartIndex.query_correct
#print axioms REWB.BoundaryApplication.StartIndex.query_iff_cuts
#print axioms REWB.BoundaryApplication.StartIndex.query_work
#print axioms REWB.BoundaryApplication.StartIndex.build_work
#print axioms REWB.BoundaryApplication.StartIndex.build_addresses_exact
#print axioms REWB.BoundaryApplication.StartRegression.empty_query
#print axioms REWB.BoundaryApplication.StartRegression.strict_partial_query
#print axioms REWB.BoundaryApplication.StartRegression.epsilon_not_both
#print axioms REWB.BoundaryApplication.StartRegression.noninjective_E_image

-- Source-only windows and complete two-mode cursor blocks.
#print axioms REWB.MaskedCluster.sourcePairQuery_correct
#print axioms REWB.MaskedCluster.sourcePairQuery_work
#print axioms REWB.MaskedCluster.filteredCell_target
#print axioms REWB.MaskedCluster.filteredCell_direct_first
#print axioms REWB.MaskedCluster.passCell_correct
#print axioms REWB.MaskedCluster.filteredPointCell_direct
#print axioms REWB.MaskedCluster.normal_current
#print axioms REWB.MaskedCluster.overshoot_current
#print axioms REWB.MaskedCluster.rowCell_correct
#print axioms REWB.MaskedCluster.rowMatrix_correct
#print axioms REWB.MaskedCluster.pointRowCell_correct
#print axioms REWB.MaskedCluster.flatten_get
#print axioms REWB.MaskedCluster.composeBlocks_correct
#print axioms REWB.MaskedCluster.compileDense_correct
#print axioms REWB.MaskedCluster.compilePoint_correct
#print axioms REWB.MaskedCluster.composeBlocks_denotes
#print axioms REWB.MaskedCluster.prepareRows_work
#print axioms REWB.MaskedCluster.compileDense_work
#print axioms REWB.MaskedCluster.compilePoint_work
#print axioms REWB.MaskedCluster.composeBlocks_work
#print axioms REWB.MaskedCluster.CursorRegression.target_outside_source_window
#print axioms REWB.MaskedCluster.CursorRegression.disabled_source_has_no_source_jump
#print axioms REWB.MaskedCluster.CursorRegression.incoming_no_jump_survives
#print axioms REWB.MaskedCluster.CursorRegression.incoming_passed_singleton

-- Actual threshold queues, ordered one-shot draining and stale adjacency validation.
#print axioms REWB.MaskedThresholdQueue.insert_spec
#print axioms REWB.MaskedThresholdQueue.takeMax_spec
#print axioms REWB.MaskedThresholdQueue.takeMax_none
#print axioms REWB.MaskedThresholdQueue.drain_spec
#print axioms REWB.MaskedThresholdQueue.drain_due_iff
#print axioms REWB.MaskedThresholdQueue.drain_pending_iff
#print axioms REWB.MaskedThresholdQueue.drain_work
#print axioms REWB.MaskedThresholdQueue.drain_order
#print axioms REWB.MaskedThresholdQueue.drain_twice_bound
#print axioms REWB.MaskedThresholdQueue.drain_no_replay
#print axioms REWB.MaskedThresholdEvents.pushEdges_spec
#print axioms REWB.MaskedThresholdEvents.add_spec
#print axioms REWB.MaskedThresholdEvents.check_correct
#print axioms REWB.MaskedThresholdEvents.check_work
#print axioms REWB.MaskedThresholdEvents.shorten_correct
#print axioms REWB.MaskedThresholdEvents.shorten_work
#print axioms REWB.MaskedThresholdEvents.Regression.actual_generations
#print axioms REWB.MaskedThresholdEvents.Regression.obsolete_pair_filtered
#print axioms REWB.MaskedThresholdEvents.Regression.descending_thresholds
#print axioms REWB.MaskedThresholdEvents.Regression.future_thresholds_once
#print axioms REWB.MaskedThresholdEvents.Regression.original_queue_preserved

-- Canonical density charges at actual first-threshold suffix-trie owners.
#print axioms REWB.MaskedDensityCharge.locus_id_unique
#print axioms REWB.MaskedDensityCharge.locus_parent
#print axioms REWB.MaskedDensityCharge.at_injective
#print axioms REWB.MaskedDensityCharge.keys_nodup
#print axioms REWB.MaskedDensityCharge.certify_completed_reset
#print axioms REWB.MaskedDensityCharge.certify_threshold
#print axioms REWB.MaskedDensityCharge.canonical_exists
#print axioms REWB.MaskedDensityCharge.actual_record
#print axioms REWB.MaskedDensityCharge.certified_budget
#print axioms REWB.MaskedDensityCharge.Regression.parent_has_charge
#print axioms REWB.MaskedDensityCharge.Regression.refinement_cannot_charge
#print axioms REWB.MaskedDensityCharge.Regression.actual_unique_charge
#print axioms REWB.MaskedDensityCharge.Regression.empty_records

-- Actual replay banks and common-prefix shortening of compiled cursor blocks.
#print axioms REWB.MaskedCluster.ReplayMaps.count_eq
#print axioms REWB.MaskedCluster.ReplayMaps.decode_encode
#print axioms REWB.MaskedCluster.ReplayMaps.rightAction_comp
#print axioms REWB.MaskedCluster.ReplayMaps.common_shortening
#print axioms REWB.MaskedCluster.ReplayMaps.replay_common_shortening
#print axioms REWB.MaskedCluster.bankAction_gate
#print axioms REWB.MaskedCluster.bankAction_comp
#print axioms REWB.MaskedCluster.bankComponent_reindex
#print axioms REWB.MaskedCluster.tabulate_reindex
#print axioms REWB.MaskedCluster.compileDenseBank_current
#print axioms REWB.MaskedCluster.compilePointBank_current
#print axioms REWB.MaskedCluster.compileDenseBank_reindex
#print axioms REWB.MaskedCluster.compilePointBank_reindex
#print axioms REWB.MaskedCluster.compileDenseBank_select_shorter
#print axioms REWB.MaskedCluster.compilePointBank_select_shorter
#print axioms REWB.MaskedCluster.compileDenseBank_work
#print axioms REWB.MaskedCluster.compilePointBank_work
#print axioms REWB.MaskedCluster.BankRegression.universe_size
#print axioms REWB.MaskedCluster.BankRegression.maps_noncommute
#print axioms REWB.MaskedCluster.BankRegression.source_gate_retained
#print axioms REWB.MaskedCluster.BankRegression.constant_word_roundtrip

-- Mutable sources, complete empty-capture initialization and separated boundaries.
#print axioms REWB.MaskedCluster.Cut.query_correct
#print axioms REWB.MaskedCluster.Cut.query_bounds
#print axioms REWB.MaskedCluster.Cut.queryBank_correct
#print axioms REWB.MaskedCluster.Cut.queryBank_entries
#print axioms REWB.MaskedCluster.Cut.queryBank_bounds
#print axioms REWB.MaskedCluster.Cut.query_denseBank_correct
#print axioms REWB.MaskedCluster.Cut.query_pointBank_correct
#print axioms REWB.MaskedCluster.CutRegression.separate_witnesses
#print axioms REWB.MaskedCluster.CutRegression.rejects_mixed_cuts
#print axioms REWB.MaskedMutableProgression.encode_injective
#print axioms REWB.MaskedMutableProgression.encode_bound
#print axioms REWB.MaskedMutableProgression.encode_capacity
#print axioms REWB.MaskedMutableProgression.grid_interval
#print axioms REWB.MaskedMutableProgression.build_valid
#print axioms REWB.MaskedMutableProgression.build_live
#print axioms REWB.MaskedMutableProgression.build_work
#print axioms REWB.MaskedMutableProgression.erase_valid
#print axioms REWB.MaskedMutableProgression.erase_live
#print axioms REWB.MaskedMutableProgression.erase_represents
#print axioms REWB.MaskedMutableProgression.member_correct
#print axioms REWB.MaskedMutableProgression.grid_correct
#print axioms REWB.MaskedMutableProgression.grid_some
#print axioms REWB.MaskedMutableProgression.ap_correct
#print axioms REWB.MaskedMutableProgression.ap_some
#print axioms REWB.MaskedMutableProgression.ap_represents
#print axioms REWB.MaskedMutableProgression.ap_build_correct
#print axioms REWB.MaskedMutableProgression.build_log_work
#print axioms REWB.MaskedMutableProgression.erase_log_work
#print axioms REWB.MaskedMutableProgression.ap_log_work
#print axioms REWB.MaskedMutableProgression.erase_global_work
#print axioms REWB.MaskedMutableProgression.ap_global_work
#print axioms REWB.MaskedMutableProgression.Regression.physical_delete
#print axioms REWB.MaskedMutableProgression.Regression.persistent_previous
#print axioms REWB.MaskedMutableProgression.Regression.repeated_and_outside
#print axioms REWB.MaskedMutableProgression.Regression.short_mask_huge_step
#print axioms REWB.MaskedMutableProgression.Regression.empty_and_zero_request
#print axioms REWB.MaskedMutableProgression.Regression.clipped_ap_delete
#print axioms REWB.MaskedSourceFanout.build_mem
#print axioms REWB.MaskedSourceFanout.build_count
#print axioms REWB.MaskedSourceFanout.build_nodup
#print axioms REWB.MaskedSourceFanout.build_good
#print axioms REWB.MaskedSourceFanout.build_work
#print axioms REWB.MaskedSourceFanout.take_balance
#print axioms REWB.MaskedSourceFanout.take_again
#print axioms REWB.MaskedSourceFanout.drain_visits
#print axioms REWB.MaskedSourceFanout.drain_deliverySize
#print axioms REWB.MaskedSourceFanout.drain_size_bound
#print axioms REWB.MaskedSourceFanout.drain_has
#print axioms REWB.MaskedSourceFanout.prepare_mem
#print axioms REWB.MaskedSourceFanout.prepare_good
#print axioms REWB.MaskedSourceFanout.prepare_nodup
#print axioms REWB.MaskedSourceFanout.prepare_memberships
#print axioms REWB.MaskedSourceFanout.prepare_work
#print axioms REWB.MaskedSourceFanout.prepare_delivery_bound
#print axioms REWB.MaskedSourceFanout.prepare_delivery_exact
#print axioms REWB.MaskedSourceFanout.Regression.overlapping_memberships
#print axioms REWB.MaskedSourceFanout.Regression.duplicate_removal
#print axioms REWB.MaskedSourceFanout.Regression.mixed_requests
#print axioms REWB.MaskedSourceFanout.Regression.empty_preparation
#print axioms REWB.MaskedClusterLeaders.check_correct
#print axioms REWB.MaskedClusterLeaders.insert_away
#print axioms REWB.MaskedClusterLeaders.refresh_mem
#print axioms REWB.MaskedClusterLeaders.add_invariant
#print axioms REWB.MaskedClusterLeaders.add_work
#print axioms REWB.MaskedClusterLeaders.add_future
#print axioms REWB.MaskedClusterLeaders.changed_leader_record
#print axioms REWB.MaskedClusterLeaders.repairLive_mem
#print axioms REWB.MaskedClusterLeaders.shorten_invariant
#print axioms REWB.MaskedClusterLeaders.shorten_future
#print axioms REWB.MaskedClusterLeaders.shorten_work
#print axioms REWB.MaskedClusterLeaders.execute_valid
#print axioms REWB.MaskedClusterLeaders.execute_leaders
#print axioms REWB.MaskedClusterLeaders.execute_work
#print axioms REWB.MaskedClusterLeaders.Regression.dense_then_split
#print axioms REWB.MaskedClusterLeaders.Regression.stale_pair_does_not_restore_leader
#print axioms REWB.MaskedClusterLeaders.Regression.overlap_records_once
#print axioms REWB.MaskedClusterLeaders.Regression.invalid_operations_ignored
#print axioms REWB.MaskedClusterLeaders.Regression.born_due_records
#print axioms REWB.MaskedCluster.Mutable.sourcePairQuery_correct
#print axioms REWB.MaskedCluster.Mutable.sourcePairQuery_work
#print axioms REWB.MaskedCluster.Mutable.sourcePairQuery_log_work
#print axioms REWB.MaskedCluster.Mutable.cell_direct_first
#print axioms REWB.MaskedCluster.Mutable.pointCell_target_erase
#print axioms REWB.MaskedCluster.Mutable.compileDenseBank_current
#print axioms REWB.MaskedCluster.Mutable.compilePointBank_current
#print axioms REWB.MaskedCluster.Mutable.compileDenseBank_reindex
#print axioms REWB.MaskedCluster.Mutable.compilePointBank_reindex
#print axioms REWB.MaskedCluster.Mutable.query_denseBank_correct
#print axioms REWB.MaskedCluster.Mutable.query_pointBank_correct
#print axioms REWB.MaskedCluster.Mutable.compileDenseBank_work
#print axioms REWB.MaskedCluster.Mutable.compilePointBank_work
#print axioms REWB.MaskedCluster.Mutable.Regression.rebuilt_source_deleted_target_retained
#print axioms REWB.MaskedCluster.Mutable.Regression.old_snapshot_remains
#print axioms REWB.MaskedCluster.Mutable.Regression.terminal_source_member
#print axioms REWB.MaskedCluster.Mutable.Batch.compileRun_lookup
#print axioms REWB.MaskedCluster.Mutable.Batch.compileRun_missing
#print axioms REWB.MaskedCluster.Mutable.Batch.member_current
#print axioms REWB.MaskedCluster.Mutable.Batch.cursor_current
#print axioms REWB.MaskedCluster.Mutable.Batch.run_singleton_member
#print axioms REWB.MaskedCluster.Mutable.Batch.compileRun_current
#print axioms REWB.MaskedCluster.Mutable.Batch.compileSingleton_current
#print axioms REWB.MaskedCluster.Mutable.Batch.compileRun_work
#print axioms REWB.MaskedCluster.Mutable.Batch.compileSingleton_work
#print axioms REWB.MaskedMutableProgression.Batch.prepare_valid
#print axioms REWB.MaskedMutableProgression.Batch.prepare_run_exists
#print axioms REWB.MaskedMutableProgression.Batch.prepare_singleton_member
#print axioms REWB.MaskedMutableProgression.Batch.eraseSource_valid
#print axioms REWB.MaskedMutableProgression.Batch.eraseMany_valid
#print axioms REWB.MaskedMutableProgression.Batch.run_valid
#print axioms REWB.MaskedMutableProgression.Batch.run_member
#print axioms REWB.MaskedMutableProgression.Batch.run_delivered
#print axioms REWB.MaskedMutableProgression.Batch.run_log_work
#print axioms REWB.MaskedMutableProgression.Batch.prepare_source_work
#print axioms REWB.MaskedMutableProgression.Batch.run_total_work
#print axioms REWB.MaskedMutableProgression.Batch.queryRun_correct
#print axioms REWB.MaskedMutableProgression.Batch.queryRun_some
#print axioms REWB.MaskedMutableProgression.Batch.queryRun_work
#print axioms REWB.MaskedMutableProgression.Batch.run_query_correct
#print axioms REWB.MaskedMutableProgression.Batch.Regression.empty_boundary
#print axioms REWB.MaskedMutableProgression.Batch.Regression.actual_cube_survives
#print axioms REWB.MaskedMutableProgression.Batch.Regression.actual_cube_exhausted
#print axioms REWB.MaskedMutableProgression.Batch.Regression.repeated_delivery_bound
#print axioms REWB.MaskedEmpty.compute_eq_computeTR
#print axioms REWB.MaskedEmpty.compute_head
#print axioms REWB.MaskedEmpty.compute_length
#print axioms REWB.MaskedEmpty.compute_get
#print axioms REWB.MaskedEmpty.solve_size
#print axioms REWB.MaskedEmpty.solve_correct
#print axioms REWB.MaskedEmpty.witness_sound
#print axioms REWB.MaskedEmpty.solve_sound
#print axioms REWB.MaskedEmpty.maskedStart_partition
#print axioms REWB.MaskedEmpty.solve_partition
#print axioms REWB.MaskedEmpty.compute_work
#print axioms REWB.MaskedEmpty.solve_work
#print axioms REWB.MaskedEmpty.Regression.empty_terminal
#print axioms REWB.MaskedEmpty.Regression.source_gate
#print axioms REWB.MaskedEmpty.Regression.target_terminal
#print axioms REWB.MaskedEmpty.Regression.positive_B_rejects_empty
#print axioms REWB.MaskedEmpty.Regression.noninjective_transition
#print axioms REWB.MaskedEmpty.Regression.missing_target_is_false
#print axioms REWB.MaskedEmpty.Regression.final_boundary_kept
#print axioms REWB.MaskedEmpty.SourceBatch.positions_mem
#print axioms REWB.MaskedEmpty.SourceBatch.positions_length
#print axioms REWB.MaskedEmpty.SourceBatch.positions_nodup
#print axioms REWB.MaskedEmpty.SourceBatch.start_reported
#print axioms REWB.MaskedEmpty.SourceBatch.start_count
#print axioms REWB.MaskedEmpty.SourceBatch.start_nodup
#print axioms REWB.MaskedEmpty.SourceBatch.start_valid
#print axioms REWB.MaskedEmpty.SourceBatch.start_current
#print axioms REWB.MaskedEmpty.SourceBatch.start_member
#print axioms REWB.MaskedEmpty.SourceBatch.start_partition
#print axioms REWB.MaskedEmpty.SourceBatch.start_work
#print axioms REWB.MaskedEmpty.SourceBatch.Regression.reports_once
#print axioms REWB.MaskedEmpty.SourceBatch.Regression.remaining_terminal
#print axioms REWB.MaskedEmpty.SourceBatch.Regression.positive_B_preserves_sources
#print axioms REWB.MaskedEmpty.SourceBatch.Regression.empty_text_is_reported
#print axioms REWB.MaskedClusterDescriptor.component_gap
#print axioms REWB.MaskedClusterDescriptor.interval_progression
#print axioms REWB.MaskedClusterDescriptor.component_progression
#print axioms REWB.BoundaryApplication.Separated.Summary.build_root
#print axioms REWB.BoundaryApplication.Separated.Summary.build_work
#print axioms REWB.BoundaryApplication.Separated.Cuts.local_correct
#print axioms REWB.BoundaryApplication.Separated.Cuts.advance_correct
#print axioms REWB.BoundaryApplication.Separated.Cuts.advance_work
#print axioms REWB.BoundaryApplication.Separated.Coverage.advance_hits
#print axioms REWB.BoundaryApplication.Separated.Pass.go_correct
#print axioms REWB.BoundaryApplication.Separated.Pass.go_work
#print axioms REWB.BoundaryApplication.Separated.buildBits_correct
#print axioms REWB.BoundaryApplication.Separated.buildBits_iff_cuts
#print axioms REWB.BoundaryApplication.Separated.buildBits_work
#print axioms REWB.BoundaryApplication.Separated.Suffix.build_active
#print axioms REWB.BoundaryApplication.Separated.Suffix.build_trans
#print axioms REWB.BoundaryApplication.Separated.Suffix.query_correct
#print axioms REWB.BoundaryApplication.Separated.Suffix.build_work
#print axioms REWB.BoundaryApplication.Separated.query_correct
#print axioms REWB.BoundaryApplication.Separated.query_iff_cuts
#print axioms REWB.BoundaryApplication.Separated.query_build_work
#print axioms REWB.BoundaryApplication.Separated.build_work
#print axioms REWB.BoundaryApplication.Separated.Regression.empty_query
#print axioms REWB.BoundaryApplication.Separated.Regression.distinct_boundaries
#print axioms REWB.BoundaryApplication.Separated.Regression.source_boundary_respected
#print axioms REWB.BoundaryApplication.Separated.Regression.noninjective_source_colors
#print axioms REWB.BoundaryApplication.Separated.Regression.endpoint_after_letter

-- Actual cluster descriptors and constant-query periodic border selection.
#print axioms REWB.MaskedClusterDescriptor.locate_work
#print axioms REWB.MaskedClusterDescriptor.describeLeader_work
#print axioms REWB.MaskedClusterDescriptor.describe_work
#print axioms REWB.MaskedClusterDescriptor.locate_correct
#print axioms REWB.MaskedClusterDescriptor.locate_unique
#print axioms REWB.MaskedClusterDescriptor.describeLeader_sound
#print axioms REWB.MaskedClusterDescriptor.locate_descriptor
#print axioms REWB.MaskedClusterDescriptor.locate_none_outside
#print axioms REWB.MaskedClusterDescriptor.locate_none_iff
#print axioms REWB.MaskedClusterDescriptor.describe_sound
#print axioms REWB.MaskedClusterDescriptor.describe_none_iff
#print axioms REWB.MaskedClusterDescriptor.Sound.anchor
#print axioms REWB.MaskedClusterDescriptor.Sound.next_bounds
#print axioms REWB.MaskedClusterDescriptor.Sound.progression
#print axioms REWB.MaskedClusterDescriptor.Sound.ap_mem
#print axioms REWB.MaskedClusterDescriptor.Sound.dense_previous
#print axioms REWB.MaskedClusterDescriptor.describeLeader_geometry
#print axioms REWB.MaskedClusterDescriptor.describe_geometry
#print axioms REWB.MaskedClusterDescriptor.Regression.dense_components
#print axioms REWB.MaskedClusterDescriptor.Regression.locator_endpoints_and_absent
#print axioms REWB.MaskedClusterDescriptor.Regression.density_split
#print axioms REWB.MaskedClusterDescriptor.Regression.singleton_and_empty
#print axioms REWB.MaskedClusterDescriptor.Regression.partial_component_is_not_assumed_ap
#print axioms REWB.MaskedClusterDescriptor.Regression.complete_periodic_geometry
#print axioms REWB.MaskedClusterDescriptor.Regression.terminal_anchor_strict
#print axioms REWB.BoundaryBorder.periodPrefix_of_lce
#print axioms REWB.BoundaryBorder.extend_correct
#print axioms REWB.BoundaryBorder.extend_work
#print axioms REWB.BoundaryBorder.prefix_failure
#print axioms REWB.BoundaryBorder.prefix_from_interval
#print axioms REWB.BoundaryBorder.prefix_move
#print axioms REWB.BoundaryBorder.copy_past_break
#print axioms REWB.BoundaryBorder.outside_unique_candidate
#print axioms REWB.BoundaryBorder.inside_iff
#print axioms REWB.BoundaryBorder.prefix_unique
#print axioms REWB.BoundaryBorder.lce_agree_iff
#print axioms REWB.BoundaryBorder.band_iff
#print axioms REWB.BoundaryBorder.choose_correct
#print axioms REWB.BoundaryBorder.choose_work
#print axioms REWB.BoundaryBorder.select_correct
#print axioms REWB.BoundaryBorder.select_work
#print axioms REWB.BoundaryBorder.progression_seed
#print axioms REWB.BoundaryBorder.select_from_seed
#print axioms REWB.BoundaryBorder.Regression.source_indexed
#print axioms REWB.BoundaryBorder.Regression.target_indexed
#print axioms REWB.BoundaryBorder.Regression.unique_past_break
#print axioms REWB.BoundaryBorder.Regression.actual_exceptional_selection
#print axioms REWB.BoundaryBorder.Regression.actual_clipped_progression
#print axioms REWB.BoundaryBorder.Regression.clipped_members

#print axioms REWB.MaskedSuffixClass.annotate_work
#print axioms REWB.MaskedSuffixClass.cut_locus
#print axioms REWB.MaskedSuffixClass.fromSuffixes_locus
#print axioms REWB.MaskedSuffixClass.query_locus
#print axioms REWB.MaskedSuffixClass.query_complete
#print axioms REWB.MaskedSuffixClass.query_sound
#print axioms REWB.MaskedSuffixClass.query_exists_iff
#print axioms REWB.MaskedSuffixClass.prepare_forward
#print axioms REWB.MaskedSuffixClass.prepare_work
#print axioms REWB.MaskedSuffixClass.prepare_addresses_exact
#print axioms REWB.MaskedSuffixClass.prepare_work_closed
#print axioms REWB.MaskedSuffixClass.query_work_height
#print axioms REWB.MaskedSuffixClass.Regression.partial_class
#print axioms REWB.MaskedSuffixClass.Regression.equal_depth_lift
#print axioms REWB.MaskedSuffixClass.Regression.retained_complete_ancestor
#print axioms REWB.MaskedCluster.Mutable.compileDenseBank_same
#print axioms REWB.MaskedCluster.Mutable.compilePointBank_same
#print axioms REWB.MaskedCluster.Mutable.Batch.compileRun_erase
#print axioms REWB.MaskedCluster.Mutable.Store.compile_presence_erase
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_other
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_coherent
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_complete
#print axioms REWB.MaskedCluster.Mutable.Store.install_coherent
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_counts
#print axioms REWB.MaskedCluster.Mutable.Store.compile_work
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_combined_work
#print axioms REWB.MaskedCluster.Mutable.Store.describe_reset_geometry
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_geometry
#print axioms REWB.MaskedCluster.Mutable.Store.Regression.inside_dense_hulls
#print axioms REWB.MaskedCluster.Mutable.Store.Regression.nonoccurrence_no_bank_repair
#print axioms REWB.MaskedCluster.Mutable.Store.Regression.other_cluster_shared

#print axioms REWB.BoundaryBorder.Window.component_work
#print axioms REWB.BoundaryBorder.Window.extract_work
#print axioms REWB.BoundaryBorder.Window.prefix_grid
#print axioms REWB.BoundaryBorder.Window.dense_exit
#print axioms REWB.BoundaryBorder.Window.component_correct
#print axioms REWB.BoundaryBorder.Window.extract_valid
#print axioms REWB.BoundaryBorder.Window.extract_correct
#print axioms REWB.BoundaryBorder.Window.query_work
#print axioms REWB.BoundaryBorder.Window.query_correct
#print axioms REWB.BoundaryBorder.WindowIndex.query_work
#print axioms REWB.BoundaryBorder.WindowIndex.query_correct
#print axioms REWB.BoundaryBorder.WindowIndex.query_invalid_class
#print axioms REWB.BoundaryBorder.WindowIndex.prepare_work_closed
#print axioms REWB.BoundaryBorder.Dyadic.window_iff
#print axioms REWB.BoundaryBorder.Dyadic.scale_correct
#print axioms REWB.BoundaryBorder.Dyadic.collect_correct
#print axioms REWB.BoundaryBorder.Dyadic.query_length
#print axioms REWB.BoundaryBorder.Dyadic.query_work_closed
#print axioms REWB.BoundaryBorder.Dyadic.query_correct
#print axioms REWB.BoundaryBorder.Dyadic.query_iff_slices
#print axioms REWB.BoundaryBorder.Window.Regression.empty_positive
#print axioms REWB.BoundaryBorder.Window.Regression.two_component_sources
#print axioms REWB.BoundaryBorder.Window.Regression.dense_holes
#print axioms REWB.BoundaryBorder.Window.Regression.target_at_end

#print axioms REWB.BoundaryRange.copy_target_bound
#print axioms REWB.BoundaryRange.at_bounds
#print axioms REWB.BoundaryRange.boundary_iff
#print axioms REWB.BoundaryRange.regionOf_correct
#print axioms REWB.BoundaryRange.region_unique
#print axioms REWB.BoundaryRange.partition
#print axioms REWB.BoundaryRange.six_cases
#print axioms REWB.BoundaryRange.near_bounds
#print axioms REWB.BoundaryRange.Automata.change_run
#print axioms REWB.BoundaryRange.Automata.change_accepts
#print axioms REWB.BoundaryRange.Automata.start_accepts
#print axioms REWB.BoundaryRange.Automata.finish_accepts
#print axioms REWB.BoundaryRange.Automata.stop_accepts
#print axioms REWB.BoundaryRange.Automata.tail_accepts
#print axioms REWB.BoundaryRange.Automata.tail_slice
#print axioms REWB.BoundaryRange.Automata.start_slice
#print axioms REWB.BoundaryRange.Automata.intersection_run
#print axioms REWB.BoundaryRange.Automata.meet_accepts
#print axioms REWB.BoundaryRange.Automata.join_accepts
#print axioms REWB.BoundaryRange.Automata.slice_take
#print axioms REWB.BoundaryRange.Automata.slice_drop
#print axioms REWB.BoundaryRange.Automata.join_slice
#print axioms REWB.BoundaryRange.Automata.gap_slice
#print axioms REWB.BoundaryRange.Automata.reverse_run
#print axioms REWB.BoundaryRange.Automata.reverse_accepts
#print axioms REWB.BoundaryRange.separated_copy
#print axioms REWB.BoundaryRange.fixedEnd_copy
#print axioms REWB.BoundaryRange.fixedStart_copy
#print axioms REWB.BoundaryRange.nearSeparated_step
#print axioms REWB.BoundaryRange.nearEnd_step
#print axioms REWB.BoundaryRange.nearStart_step
#print axioms REWB.BoundaryRange.split_gap
#print axioms REWB.BoundaryRange.nearBorder_step
#print axioms REWB.BoundaryRange.farLeft_step
#print axioms REWB.BoundaryRange.reverse_slice
#print axioms REWB.BoundaryRange.masked_reverse
#print axioms REWB.BoundaryRange.beforeEnd_copy
#print axioms REWB.BoundaryRange.farMask_true
#print axioms REWB.BoundaryRange.through_state
#print axioms REWB.BoundaryRange.farRight_step
#print axioms REWB.BoundaryRange.FarMask.point_correct
#print axioms REWB.BoundaryRange.FarMask.point_work
#print axioms REWB.BoundaryRange.FarMask.build_get
#print axioms REWB.BoundaryRange.FarMask.build_correct
#print axioms REWB.BoundaryRange.FarMask.build_bits
#print axioms REWB.BoundaryRange.FarMask.build_work
#print axioms REWB.BoundaryRange.Regression.all_six_regions
#print axioms REWB.BoundaryRange.Regression.boundary_equalities
#print axioms REWB.BoundaryRange.Regression.noninjective_reversal
#print axioms REWB.BoundaryRange.Regression.separate_regular_splits_rejected
#print axioms REWB.BoundaryRange.Regression.real_reversed_mask
#print axioms REWB.BoundaryRange.Regression.no_tail_beyond_text
#print axioms REWB.BoundaryRange.Regression.original_terminal_not_selected

#print axioms REWB.MaskedTraversalEdge.next_spec
#print axioms REWB.MaskedTraversalEdge.invariant_between
#print axioms REWB.MaskedTraversalEdge.threshold_between
#print axioms REWB.MaskedTraversalEdge.Chain.coverage
#print axioms REWB.MaskedTraversalEdge.Chain.unique
#print axioms REWB.MaskedTraversalEdge.Band.Valid.at
#print axioms REWB.MaskedTraversalEdge.run_valid
#print axioms REWB.MaskedTraversalEdge.run_occurrences
#print axioms REWB.MaskedTraversalEdge.run_measured
#print axioms REWB.MaskedTraversalEdge.run_work_queue
#print axioms REWB.MaskedTraversalEdge.Regression.parent_event_order
#print axioms REWB.MaskedTraversalEdge.Regression.long_singleton
#print axioms REWB.BoundaryBorder.Regular.Counted.compress_value
#print axioms REWB.BoundaryBorder.Regular.Counted.compress_work
#print axioms REWB.BoundaryBorder.Regular.Counted.pair_value
#print axioms REWB.BoundaryBorder.Regular.Counted.pair_work
#print axioms REWB.BoundaryBorder.Regular.Counted.solve_correct
#print axioms REWB.BoundaryBorder.Regular.Counted.solve_work
#print axioms REWB.BoundaryBorder.Regular.product_orbit
#print axioms REWB.BoundaryBorder.Regular.maps_value
#print axioms REWB.BoundaryBorder.Regular.maps_work
#print axioms REWB.BoundaryBorder.Regular.materialize_value
#print axioms REWB.BoundaryBorder.Regular.materialize_work
#print axioms REWB.BoundaryBorder.Regular.prefix_slice
#print axioms REWB.BoundaryBorder.Regular.capture
#print axioms REWB.BoundaryBorder.Regular.suffix
#print axioms REWB.BoundaryBorder.Regular.dense_correct
#print axioms REWB.BoundaryBorder.Regular.dense_work
#print axioms REWB.BoundaryBorder.Regular.query_correct
#print axioms REWB.BoundaryBorder.Regular.query_work
#print axioms REWB.BoundaryBorder.Regular.select_supported
#print axioms REWB.BoundaryBorder.Regular.select_progression_periods
#print axioms REWB.BoundaryBorder.Regular.align_correct
#print axioms REWB.BoundaryBorder.Regular.choice_correct
#print axioms REWB.BoundaryBorder.Regular.choice_work
#print axioms REWB.BoundaryBorder.Regular.dyadic_supported
#print axioms REWB.BoundaryBorder.Regular.rows_correct
#print axioms REWB.BoundaryBorder.Regular.rows_work
#print axioms REWB.BoundaryBorder.Regular.dyadic_correct
#print axioms REWB.BoundaryBorder.Regular.dyadic_work_closed
#print axioms REWB.BoundaryBorder.Regular.Regression.clipped_alignment
#print axioms REWB.BoundaryBorder.Regular.Regression.product_noninjective
#print axioms REWB.BoundaryBorder.Regular.Regression.zero_count_point
#print axioms REWB.BoundaryBorder.Regular.Regression.strict_partial_accept
#print axioms REWB.BoundaryBorder.Regular.Regression.right_clipped_reject
#print axioms REWB.BoundaryBorder.Regular.Regression.empty_positive

#print axioms REWB.BoundaryRange.Table.get_build
#print axioms REWB.BoundaryRange.Table.build_work
#print axioms REWB.BoundaryRange.Table.build_work_le
#print axioms REWB.BoundaryRange.Table.build_work_mono
#print axioms REWB.BoundaryRange.TableColor.choose_correct
#print axioms REWB.BoundaryRange.TableColor.choose_work
#print axioms REWB.BoundaryRange.NearIndex.build_separated
#print axioms REWB.BoundaryRange.NearIndex.build_end
#print axioms REWB.BoundaryRange.NearIndex.build_start
#print axioms REWB.BoundaryRange.NearIndex.cKey_variant
#print axioms REWB.BoundaryRange.NearIndex.separated_correct
#print axioms REWB.BoundaryRange.NearIndex.fixedEnd_correct
#print axioms REWB.BoundaryRange.NearIndex.fixedStart_correct
#print axioms REWB.BoundaryRange.NearIndex.separated_work
#print axioms REWB.BoundaryRange.NearIndex.fixedEnd_work
#print axioms REWB.BoundaryRange.NearIndex.fixedStart_work
#print axioms REWB.BoundaryRange.NearIndex.build_work
#print axioms REWB.BoundaryRange.NearIndex.scan_correct
#print axioms REWB.BoundaryRange.NearIndex.scan_work
#print axioms REWB.BoundaryRange.NearIndex.querySeparated_correct
#print axioms REWB.BoundaryRange.NearIndex.queryEnd_correct
#print axioms REWB.BoundaryRange.NearIndex.queryStart_correct
#print axioms REWB.BoundaryRange.NearIndex.queryThree_correct
#print axioms REWB.BoundaryRange.NearIndex.queryThree_work
#print axioms REWB.BoundaryRange.NearIndex.Regression.dependent_payload
#print axioms REWB.BoundaryRange.NearIndex.Regression.factory_counts_once
#print axioms REWB.BoundaryRange.NearIndex.Regression.coalesced_final_subset
#print axioms REWB.BoundaryRange.NearIndex.Regression.zero_width
#print axioms REWB.BoundaryRange.NearIndex.Regression.cached_separated
#print axioms REWB.BoundaryRange.NearIndex.Regression.cached_end
#print axioms REWB.BoundaryRange.NearIndex.Regression.cached_start
#print axioms REWB.BoundaryRange.FarLeft.scan_correct
#print axioms REWB.BoundaryRange.FarLeft.build_get
#print axioms REWB.BoundaryRange.FarLeft.query_correct
#print axioms REWB.BoundaryRange.FarLeft.component_le
#print axioms REWB.BoundaryRange.FarLeft.buildRow_work
#print axioms REWB.BoundaryRange.FarLeft.build_work
#print axioms REWB.BoundaryRange.FarLeft.scan_work
#print axioms REWB.BoundaryRange.FarLeft.query_work
#print axioms REWB.BoundaryRange.FarLeft.Regression.empty_actual_query
#print axioms REWB.BoundaryRange.FarLeft.Regression.invalid_left_rejected
#print axioms REWB.BoundaryRange.FarLeft.Regression.invalid_right_rejected

#print axioms REWB.MaskedTraversalFrontier.insert_valid
#print axioms REWB.MaskedTraversalFrontier.merge_valid
#print axioms REWB.MaskedTraversalFrontier.merge_mem
#print axioms REWB.MaskedTraversalFrontier.merge_measured
#print axioms REWB.MaskedTraversalDriver.build_valid
#print axioms REWB.MaskedTraversalDriver.build_mem
#print axioms REWB.MaskedTraversalDriver.node_children_at_parent
#print axioms REWB.MaskedTraversalDriver.build_measured
#print axioms REWB.MaskedTraversalDriver.build_imports
#print axioms REWB.MaskedTraversalDriver.build_work
#print axioms REWB.MaskedTraversalDriver.suffix_work
#print axioms REWB.MaskedTraversalDriver.build_band_locus
#print axioms REWB.MaskedTraversalDriver.build_cover
#print axioms REWB.MaskedTraversalDriver.suffix_band_complete
#print axioms REWB.MaskedTraversalDriver.suffix_cover
#print axioms REWB.MaskedTraversalDriver.Regression.actual_suffix_coverage
#print axioms REWB.MaskedRunCatalog.Map.bits_value
#print axioms REWB.MaskedRunCatalog.Map.key_value
#print axioms REWB.MaskedRunCatalog.Map.key_work
#print axioms REWB.MaskedRunCatalog.Map.put_lookup
#print axioms REWB.MaskedRunCatalog.Map.put_work
#print axioms REWB.MaskedRunCatalog.Map.read_value
#print axioms REWB.MaskedRunCatalog.Map.read_work
#print axioms REWB.MaskedRunCatalog.build_get
#print axioms REWB.MaskedRunCatalog.build_cells
#print axioms REWB.MaskedRunCatalog.build_work
#print axioms REWB.MaskedRunCatalog.lookupId_correct
#print axioms REWB.MaskedRunCatalog.lookup_found
#print axioms REWB.MaskedRunCatalog.ofBatch_exists
#print axioms REWB.MaskedRunCatalog.ofBatch_counts
#print axioms REWB.MaskedRunCatalog.ofBatch_eraseMany
#print axioms REWB.MaskedRunCatalog.ofBatch_cells
#print axioms REWB.MaskedRunCatalog.ofBatch_work_closed
#print axioms REWB.MaskedRunCatalog.prepare_work
#print axioms REWB.MaskedRunCatalog.descriptor_period
#print axioms REWB.MaskedRunCatalog.run_contains_right
#print axioms REWB.MaskedRunCatalog.discover_complete
#print axioms REWB.MaskedRunCatalog.descriptor_complete
#print axioms REWB.MaskedRunCatalog.descriptorShared_work
#print axioms REWB.MaskedRunCatalog.Regression.exact_ids
#print axioms REWB.MaskedRunCatalog.Regression.truncated_alias_rejected
#print axioms REWB.MaskedRunCatalog.Regression.short_mask_counts
#print axioms REWB.MaskedRunCatalog.Regression.huge_step_counts
#print axioms REWB.MaskedRunCatalog.Regression.actual_dense_catalog

#print axioms REWB.BoundaryRange.NearIndex.Border.build_gap
#print axioms REWB.BoundaryRange.NearIndex.Border.gap_correct
#print axioms REWB.BoundaryRange.NearIndex.Border.gap_iff_split
#print axioms REWB.BoundaryRange.NearIndex.Border.copy_correct
#print axioms REWB.BoundaryRange.NearIndex.Border.queryAt_correct
#print axioms REWB.BoundaryRange.NearIndex.Border.row_correct
#print axioms REWB.BoundaryRange.NearIndex.Border.query_correct
#print axioms REWB.BoundaryRange.NearIndex.Border.gap_work
#print axioms REWB.BoundaryRange.NearIndex.Border.copy_work
#print axioms REWB.BoundaryRange.NearIndex.Border.queryAt_work
#print axioms REWB.BoundaryRange.NearIndex.Border.row_work
#print axioms REWB.BoundaryRange.NearIndex.Border.query_work
#print axioms REWB.BoundaryRange.NearIndex.Border.atBudget_height
#print axioms REWB.BoundaryRange.NearIndex.Border.query_work_height
#print axioms REWB.BoundaryRange.NearIndex.Border.buildGap_work
#print axioms REWB.BoundaryRange.NearIndex.Border.build_work
#print axioms REWB.BoundaryRange.NearIndex.Full.query_correct
#print axioms REWB.BoundaryRange.NearIndex.Full.query_iff
#print axioms REWB.BoundaryRange.NearIndex.Full.build_work
#print axioms REWB.BoundaryRange.NearIndex.Full.query_work
#print axioms REWB.BoundaryRange.NearIndex.Border.Regression.positive_in_same_block
#print axioms REWB.BoundaryRange.NearIndex.Border.Regression.empty_in_same_block
#print axioms REWB.BoundaryRange.NearIndex.Border.Regression.clipped_at_target_start
#print axioms REWB.BoundaryRange.NearIndex.Border.Regression.common_split_required
#print axioms REWB.BoundaryRange.NearIndex.Border.Regression.all_four_positive
#print axioms REWB.BoundaryRange.NearIndex.Border.Regression.all_four_zero_width
#print axioms REWB.ResidualSeparated.slice_inside
#print axioms REWB.ResidualSeparated.Window.copy
#print axioms REWB.ResidualSeparated.window_of_strip
#print axioms REWB.ResidualSeparated.gap_run
#print axioms REWB.ResidualSeparated.tail_accepts
#print axioms REWB.ResidualSeparated.outerSuffix_accepts
#print axioms REWB.ResidualSeparated.p1_iff
#print axioms REWB.ResidualSeparated.P1Witness.sound
#print axioms REWB.ResidualSeparated.p1_complete
#print axioms REWB.ResidualSeparated.innerPrefix_accepts
#print axioms REWB.ResidualSeparated.p2_iff
#print axioms REWB.ResidualSeparated.P2Witness.sound
#print axioms REWB.ResidualSeparated.p2_complete
#print axioms REWB.ResidualRunWindows.candidate_work
#print axioms REWB.ResidualRunWindows.shifted_equal
#print axioms REWB.ResidualRunWindows.candidate_sound
#print axioms REWB.ResidualRunWindows.candidate_complete
#print axioms REWB.ResidualRunWindows.large_pair_multiple
#print axioms REWB.ResidualRunWindows.low_valid
#print axioms REWB.ResidualRunWindows.large_valid
#print axioms REWB.ResidualRunWindows.low_window
#print axioms REWB.ResidualRunWindows.large_window
#print axioms REWB.ResidualSeparated.Regression.earlier_source_outside_strip
#print axioms REWB.ResidualSeparated.Regression.nested_inner_inside_strip
#print axioms REWB.ResidualSeparated.Regression.boundary_allows_earlier_source
#print axioms REWB.ResidualSeparated.Regression.one_use_enforces_source_lower_bound
#print axioms REWB.ResidualStripSchedule.eq_of_shared_cell
#print axioms REWB.ResidualStripSchedule.allCells_nodup
#print axioms REWB.ResidualStripSchedule.totalSpan_bound
#print axioms REWB.ResidualStripSchedule.long_count
#print axioms REWB.ResidualStripSchedule.select_eq_selectTR
#print axioms REWB.ResidualStripSchedule.dedup_mem
#print axioms REWB.ResidualStripSchedule.dedup_nodup
#print axioms REWB.ResidualStripSchedule.dedup_work
#print axioms REWB.ResidualStripSchedule.generate_span
#print axioms REWB.ResidualStripSchedule.generate_length
#print axioms REWB.ResidualStripSchedule.generate_complete
#print axioms REWB.ResidualStripSchedule.generate_maximal
#print axioms REWB.ResidualStripSchedule.cutLoop_eq_cutLoopTR
#print axioms REWB.ResidualStripSchedule.cutLoop_mem
#print axioms REWB.ResidualStripSchedule.gridCount_bound
#print axioms REWB.ResidualStripSchedule.collect_eq_collectTR
#print axioms REWB.ResidualStripSchedule.collect_probes
#print axioms REWB.ResidualStripSchedule.collect_queries
#print axioms REWB.ResidualStripSchedule.collect_work
#print axioms REWB.ResidualStripSchedule.prepare_queries
#print axioms REWB.ResidualStripSchedule.prepare_query_length
#print axioms REWB.ResidualStripSchedule.prepare_sound
#print axioms REWB.ResidualStripSchedule.prepare_complete
#print axioms REWB.ResidualStripSchedule.prepare_existing_cut
#print axioms REWB.ResidualStripSchedule.generate_work
#print axioms REWB.ResidualStripSchedule.prepare_work
#print axioms REWB.ResidualStripSchedule.Regression.repeated_strip_once
#print axioms REWB.ResidualStripSchedule.Regression.separated_once
#print axioms REWB.ResidualStripSchedule.Regression.overlap_exact_cuts
#print axioms REWB.ResidualStripSchedule.Regression.empty_schedule
#print axioms REWB.ResidualStripSchedule.Regression.existing_short_gap_cut
#print axioms REWB.ResidualStripSchedule.Regression.actual_query_budget
#print axioms REWB.MaskedTraversalBankReady.prepare_dense_reset
#print axioms REWB.MaskedTraversalBankReady.compile_reset_present
#print axioms REWB.MaskedTraversalBankReady.anchorBounds_reset
#print axioms REWB.MaskedTraversalBankReady.previous_next
#print axioms REWB.MaskedTraversalBankReady.incoming_bound
#print axioms REWB.MaskedTraversalBankReady.prepare_reset_geometry
#print axioms REWB.MaskedTraversalBankReady.prepare_work
#print axioms REWB.MaskedTraversalBankReady.compile_reset_work
#print axioms REWB.MaskedTraversalBankReady.compile_reset_current
#print axioms REWB.MaskedTraversalBankReady.write_selected
#print axioms REWB.MaskedTraversalBankReady.write_other
#print axioms REWB.MaskedTraversalBankReady.write_sources
#print axioms REWB.MaskedTraversalDriver.mem_bandView
#print axioms REWB.MaskedTraversalDriver.chain_disjoint
#print axioms REWB.MaskedTraversalDriver.lower_disjoint
#print axioms REWB.MaskedTraversalDriver.band_position
#print axioms REWB.MaskedTraversalDriver.build_disjoint
#print axioms REWB.MaskedTraversalDriver.suffix_disjoint
#print axioms REWB.MaskedTraversalDriver.pairwise_unique
#print axioms REWB.MaskedTraversalDriver.suffix_unique
#print axioms REWB.MaskedTraversalDriver.charges_nodup
#print axioms REWB.MaskedTraversalDriver.suffix_charges_nodup
#print axioms REWB.MaskedTraversalDriver.density_square
#print axioms REWB.MaskedTraversalDriver.suffix_charges_budget
#print axioms REWB.MaskedTraversalDriver.suffix_exactly_once
#print axioms REWB.OneUseRange.Border.Regular.maps_value
#print axioms REWB.OneUseRange.Border.Regular.maps_work
#print axioms REWB.OneUseRange.Border.Regular.prefix_slice
#print axioms REWB.OneUseRange.Border.Regular.point_correct
#print axioms REWB.OneUseRange.Border.Regular.dense_correct
#print axioms REWB.OneUseRange.Border.Regular.query_correct
#print axioms REWB.OneUseRange.Border.Regular.query_work
#print axioms REWB.OneUseRange.Border.Regular.choice_correct
#print axioms REWB.OneUseRange.Border.Regular.choice_work
#print axioms REWB.OneUseRange.Border.Regular.dyadic_correct
#print axioms REWB.OneUseRange.Border.Regular.dyadic_work_closed
#print axioms REWB.OneUseRange.Border.changeRanges_build
#print axioms REWB.OneUseRange.Border.startRanges_build
#print axioms REWB.OneUseRange.Border.stopRanges_build
#print axioms REWB.OneUseRange.Border.any_correct
#print axioms REWB.OneUseRange.Border.any_work
#print axioms REWB.OneUseRange.Border.middle_bounds
#print axioms REWB.OneUseRange.Border.middle_cut
#print axioms REWB.OneUseRange.Border.split_gap
#print axioms REWB.OneUseRange.Border.state_correct
#print axioms REWB.OneUseRange.Border.positive_correct
#print axioms REWB.OneUseRange.Border.inner_correct
#print axioms REWB.OneUseRange.Border.queryAt_correct
#print axioms REWB.OneUseRange.Border.query_correct
#print axioms REWB.OneUseRange.Border.at_iff_cuts
#print axioms REWB.OneUseRange.Border.oneUse_iff
#print axioms REWB.OneUseRange.Border.query_iff_cuts
#print axioms REWB.OneUseRange.Border.state_work
#print axioms REWB.OneUseRange.Border.inner_work
#print axioms REWB.OneUseRange.Border.queryAt_work
#print axioms REWB.OneUseRange.Border.query_work
#print axioms REWB.OneUseRange.Border.build_work
#print axioms REWB.OneUseRange.Border.atBudget_height
#print axioms REWB.OneUseRange.Border.query_work_height
#print axioms REWB.OneUseRange.Border.partition
#print axioms REWB.OneUseRange.Border.Regression.lower_bound_preserved
#print axioms REWB.OneUseRange.Border.Regression.common_midpoint_state
#print axioms REWB.OneUseRange.Border.Regression.odd_midpoint_positive
#print axioms REWB.OneUseRange.Border.Regression.reset_gap_positive
#print axioms REWB.OneUseRange.Border.Regression.empty_at_terminal
#print axioms REWB.OneUseRange.Border.Regression.empty_input
#print axioms REWB.OneUseRange.Border.Regression.stop_shares_tree
#print axioms REWB.ResidualDispatch.lowRows_value
#print axioms REWB.ResidualDispatch.lowRows_work
#print axioms REWB.ResidualDispatch.largeRows_value
#print axioms REWB.ResidualDispatch.largeRows_work
#print axioms REWB.ResidualDispatch.select_eq_selectTR
#print axioms REWB.ResidualDispatch.select_mem
#print axioms REWB.ResidualDispatch.select_counts
#print axioms REWB.ResidualDispatch.prepare_mem
#print axioms REWB.ResidualDispatch.prepare_count
#print axioms REWB.ResidualDispatch.compile_selector_work
#print axioms REWB.ResidualDispatch.prepare_sound
#print axioms REWB.ResidualDispatch.residual_window
#print axioms REWB.ResidualDispatch.scheduled_p1_sound
#print axioms REWB.ResidualDispatch.scheduled_p2_sound
#print axioms REWB.ResidualDispatch.global_p1_sound
#print axioms REWB.ResidualDispatch.p1_dispatch_complete
#print axioms REWB.ResidualDispatch.p2_dispatch_complete
#print axioms REWB.ResidualDispatch.p1_dispatch_iff
#print axioms REWB.ResidualDispatch.p2_dispatch_iff
#print axioms REWB.ResidualDispatch.prepare_selectors
#print axioms REWB.ResidualDispatch.prepare_windows
#print axioms REWB.ResidualDispatch.prepare_selectorWork
#print axioms REWB.ResidualDispatch.runWork_bound
#print axioms REWB.ResidualDispatch.prepare_work
#print axioms REWB.ResidualDispatch.stateQueries_bound
#print axioms REWB.ResidualDispatch.Regression.candidate_once
#print axioms REWB.ResidualDispatch.Regression.concrete_rows
#print axioms REWB.ResidualDispatch.Regression.earlier_source_dispatched
#print axioms REWB.ResidualDispatch.Regression.earlier_source_match
#print axioms REWB.ResidualDispatch.Regression.empty_dispatch
#print axioms REWB.OneUseRange.FarAggregate.build_size
#print axioms REWB.OneUseRange.FarAggregate.build_work_exact
#print axioms REWB.OneUseRange.FarAggregate.build_work
#print axioms REWB.OneUseRange.FarAggregate.query_work
#print axioms REWB.OneUseRange.FarAggregate.sweep_correct
#print axioms REWB.OneUseRange.FarAggregate.build_correct
#print axioms REWB.OneUseRange.FarAggregate.query_correct
#print axioms REWB.OneUseRange.FarAggregate.query_end
#print axioms REWB.OneUseRange.FarAggregate.query_zero
#print axioms REWB.OneUseRange.FarAggregate.query_empty
#print axioms REWB.OneUseRange.FarAggregate.bit_outside
#print axioms REWB.OneUseRange.FarAggregate.query_substitute
#print axioms REWB.OneUseRange.FarAggregate.query_prefix_correct
#print axioms REWB.OneUseRange.FarAggregate.query_prefix_substitute
#print axioms REWB.OneUseRange.FarAggregate.query_maskedStart
#print axioms REWB.MaskedTraversalDirty.markChange_spec
#print axioms REWB.MaskedTraversalDirty.importLoop_patches
#print axioms REWB.MaskedTraversalDirty.merge_patches
#print axioms REWB.MaskedTraversalDirty.patches_spec
#print axioms REWB.MaskedTraversalDirty.live_spec
#print axioms REWB.MaskedTraversalDirty.crossing_spec
#print axioms REWB.MaskedTraversalRepair.anchorsLoop_read
#print axioms REWB.MaskedTraversalRepair.anchorsLoop_bounds
#print axioms REWB.MaskedTraversalRepair.banksLoop_selected
#print axioms REWB.MaskedTraversalRepair.banksLoop_budget
#print axioms REWB.MaskedTraversalRepair.reset_current
#print axioms REWB.MaskedTraversalRepair.reset_work

#print axioms REWB.MaskedTraversalContext.successors_spec
#print axioms REWB.MaskedTraversalContext.pred_next
#print axioms REWB.MaskedTraversalContext.incoming_unchanged
#print axioms REWB.MaskedTraversalContext.prepare_some
#print axioms REWB.MaskedTraversalContext.compile_selected
#print axioms REWB.MaskedTraversalContext.runBacked_context
#print axioms REWB.MaskedTraversalContext.retained_geometry
#print axioms REWB.MaskedTraversalContext.store_current
#print axioms REWB.MaskedTraversalContext.compile_current
#print axioms REWB.MaskedTraversalContext.write_ready
#print axioms REWB.MaskedTraversalContext.compile_work
#print axioms REWB.MaskedTraversalContext.applyLoop_work
#print axioms REWB.OneUseRange.Reverse.accepts_slice
#print axioms REWB.OneUseRange.Reverse.accepts_complement
#print axioms REWB.OneUseRange.Reverse.at_congr
#print axioms REWB.OneUseRange.Reverse.at_forward
#print axioms REWB.OneUseRange.Reverse.twice
#print axioms REWB.OneUseRange.Reverse.at_reverse
#print axioms REWB.OneUseRange.Reverse.oneUseRange_reverse
#print axioms REWB.OneUseRange.Reverse.farSource_reverse
#print axioms REWB.OneUseRange.FarSelection.key_variant
#print axioms REWB.OneUseRange.FarSelection.key_work
#print axioms REWB.OneUseRange.FarSelection.build_work
#print axioms REWB.OneUseRange.FarSelection.prefix_slice
#print axioms REWB.OneUseRange.FarSelection.masked_prefix
#print axioms REWB.OneUseRange.FarSelection.farTarget_iff
#print axioms REWB.OneUseRange.FarBank.build_get
#print axioms REWB.OneUseRange.FarBank.query_bits
#print axioms REWB.OneUseRange.FarBank.query_correct
#print axioms REWB.OneUseRange.FarBank.build_work
#print axioms REWB.OneUseRange.FarBank.query_work
#print axioms REWB.OneUseRange.Grid.position_bound
#print axioms REWB.OneUseRange.Grid.floor_slot
#print axioms REWB.OneUseRange.Grid.ceil_slot
#print axioms REWB.OneUseRange.Grid.floor_bounds
#print axioms REWB.OneUseRange.Grid.ceil_bounds
#print axioms REWB.OneUseRange.Grid.choose_positions
#print axioms REWB.OneUseRange.Grid.choose_bounds
#print axioms REWB.OneUseRange.Grid.choose_work
#print axioms REWB.OneUseRange.Grid.reverse_grid_bound
#print axioms REWB.OneUseRange.Cache.build_forward
#print axioms REWB.OneUseRange.Cache.build_backward_query
#print axioms REWB.OneUseRange.Cache.queryValid_correct
#print axioms REWB.OneUseRange.Cache.query_correct
#print axioms REWB.OneUseRange.Cache.forward_work
#print axioms REWB.OneUseRange.Cache.backward_work
#print axioms REWB.OneUseRange.Cache.build_work
#print axioms REWB.OneUseRange.Cache.queryValid_work
#print axioms REWB.OneUseRange.Cache.query_work
#print axioms REWB.OneUseRange.Cache.Regression.emptyRows_ready
#print axioms REWB.OneUseRange.Cache.Regression.emptyInputs_ready
#print axioms REWB.OneUseRange.Cache.Regression.empty_input
#print axioms REWB.OneUseRange.Cache.Regression.epsilon_rejected_by_prefix
#print axioms REWB.OneUseRange.Cache.Regression.invalid_range
#print axioms REWB.OneUseRange.Cache.Regression.clipped_terminal_grid
#print axioms REWB.OneUseRange.Cache.Regression.width_exceeds_text
#print axioms REWB.OneUseRange.Cache.Regression.selected_core_equal
#print axioms REWB.OneUseRange.Cache.Regression.bank_core_equal

#print axioms REWB.ShortOuter.Keys.loop_good
#print axioms REWB.ShortOuter.Keys.get_lookup
#print axioms REWB.ShortOuter.Keys.get_bound
#print axioms REWB.ShortOuter.Keys.get_eq_general
#print axioms REWB.ShortOuter.Keys.build_work
#print axioms REWB.ShortOuter.Keys.build_next
#print axioms REWB.ShortOuter.Sweep.move_correct
#print axioms REWB.ShortOuter.Sweep.update_good
#print axioms REWB.ShortOuter.Sweep.update_value
#print axioms REWB.ShortOuter.Sweep.update_work
#print axioms REWB.ShortOuter.Suffix.get_correct
#print axioms REWB.ShortOuter.Suffix.build_work
#print axioms REWB.ShortOuter.Band.inserts_stage
#print axioms REWB.ShortOuter.Band.probes_stage
#print axioms REWB.ShortOuter.Band.run_correct
#print axioms REWB.ShortOuter.Band.get_correct
#print axioms REWB.ShortOuter.Band.get_iff
#print axioms REWB.ShortOuter.Band.run_bounds
#print axioms REWB.ShortOuter.Band.build_work
#print axioms REWB.ShortOuter.Band.build_touches
#print axioms REWB.ShortOuter.Band.build_bits_size
#print axioms REWB.ShortOuter.Band.query_work

#print axioms REWB.MaskedTraversalAggregate.meaning_read
#print axioms REWB.MaskedTraversalAggregate.meaning_jump
#print axioms REWB.MaskedTraversalAggregate.meaning_direct
#print axioms REWB.MaskedTraversalAggregate.meaning_cursor
#print axioms REWB.MaskedTraversalAggregate.meaning_final
#print axioms REWB.MaskedTraversalAggregate.prepare_good
#print axioms REWB.MaskedTraversalAggregate.prepare_work
#print axioms REWB.MaskedTraversalAggregate.prepare_cells
#print axioms REWB.MaskedTraversalAggregate.refresh_good
#print axioms REWB.MaskedTraversalAggregate.refresh_cells
#print axioms REWB.MaskedTraversalAggregate.refresh_work
#print axioms REWB.MaskedTraversalAggregate.refreshMany_good
#print axioms REWB.MaskedTraversalAggregate.refreshMany_work
#print axioms REWB.MaskedTraversalAggregate.shorten_cells
#print axioms REWB.MaskedTraversalAggregate.product_chain
#print axioms REWB.MaskedTraversalAggregate.cache_chain
#print axioms REWB.MaskedTraversalAggregate.component_product
#print axioms REWB.MaskedTraversalAggregate.region_view
#print axioms REWB.MaskedTraversalAggregate.region_chain
#print axioms REWB.MaskedTraversalAggregate.region_work
#print axioms REWB.MaskedTraversalAggregate.close_correct
#print axioms REWB.MaskedTraversalAggregate.close_probes
#print axioms REWB.MaskedTraversalAggregate.queryBand_correct
#print axioms REWB.MaskedTraversalAggregate.queryBand_counters
#print axioms REWB.MaskedTraversalAggregate.chain_denotes
#print axioms REWB.MaskedTraversalAggregate.denotes_append
#print axioms REWB.MaskedTraversalAggregate.physical_meaning
#print axioms REWB.MaskedTraversalAggregate.physical_final
#print axioms REWB.MaskedTraversalAggregate.masked_of_final
#print axioms REWB.MaskedTraversalAggregate.queryBand_sound
#print axioms REWB.MaskedTraversalAggregate.Clip.selected_mem
#print axioms REWB.MaskedTraversalAggregate.Clip.selected_length
#print axioms REWB.MaskedTraversalAggregate.Clip.selected_nodup
#print axioms REWB.MaskedTraversalAggregate.Clip.plan_length
#print axioms REWB.MaskedTraversalAggregate.Clip.plan_nodup
#print axioms REWB.MaskedTraversalAggregate.Clip.plan_work
#print axioms REWB.MaskedTraversalAggregate.Clip.predecessor_selection
#print axioms REWB.MaskedTraversalAggregate.Clip.plan_selection
#print axioms REWB.MaskedTraversalAggregate.Clip.config_anchor
#print axioms REWB.MaskedTraversalAggregate.Clip.config_runBacked
#print axioms REWB.MaskedTraversalAggregate.Clip.atLeader_good
#print axioms REWB.MaskedTraversalAggregate.Clip.atLeader_calls
#print axioms REWB.MaskedTraversalAggregate.Clip.atLeader_work
#print axioms REWB.MaskedTraversalAggregate.Clip.atLeader_cells
#print axioms REWB.MaskedTraversalAggregate.Clip.applyKeys_good
#print axioms REWB.MaskedTraversalAggregate.Clip.applyKeys_calls
#print axioms REWB.MaskedTraversalAggregate.Clip.window_good
#print axioms REWB.MaskedTraversalAggregate.Clip.window_calls
#print axioms REWB.MaskedTraversalAggregate.Clip.config_geometry
#print axioms REWB.MaskedTraversalAggregate.Clip.selectedWork_bound
#print axioms REWB.MaskedTraversalAggregate.Clip.applyKeys_work
#print axioms REWB.MaskedTraversalAggregate.Clip.window_work
#print axioms REWB.MaskedTraversalAggregate.queryWindow_selected
#print axioms REWB.MaskedTraversalAggregate.queryWindow_correct
#print axioms REWB.MaskedTraversalAggregate.queryWindow_counts
#print axioms REWB.MaskedTraversalAggregate.queryWindow_clipping_work
#print axioms REWB.MaskedTraversalAggregate.queryWindow_band_counters
#print axioms REWB.MaskedTraversalAggregate.dense_select_shorter
#print axioms REWB.MaskedTraversalAggregate.point_select_shorter
#print axioms REWB.MaskedTraversalAggregate.store_select_shorter
#print axioms REWB.MaskedTraversalAggregate.store_shorter_current

#print axioms REWB.MaskedTraversalNeighbor.around_left
#print axioms REWB.MaskedTraversalNeighbor.around_right
#print axioms REWB.MaskedTraversalNeighbor.describe_insert_away
#print axioms REWB.MaskedTraversalNeighbor.add_describe_away
#print axioms REWB.MaskedTraversalNeighbor.describe_additions_away
#print axioms REWB.MaskedTraversalNeighbor.shorten_describe_away
#print axioms REWB.MaskedTraversalNeighbor.crossing_describe_unmarked
#print axioms REWB.MaskedTraversalNeighbor.importLoop_describe_unmarked
#print axioms REWB.MaskedTraversalNeighbor.merge_describe_unmarked
#print axioms REWB.MaskedTraversalNeighbor.add_anchorBoundsAway
#print axioms REWB.MaskedTraversalNeighbor.crossing_anchorBoundsAway
#print axioms REWB.MaskedTraversalNeighbor.merge_anchorBoundsAway
#print axioms REWB.MaskedTraversalAggregate.Cells.prepare_represents
#print axioms REWB.MaskedTraversalAggregate.Cells.slot_view
#print axioms REWB.MaskedTraversalAggregate.Cells.refresh_represents
#print axioms REWB.MaskedTraversalAggregate.Cells.refreshMany_represents
#print axioms REWB.MaskedTraversalAggregate.Cells.denotes_entries
#print axioms REWB.MaskedTraversalAggregate.Cells.denotes_region
#print axioms REWB.MaskedTraversalAggregate.Cells.entry_current
#print axioms REWB.MaskedTraversalAggregate.Cells.clippedEntry_selected
#print axioms REWB.MaskedTraversalAggregate.Cells.atLeader_represents
#print axioms REWB.MaskedTraversalAggregate.Cells.applyKeys_represents
#print axioms REWB.MaskedTraversalAggregate.Cells.window_represents
#print axioms REWB.MaskedTraversalAggregate.refreshCurrent_sources
#print axioms REWB.MaskedTraversalAggregate.eraseCurrent_sources
#print axioms REWB.MaskedTraversalAggregate.refreshCurrent_good
#print axioms REWB.MaskedTraversalAggregate.eraseCurrent_good
#print axioms REWB.MaskedTraversalAggregate.refreshCurrent_calls
#print axioms REWB.MaskedTraversalAggregate.eraseCurrent_calls
#print axioms REWB.MaskedTraversalAggregate.refreshCurrent_selected
#print axioms REWB.MaskedTraversalAggregate.refreshCurrent_work
#print axioms REWB.MaskedTraversalAggregate.selectedCurrentWork_bound
#print axioms REWB.MaskedTraversalAggregate.eraseCurrent_work
#print axioms REWB.MaskedTraversalAggregate.refreshCurrent_represents
#print axioms REWB.MaskedTraversalAggregate.eraseCurrent_represents
#print axioms REWB.MaskedTraversalAggregate.Cells.gated_allows
#print axioms REWB.MaskedTraversalAggregate.Cells.windowFor_selection
#print axioms REWB.MaskedTraversalAggregate.Cells.windowFor_current
#print axioms REWB.MaskedTraversalAggregate.Cells.entryView_reindexed
#print axioms REWB.MaskedTraversalAggregate.Cells.shorten_represents
#print axioms REWB.MaskedTraversalAggregate.Cells.point_reindex_word
#print axioms REWB.MaskedTraversalAggregate.Cells.dense_reindex_word
#print axioms REWB.MaskedTraversalAggregate.Cells.store_reindex
#print axioms REWB.MaskedTraversalRetained.copies_mem
#print axioms REWB.MaskedTraversalRetained.anchorsLoop_slot
#print axioms REWB.MaskedTraversalRetained.reset_own
#print axioms REWB.MaskedTraversalRetained.reset_all
#print axioms REWB.MaskedTraversalRetained.next_marks_first
#print axioms REWB.MaskedTraversalRetained.overlap_record
#print axioms REWB.MaskedTraversalRetained.mode_away
#print axioms REWB.MaskedTraversalRetained.mode_between
#print axioms REWB.MaskedTraversalRetained.band_own
#print axioms REWB.MaskedTraversalRetained.add_away
#print axioms REWB.MaskedTraversalRetained.merge_away
#print axioms REWB.MaskedTraversalRetained.crossing_away
#print axioms REWB.MaskedTraversalRetained.band_all
#print axioms REWB.MaskedTraversalRetained.crossing_reset_all
#print axioms REWB.BoundaryRange.FarRight.prepare_get
#print axioms REWB.BoundaryRange.FarRight.readMask_correct
#print axioms REWB.BoundaryRange.FarRight.masked_mask_congr
#print axioms REWB.BoundaryRange.FarRight.ready_original
#print axioms REWB.BoundaryRange.FarRight.prepare_masks_work
#print axioms REWB.BoundaryRange.FarRight.prepare_work
#print axioms REWB.BoundaryRange.FarRight.unionPoint_correct
#print axioms REWB.BoundaryRange.FarRight.unionPoint_work
#print axioms REWB.BoundaryRange.FarRight.unionRow_correct
#print axioms REWB.BoundaryRange.FarRight.unionRow_work
#print axioms REWB.BoundaryRange.FarRight.build_get
#print axioms REWB.BoundaryRange.FarRight.reverse_suffix
#print axioms REWB.BoundaryRange.FarRight.query_bits
#print axioms REWB.BoundaryRange.FarRight.query_correct
#print axioms REWB.BoundaryRange.FarRight.assemble_work
#print axioms REWB.BoundaryRange.FarRight.build_work
#print axioms REWB.BoundaryRange.FarRight.query_work
#print axioms REWB.BoundaryRange.CacheGrid.bounds
#print axioms REWB.BoundaryRange.CacheGrid.span
#print axioms REWB.BoundaryRange.CacheGrid.slot_bound
#print axioms REWB.BoundaryRange.CacheGrid.selected_bounds
#print axioms REWB.BoundaryRange.Cache.buildBlock_lower
#print axioms REWB.BoundaryRange.Cache.buildBlock_upper
#print axioms REWB.BoundaryRange.Cache.buildBlock_far
#print axioms REWB.BoundaryRange.Cache.buildBlock_near
#print axioms REWB.BoundaryRange.Cache.prepare_block
#print axioms REWB.BoundaryRange.Cache.build_prepared
#print axioms REWB.BoundaryRange.Cache.build_right
#print axioms REWB.BoundaryRange.Cache.prepare_request_mask
#print axioms REWB.BoundaryRange.Cache.queryValid_correct
#print axioms REWB.BoundaryRange.Cache.query_correct
#print axioms REWB.BoundaryRange.Cache.buildBlock_work
#print axioms REWB.BoundaryRange.Cache.prepare_blocks_work
#print axioms REWB.BoundaryRange.Cache.prepare_work
#print axioms REWB.BoundaryRange.Cache.assemble_right_work
#print axioms REWB.BoundaryRange.Cache.assemble_work
#print axioms REWB.BoundaryRange.Cache.build_work
#print axioms REWB.BoundaryRange.Cache.threeBudget_mono
#print axioms REWB.BoundaryRange.Cache.borderBudget_mono
#print axioms REWB.BoundaryRange.Cache.queryValid_work
#print axioms REWB.BoundaryRange.Cache.query_work
#print axioms REWB.BoundaryRange.Cache.Regression.closedRows_ready
#print axioms REWB.BoundaryRange.Cache.Regression.emptyInputs_ready
#print axioms REWB.BoundaryRange.Cache.Regression.empty_input
#print axioms REWB.BoundaryRange.Cache.Regression.empty_capture_rejected
#print axioms REWB.BoundaryRange.Cache.Regression.finite_union_missing_bits
#print axioms REWB.BoundaryRange.Cache.Regression.finite_union_empty
#print axioms REWB.BoundaryRange.Cache.Regression.zero_width_terminal_block
#print axioms REWB.BoundaryRange.Cache.Regression.clipped_last_block
#print axioms REWB.BoundaryRange.Cache.Regression.invalid_range
#print axioms REWB.BoundaryRange.Cache.Regression.two_stage
#print axioms REWB.BoundaryRange.Cache.Regression.all_gap
#print axioms REWB.BoundaryRange.Cache.Regression.all_masked
#print axioms REWB.BoundaryRange.Cache.Regression.copiedMasks_ready
#print axioms REWB.MaskedTraversalAggregate.Cells.EntryState.shortened
#print axioms REWB.MaskedTraversalAggregate.Cells.Coherent.shortened
#print axioms REWB.MaskedTraversalAggregate.Cells.refreshCurrent_other
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseCurrent_other
#print axioms REWB.MaskedTraversalAggregate.Cells.EntryState.erased_away
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseCurrent_ready
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseCurrent_coherent
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseCurrent_complete
#print axioms REWB.MaskedTraversalIncoming.previous_unmarked
#print axioms REWB.MaskedTraversalIncoming.predecessor_preserved
#print axioms REWB.MaskedTraversalIncoming.incoming_transport
#print axioms REWB.MaskedTraversalIncoming.retained_transport
#print axioms REWB.MaskedTraversalIncoming.add_incoming_away
#print axioms REWB.MaskedTraversalIncoming.merge_incoming_away
#print axioms REWB.MaskedTraversalIncoming.crossing_incoming_away
#print axioms REWB.MaskedTraversalIncoming.reset_preserves_transport
#print axioms REWB.MaskedTraversalIncoming.populated_length
#print axioms REWB.MaskedTraversalIncoming.band_incoming
#print axioms REWB.MaskedTraversalIncoming.config_preserved
#print axioms REWB.MaskedTraversalIncoming.retained_config_preserved
#print axioms REWB.ShortOuter.Regular.row_get
#print axioms REWB.ShortOuter.Regular.row_work
#print axioms REWB.ShortOuter.Regular.accepts_correct
#print axioms REWB.ShortOuter.Regular.build_work
#print axioms REWB.ShortOuter.Ready.mask_get
#print axioms REWB.ShortOuter.Ready.row_work
#print axioms REWB.ShortOuter.Ready.query_work
#print axioms REWB.ShortOuter.Ready.build_work
#print axioms REWB.ShortOuter.Ready.get_iff
#print axioms REWB.ShortOuter.Ready.get_expanded
#print axioms REWB.ShortOuter.Collect.mem
#print axioms REWB.ShortOuter.Collect.length
#print axioms REWB.ShortOuter.Collect.work
#print axioms REWB.ShortOuter.Join.run_correct
#print axioms REWB.ShortOuter.Join.run_work
#print axioms REWB.ShortOuter.Join.run_work_max
#print axioms REWB.ShortOuter.prefix_correct
#print axioms REWB.ShortOuter.prepare_work
#print axioms REWB.ShortOuter.prepare_ready_correct
#print axioms REWB.ShortOuter.P1.sources_length
#print axioms REWB.ShortOuter.P1.targets_length
#print axioms REWB.ShortOuter.P1.sources_work
#print axioms REWB.ShortOuter.P1.targets_work
#print axioms REWB.ShortOuter.P1.match_iff
#print axioms REWB.ShortOuter.P1.solve_correct
#print axioms REWB.ShortOuter.P1.solve_work
#print axioms REWB.ShortOuter.P1.solve_sound
#print axioms REWB.ShortOuter.P1.solve_zero_limit
#print axioms REWB.ShortOuter.P2.sources_length
#print axioms REWB.ShortOuter.P2.targets_length
#print axioms REWB.ShortOuter.P2.sources_work
#print axioms REWB.ShortOuter.P2.targets_work
#print axioms REWB.ShortOuter.P2.match_iff
#print axioms REWB.ShortOuter.P2.block_correct
#print axioms REWB.ShortOuter.P2.block_work
#print axioms REWB.ShortOuter.P2.solve_correct
#print axioms REWB.ShortOuter.P2.solve_work
#print axioms REWB.ShortOuter.P2.solve_sound
#print axioms REWB.ShortOuter.P2.solve_zero_limit
#print axioms REWB.ShortOuter.p1_dispatch_iff
#print axioms REWB.ShortOuter.p2_dispatch_iff
#print axioms REWB.ShortOuter.Cost.join_envelope
#print axioms REWB.ShortOuter.Cost.prepare_envelope
#print axioms REWB.ShortOuter.Cost.p1_budget
#print axioms REWB.ShortOuter.Cost.p2_budget
#print axioms REWB.ShortOuter.Cost.p1_work
#print axioms REWB.ShortOuter.Cost.p2_work
#print axioms REWB.ShortOuter.Regression.empty_p1
#print axioms REWB.ShortOuter.Regression.empty_p2
#print axioms REWB.ShortOuter.Regression.empty_outer_nonempty_gap_p1
#print axioms REWB.ShortOuter.Regression.empty_outer_nonempty_gap_p2
#print axioms REWB.ShortOuter.Regression.global_earlier_source
#print axioms REWB.ShortOuter.Regression.p2_empty_inner
#print axioms REWB.ShortOuter.Regression.strict_limit_p1
#print axioms REWB.ShortOuter.Regression.strict_limit_p2
#print axioms REWB.ShortOuter.Regression.zero_limit_p1
#print axioms REWB.ShortOuter.Regression.zero_limit_p2
#print axioms REWB.MaskedTraversalAggregate.Cells.Coherent.current
#print axioms REWB.MaskedTraversalAggregate.Cells.Linked.at_length
#print axioms REWB.MaskedTraversalAggregate.Cells.Linked.clipped
#print axioms REWB.MaskedTraversalAggregate.Cells.Current.cell_meaning
#print axioms REWB.MaskedTraversalAggregate.Cells.CurrentEntries.denotes_region
#print axioms REWB.MaskedTraversalAggregate.Cells.erasedEntries_config
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseCurrent_linked
#print axioms REWB.MaskedTraversalAggregate.Cells.shorten_linked
#print axioms REWB.MaskedTraversalAggregate.Cells.clipped_presence
#print axioms REWB.MaskedTraversalAggregate.Cells.clippedEntry_present
#print axioms REWB.MaskedTraversalAggregate.Cells.atLeader_ready
#print axioms REWB.MaskedTraversalAggregate.Cells.applyKeys_ready
#print axioms REWB.MaskedTraversalAggregate.Cells.plan_keys_leaders
#print axioms REWB.MaskedTraversalAggregate.Cells.window_ready
#print axioms REWB.MaskedTraversalAggregate.Cells.clipEntries_get
#print axioms REWB.MaskedTraversalAggregate.Cells.clipEntries_current
#print axioms REWB.MaskedTraversalAggregate.Cells.clipEntries_linked
#print axioms REWB.MaskedTraversalAggregate.Cells.clipEntries_complete
#print axioms REWB.MaskedTraversalAggregate.Cells.clipEntries_config
#print axioms REWB.MaskedTraversalAggregate.Cells.window_denotes
#print axioms REWB.MaskedTraversalAggregate.Cells.queryWindow_physical
#print axioms REWB.MaskedTraversalAggregate.Cells.Current.bank_geometry
#print axioms REWB.MaskedTraversalAggregate.Cells.raw_current_geometry
#print axioms REWB.MaskedTraversalAggregate.Cells.queryWindow_actual_clipping_work
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseCurrent_actual_work
#print axioms REWB.MaskedTraversalAggregate.Cells.parts_mem
#print axioms REWB.MaskedTraversalAggregate.Cells.regionParts_mem
#print axioms REWB.MaskedTraversalAggregate.Cells.plan_lower_le
#print axioms REWB.MaskedTraversalAggregate.Cells.candidate_owner
#print axioms REWB.MaskedTraversalAggregate.Cells.clipped_source_iff
#print axioms REWB.MaskedTraversalAggregate.Cells.windowParts_marks
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseMany_sources
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseCurrent_unclipped
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseCurrent_maintained
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseMany_maintained
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseMany_calls
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseMany_work
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseMany_charged
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseMany_fanout_balance
#print axioms REWB.MaskedTraversalAggregate.Reporting.query_aggregate_work
#print axioms REWB.MaskedTraversalAggregate.Reporting.ask_work
#print axioms REWB.MaskedTraversalAggregate.Reporting.run_nodup
#print axioms REWB.MaskedTraversalAggregate.Reporting.run_maintained
#print axioms REWB.MaskedTraversalAggregate.Reporting.run_queryWork
#print axioms REWB.MaskedTraversalAggregate.Reporting.ask_correct
#print axioms REWB.MaskedTraversalAggregate.Reporting.run_correct
#print axioms REWB.MaskedTraversalAggregate.Reporting.run_sound
#print axioms REWB.MaskedTraversalAggregate.Reporting.run_calls
#print axioms REWB.MaskedTraversalAggregate.Reporting.run_exhausts
#print axioms REWB.MaskedTraversalAggregate.Reporting.run_charged
#print axioms REWB.MaskedTraversalAggregate.Collect.run_history
#print axioms REWB.MaskedTraversalAggregate.Collect.run_sources
#print axioms REWB.MaskedTraversalAggregate.Collect.run_runs
#print axioms REWB.MaskedTraversalAggregate.Collect.run_maintained
#print axioms REWB.MaskedTraversalAggregate.Collect.run_answers_valid
#print axioms REWB.MaskedTraversalAggregate.Collect.run_count
#print axioms REWB.MaskedTraversalAggregate.Collect.run_read
#print axioms REWB.MaskedTraversalAggregate.Collect.run_added_work
#print axioms REWB.MaskedTraversalAggregate.Collect.run_charged
#print axioms REWB.MaskedTraversalAnswers.pushOne_size
#print axioms REWB.MaskedTraversalAnswers.pushOne_read
#print axioms REWB.MaskedTraversalAnswers.push_size
#print axioms REWB.MaskedTraversalAnswers.push_history
#print axioms REWB.MaskedTraversalAnswers.push_count
#print axioms REWB.MaskedTraversalAnswers.push_work
#print axioms REWB.MaskedTraversalAnswers.push_read
#print axioms REWB.MaskedTraversalAnswers.fromBits_valid
#print axioms REWB.MaskedTraversalAnswers.pushOne_valid
#print axioms REWB.MaskedTraversalAnswers.push_valid
#print axioms REWB.MaskedTraversalAnswers.Valid.count_le
#print axioms REWB.MaskedTraversalInitial.union_size
#print axioms REWB.MaskedTraversalInitial.union_read
#print axioms REWB.MaskedTraversalInitial.start_size
#print axioms REWB.MaskedTraversalInitial.start_read
#print axioms REWB.MaskedTraversalInitial.start_history
#print axioms REWB.MaskedTraversalInitial.handled_sound
#print axioms REWB.MaskedTraversalInitial.start_answers_valid
#print axioms REWB.MaskedTraversalInitial.start_count
#print axioms REWB.MaskedTraversalInitial.start_valid
#print axioms REWB.MaskedTraversalInitial.start_n
#print axioms REWB.MaskedTraversalInitial.start_modulus
#print axioms REWB.MaskedTraversalInitial.start_runs
#print axioms REWB.MaskedTraversalInitial.start_current
#print axioms REWB.MaskedTraversalInitial.start_member
#print axioms REWB.MaskedTraversalInitial.start_partition
#print axioms REWB.MaskedTraversalInitial.periodic_work
#print axioms REWB.MaskedTraversalInitial.start_history_count
#print axioms REWB.MaskedTraversalInitial.start_source_work
#print axioms REWB.MaskedTraversalInitial.start_accountedWork
#print axioms REWB.MaskedTraversalAnswers.Regression.seed_history
#print axioms REWB.MaskedTraversalAnswers.Regression.added_bits
#print axioms REWB.MaskedTraversalAnswers.Regression.added_history
#print axioms REWB.MaskedTraversalAnswers.Regression.added_count
#print axioms REWB.MaskedTraversalAnswers.Regression.added_work
#print axioms REWB.MaskedTraversalAnswers.Regression.persistent_seed
#print axioms REWB.MaskedTraversalAnswers.Regression.no_false_growth
#print axioms REWB.MaskedTraversalAnswers.Regression.initial_terminal_empty
#print axioms REWB.MaskedTraversalAnswers.Regression.initial_missing_target
#print axioms REWB.MaskedTraversalAggregate.Cells.locate_absent
#print axioms REWB.MaskedTraversalAggregate.Cells.erased_absent_compile
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseMany_absent_compile
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseMany_other
#print axioms REWB.MaskedTraversalAggregate.Cells.Coherent.transport_erases
#print axioms REWB.MaskedTraversalAggregate.Cells.LinkedEntries.transport_runs
#print axioms REWB.MaskedTraversalAggregate.Cells.Maintained.transport_erases
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseMany_disjoint_slots
#print axioms REWB.MaskedTraversalAggregate.Cells.eraseMany_disjoint_maintained
#print axioms REWB.MaskedTraversalRepairCoherence.compile_eraseMany_supported
#print axioms REWB.MaskedTraversalRepairCoherence.incoming_slots
#print axioms REWB.MaskedTraversalRepairCoherence.Pending.transfer
#print axioms REWB.MaskedTraversalRepairCoherence.Pending.transfer_erases
#print axioms REWB.MaskedTraversalRepairCoherence.retained_slots
#print axioms REWB.MaskedTraversalRepairCoherence.apply_disjoint_slots
#print axioms REWB.MaskedTraversalRepairCoherence.apply_disjoint_pending
#print axioms REWB.MaskedTraversalRepairCoherence.apply_disjoint_anchors
#print axioms REWB.MaskedTraversalComplete.partStep_code
#print axioms REWB.MaskedTraversalComplete.pass_step
#print axioms REWB.MaskedTraversalComplete.chain_single
#print axioms REWB.MaskedTraversalComplete.chain_append
#print axioms REWB.MaskedTraversalComplete.waiting_chain
#print axioms REWB.MaskedTraversalComplete.jump_step
#print axioms REWB.MaskedTraversalComplete.source_direct
#print axioms REWB.MaskedTraversalComplete.target_direct
#print axioms REWB.MaskedTraversalComplete.admitted_false
#print axioms REWB.MaskedTraversalComplete.finishMode_false
#print axioms REWB.MaskedTraversalComplete.pass_chain
#print axioms REWB.MaskedTraversalComplete.continuous_split
#print axioms REWB.MaskedTraversalComplete.enabled_append_right
#print axioms REWB.MaskedTraversalComplete.admitted_jump
#print axioms REWB.MaskedTraversalComplete.jump_after
#print axioms REWB.MaskedTraversalComplete.target_entry
#print axioms REWB.MaskedTraversalComplete.final_mode
#print axioms REWB.MaskedTraversalComplete.finish_pass
#print axioms REWB.MaskedTraversalComplete.arrive_target
#print axioms REWB.MaskedTraversalComplete.two_jumps
#print axioms REWB.MaskedTraversalComplete.parts_firsts
#print axioms REWB.MaskedTraversalComplete.regionParts_keys
#print axioms REWB.MaskedTraversalComplete.entryKeys_mem
#print axioms REWB.MaskedTraversalComplete.entryKeys_ordered
#print axioms REWB.MaskedTraversalComplete.regionParts_firsts
#print axioms REWB.MaskedTraversalComplete.adjacent_specs
#print axioms REWB.MaskedTraversalComplete.last_spec
#print axioms REWB.MaskedTraversalComplete.region_actual
#print axioms REWB.MaskedTraversalComplete.Actual.geometry
#print axioms REWB.MaskedTraversalComplete.Actual.incoming
#print axioms REWB.MaskedTraversalComplete.Actual.safe
#print axioms REWB.MaskedTraversalComplete.Actual.compatible
#print axioms REWB.MaskedTraversalComplete.Actual.terminal
#print axioms REWB.MaskedTraversalComplete.interfaces
#print axioms REWB.MaskedTraversalComplete.actual_interfaces
#print axioms REWB.MaskedTraversalComplete.ordered_split
#print axioms REWB.MaskedTraversalComplete.owner_order
#print axioms REWB.MaskedTraversalComplete.actual_member
#print axioms REWB.MaskedTraversalComplete.window_keys
#print axioms REWB.MaskedTraversalComplete.window_actual
#print axioms REWB.MaskedTraversalComplete.window_complete
#print axioms REWB.MaskedTraversalComplete.tracked_weaken
#print axioms REWB.MaskedTraversalComplete.tracked_read
#print axioms REWB.MaskedTraversalComplete.tracked_jump
#print axioms REWB.MaskedTraversalComplete.tracked_direct
#print axioms REWB.MaskedTraversalComplete.tracked_cursor
#print axioms REWB.MaskedTraversalComplete.tracked_chain
#print axioms REWB.MaskedTraversalComplete.tracked_final
#print axioms REWB.MaskedTraversalComplete.Actual.owner
#print axioms REWB.MaskedTraversalComplete.window_sound
#print axioms REWB.MaskedTraversalComplete.window_path_iff
#print axioms REWB.MaskedTraversalComplete.class_slice
#print axioms REWB.MaskedTraversalComplete.queryWindow_iff
#print axioms REWB.MaskedTraversalComplete.Regression.actual_descriptors
#print axioms REWB.MaskedTraversalComplete.Regression.actual_enabled_incoming
#print axioms REWB.MaskedTraversalComplete.Regression.overshoot_skips_first_target
#print axioms REWB.MaskedTraversalComplete.Regression.actual_distinct_owners
#print axioms REWB.MaskedTraversalComplete.Regression.immediate_dense_target_path
#print axioms REWB.MaskedTraversalComplete.Regression.empty_path_rejects
#print axioms REWB.MaskedTraversalPeriodicCoverage.same_owner_run
#print axioms REWB.MaskedTraversalPeriodicCoverage.class_copy
#print axioms REWB.MaskedTraversalPeriodicCoverage.same_owner_witness
#print axioms REWB.MaskedTraversalPeriodicCoverage.same_owner_covered
#print axioms REWB.MaskedTraversalPeriodicCoverage.same_owner_hit
#print axioms REWB.MaskedTraversalPeriodicCoverage.member_of_copy
#print axioms REWB.MaskedTraversalPeriodicCoverage.cut_partition
#print axioms REWB.MaskedTraversalPeriodicCoverage.remaining_distinct
#print axioms REWB.MaskedTraversalPeriodicCoverage.original_length
#print axioms REWB.MaskedTraversalPeriodicCoverage.original_partition
#print axioms REWB.MaskedTraversalPeriodicCoverage.Regression.actual_invariant
#print axioms REWB.MaskedTraversalPeriodicCoverage.Regression.actual_complete
#print axioms REWB.MaskedTraversalPeriodicCoverage.Regression.actual_same_owner
#print axioms REWB.MaskedTraversalPeriodicCoverage.Regression.enumerated_pair
#print axioms REWB.MaskedTraversalPeriodicCoverage.Regression.actual_periodic_hit
#print axioms REWB.MaskedTraversalPeriodicCoverage.Regression.original_cut_partition
#print axioms REWB.MaskedTraversalRepairCoherence.apply_sources
#print axioms REWB.MaskedTraversalRepairCoherence.apply_represents
#print axioms REWB.MaskedTraversalRepairCoherence.compile_present
#print axioms REWB.MaskedTraversalRepairCoherence.reset_runBacked
#print axioms REWB.MaskedTraversalRepairCoherence.refreshLoop_selected
#print axioms REWB.MaskedTraversalRepairCoherence.resetBanks_present
#print axioms REWB.MaskedTraversalRepairCoherence.resetBanks_raw
#print axioms REWB.MaskedTraversalRepairCoherence.model_get
#print axioms REWB.MaskedTraversalRepairCoherence.apply_selected
#print axioms REWB.MaskedTraversalRepairCoherence.apply_coherent
#print axioms REWB.MaskedTraversalRepairCoherence.apply_linked
#print axioms REWB.MaskedTraversalRepairCoherence.apply_complete
#print axioms REWB.MaskedTraversalRepairCoherence.apply_anchors
#print axioms REWB.MaskedTraversalRepairCoherence.raw_geometry
#print axioms REWB.MaskedTraversalRepairCoherence.apply_work
#print axioms REWB.MaskedTraversalRepairTransport.old_context_unmarked
#print axioms REWB.MaskedTraversalRepairTransport.repartition
#print axioms REWB.MaskedTraversalRepairTransport.add_pending
#print axioms REWB.MaskedTraversalRepairTransport.merge_pending
#print axioms REWB.MaskedTraversalRepairCoherence.apply_unclipped
#print axioms REWB.MaskedTraversalRepairCoherence.Snapshot.runBacked
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_reset_selected
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_reset_present
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_reset_raw
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_apply_selected
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_apply_present
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_apply_maintained
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_apply_anchors
#print axioms REWB.MaskedTraversalRepairCoherence.compile_snapshot_work
#print axioms REWB.MaskedTraversalRepairCoherence.reset_snapshot_work
#print axioms REWB.MaskedTraversalRepairCoherence.apply_snapshot_work
#print axioms REWB.MaskedTraversalRepairTransport.reindexed_get
#print axioms REWB.MaskedTraversalRepairTransport.shortened_entry
#print axioms REWB.MaskedTraversalRepairTransport.crossing_same_pending
#print axioms REWB.MaskedTraversalRepairTransport.crossing_pending
#print axioms REWB.MaskedTraversalRepairTransport.reindexed_unclipped
#print axioms REWB.MaskedTraversalExecute.band_count
#print axioms REWB.MaskedTraversalExecute.band_actions
#print axioms REWB.MaskedTraversalExecute.bands_count
#print axioms REWB.MaskedTraversalExecute.bands_actions
#print axioms REWB.MaskedTraversalExecute.edge_equal
#print axioms REWB.MaskedTraversalExecute.supported_mono
#print axioms REWB.MaskedTraversalExecute.coherent_supported
#print axioms REWB.MaskedTraversalExecute.supported_reindexed
#print axioms REWB.MaskedTraversalExecute.dirty_empty
#print axioms REWB.MaskedTraversalExecute.change_supported
#print axioms REWB.MaskedTraversalExecute.marked_supported
#print axioms REWB.MaskedTraversalExecute.add_supported
#print axioms REWB.MaskedTraversalExecute.crossing_supported
#print axioms REWB.MaskedTraversalPositiveCoverage.suffix_band_valid
#print axioms REWB.MaskedTraversalPositiveCoverage.representative_mem
#print axioms REWB.MaskedTraversalPositiveCoverage.band_metadata
#print axioms REWB.MaskedTraversalPositiveCoverage.Metadata.invariant
#print axioms REWB.MaskedTraversalPositiveCoverage.current_unhandled
#print axioms REWB.MaskedTraversalPositiveCoverage.current_positive
#print axioms REWB.MaskedTraversalPositiveCoverage.current_not_periodic
#print axioms REWB.MaskedTraversalPositiveCoverage.surviving_band
#print axioms REWB.MaskedTraversalPositiveCoverage.band_good_sound
#print axioms REWB.MaskedTraversalPositiveCoverage.initial_partition
#print axioms REWB.MaskedTraversalPositiveCoverage.Regression.cross_initial_empty
#print axioms REWB.MaskedTraversalPositiveCoverage.Regression.cross_original
#print axioms REWB.MaskedTraversalPositiveCoverage.Regression.actual_remaining_band
#print axioms REWB.MaskedTraversalPositiveCoverage.Regression.actual_initial_partition
#print axioms REWB.MaskedTraversalPositiveCoverage.Regression.terminal_empty_reported
#print axioms REWB.MaskedTraversalPositiveCoverage.Regression.terminal_has_no_positive_band
#print axioms REWB.MaskedTraversalPositiveCoverage.currentBit_antitone
#print axioms REWB.MaskedTraversalPositiveCoverage.bandGood_antitone
#print axioms REWB.MaskedTraversalPositiveCoverage.BandExhausted.mono
#print axioms REWB.MaskedTraversalPositiveCoverage.Exhausted.mono
#print axioms REWB.MaskedTraversalPositiveCoverage.exhausted_node
#print axioms REWB.MaskedTraversalPositiveCoverage.collect_history_includes
#print axioms REWB.MaskedTraversalPositiveCoverage.collect_exhausts
#print axioms REWB.MaskedTraversalPositiveCoverage.collect_preserves
#print axioms REWB.MaskedTraversalPositiveCoverage.exhausted_no_live
#print axioms REWB.MaskedTraversalPositiveCoverage.answers_correct
