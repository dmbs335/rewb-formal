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
