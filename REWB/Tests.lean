import REWB

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
