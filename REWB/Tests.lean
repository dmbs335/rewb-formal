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
  exact .seq (.starCons (.capture (.atom allWords [7] (by decide)))
    (.starCons (.capture (.atom allWords [1] (by decide))) (.starNil _))) .reference

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
