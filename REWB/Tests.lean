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
