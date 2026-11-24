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
