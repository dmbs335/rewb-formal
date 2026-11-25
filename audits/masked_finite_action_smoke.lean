import REWB.MaskedFiniteActionRegression

/-! Run after `lake build REWB.MaskedFiniteActionRegression` with:
    `lake env lean --run audits/masked_finite_action_smoke.lean`. -/

open REWB.MaskedFiniteAction
open REWB.MaskedFiniteAction.Regression

def main : IO Unit := do
  IO.println s!"finite universe: states=3, maps={Maps.count 3}"
  IO.println s!"action tree: build={initial.2}, firstReindex={first.2}, secondReindex={second.2}, replace={replaced.2}, prefix={prefixResult.2}"
  let a := (Tree.cache replaced.1).view ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  let b := (Tree.cache replaced.1).view ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  IO.println s!"fresh replacement under old noninjective tags: index0={a}, index2={b}"
  let mut intervalChecks := 0
  for lo in List.range 8 do
    for hi in List.range 8 do
      let result := Tree.queryRange matrixReplaced.1 lo hi
      let expected := View.product (REWB.Spec.slice (Tree.leaves matrixReplaced.1) lo hi)
      unless result.2≤2*3*Tree.queryBudget 3 2 do
        throw (IO.userError "interval query counter bound exceeded")
      for i in List.finRange 3 do
        for p in List.finRange 2 do
          for q in List.finRange 2 do
            unless result.1.view i p q=expected i p q do
              throw (IO.userError "noncommuting lazy interval query mismatch")
            intervalChecks := intervalChecks+1
  IO.println s!"ordered interval products: entryChecks={intervalChecks}, mismatches=0"

#print axioms View.reindex_product
#print axioms Counted.mul_steps
#print axioms Tree.reindex_leaves
#print axioms Tree.reindex_steps
#print axioms Tree.replace_leaves
#print axioms Tree.replace_steps
#print axioms Tree.queryPrefix_correct
#print axioms Tree.querySuffix_correct
#print axioms Tree.queryRange_correct
#print axioms Tree.queryRange_steps
#print axioms Maps.vectors_complete
#print axioms Maps.count_eq
#print axioms Maps.decode_encode
#print axioms Maps.rightAction_comp
#print axioms Maps.localAnchor_shortening
#print axioms Regression.execution
#print axioms Regression.interval_order
