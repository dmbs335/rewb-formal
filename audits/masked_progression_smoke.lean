import REWB.MaskedProgressionRegression

/-! Run with `lake env lean --run audits/masked_progression_smoke.lean`.
    Test enumeration belongs only to this audit. Every query uses a
    prebuilt array, including on nonperiodic arbitrary masks. -/

open REWB.MaskedProgression
open REWB.MaskedProgression.Regression

def smallMask (seed : Nat) : Array Bool :=
  Array.ofFn fun i : Fin 4 => decide ((seed / 2^i.val)%2=1)

def main : IO Unit := do
  IO.println s!"stepped array: {exampleBuild.counts}, slots={exampleBuild.slots}, arithmetic={exampleBuild.arithmetic}"
  IO.println s!"AP first={reprStr exampleQuery}, subtract={reprStr subtractQuery}, absent={reprStr unmarkedQuery}"
  let masks := (List.range 16).map smallMask ++ [arbitraryMask]
  let mut queries := 0
  let mut builds := 0
  let mut hits := 0
  let mut maxSlots := 0
  let mut maxArithmetic := 0
  for mask in masks do
    for base in List.range 6 do
      for len in List.range 7 do
        for q0 in List.range 3 do
          for K0 in List.range 3 do
            let q := q0+1
            let K := K0+1
            let index := build mask base len (K*q)
            builds := builds+1
            unless index.counts.size=len && index.slots=3*len+(len-K*q) &&
                index.arithmetic=8*len+(len-K*q) do
              throw (IO.userError s!"build counter mismatch: base={base}, len={len}, q={q}, K={K}")
            for s in List.range 7 do
              for lo in List.range 5 do
                for hi in List.range 5 do
                  for r in List.range (K+1) do
                    let result := ap index.counts base q K s lo hi r
                    let expected := direct mask base len q K s lo hi r
                    unless result.answer=expected do
                      throw (IO.userError s!"AP mismatch: mask={mask}, base={base}, len={len}, q={q}, K={K}, s={s}, lo={lo}, hi={hi}, r={r}, got={result.answer}, expected={expected}")
                    unless result.slots≤2 && result.arithmetic≤37 do
                      throw (IO.userError "query counter bound exceeded")
                    queries := queries+1
                    if result.answer then hits := hits+1
                    maxSlots := max maxSlots result.slots
                    maxArithmetic := max maxArithmetic result.arithmetic
  IO.println s!"direct-mask regression: masks={masks.length}, builds={builds}, queries={queries}, hits={hits}, mismatches=0"
  IO.println s!"query maxima: arraySlots={maxSlots}, scalarArithmetic={maxArithmetic}"

#print axioms build_correct
#print axioms build_slots_exact
#print axioms build_arithmetic_exact
#print axioms grid_build_correct
#print axioms ap_build_correct
#print axioms ap_slots
#print axioms ap_arithmetic
#print axioms Regression.ap_eq_direct
#print axioms Regression.example_counts
#print axioms Regression.endpoint_and_empty_queries
