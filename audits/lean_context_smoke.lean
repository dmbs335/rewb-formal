import REWB.BoundaryContexts

/-! Exercise the actual shared context constructor on a long text.
The three-state DFA adds 1 on symbol 0 and 2 on symbol 1 modulo 3.
For an even-length alternating word, prefix states and all suffix-row
entries have simple independent arithmetic reference values.
Run with `lake env lean --run audits/lean_context_smoke.lean`. -/
open REWB

private def bit (n : Nat) : Fin 2 := ⟨n%2,Nat.mod_lt n (by decide)⟩
private def state (n : Nat) : Fin 3 := ⟨n%3,Nat.mod_lt n (by decide)⟩

private def cyclic : DFA (Fin 2) :=
  ⟨3,state 0,fun q c=>state (q.val+c.val+1),fun q=>q.val==0⟩

private def pattern : SevenDFA (Fin 2) :=
  ⟨cyclic,cyclic,cyclic,cyclic,cyclic,cyclic,cyclic⟩

def main : IO Unit := do
  let n:=100000
  let w:=(List.range n).map bit
  let result:=BoundaryContexts.build pattern w
  if result.1.prefixes.size != n+1 || result.1.suffixes.size != n+1 then
    throw (IO.userError "shared context array sizes differ from n+1")
  if result.2 != (n+1)*(1+pattern.H.stateCount) then
    throw (IO.userError s!"shared context entry count differs: {result.2}")
  for i in List.range (n+1) do
    let prefixState:=BoundaryContexts.prefixAt pattern result.1 i
    if prefixState.val != i%2 then
      throw (IO.userError s!"prefix state differs at boundary {i}: {prefixState.val}")
    let row:=BoundaryContexts.suffixAt pattern result.1 i
    if row.size != pattern.H.stateCount then
      throw (IO.userError s!"suffix row size differs at boundary {i}")
    for j in List.range 3 do
      let got:=DFACut.read pattern.H row (state j)
      let expected:=(j+3-i%2)%3
      if got.val != expected then
        throw (IO.userError s!"suffix state differs at boundary {i}, state {j}: {got.val}")
  IO.println s!"context text symbols={n}; prefix boundaries={result.1.prefixes.size}; suffix rows={result.1.suffixes.size}"
  IO.println s!"all prefix/suffix states verified; measured entries={result.2}; stack-safe shared construction passed"
