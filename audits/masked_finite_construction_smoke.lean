import REWB.MaskedFiniteConstruction

open REWB REWB.MaskedCluster REWB.MaskedFiniteConstruction

def checkUniverse (c e : Nat) : IO (Nat×Nat) := do
  let prepared:=MaskedFiniteConstruction.prepare c e
  if prepared.1.values != (ReplayMaps.prepare c e).values then
    throw (IO.userError s!"catalog mismatch c={c} e={e}")
  if prepared.2>MaskedFiniteConstruction.prepareBudget c e then
    throw (IO.userError s!"catalog work c={c} e={e}")
  let mut actions:=0
  let mut cells:=0
  for z in (ReplayMaps.enumeration c e).elems do
    let actual:=MaskedFiniteConstruction.bankAction z
    if actual.1 != MaskedCluster.bankAction z then
      throw (IO.userError s!"action mismatch c={c} e={e}")
    if actual.2>MaskedFiniteConstruction.bankActionBudget c e then
      throw (IO.userError s!"action work c={c} e={e}")
    actions:=actions+1
    cells:=cells+2*ReplayMaps.count c e
  return (actions,cells)

def main : IO Unit := do
  let started←IO.monoMsNow
  let mut actions:=0
  let mut cells:=0
  for c in [0,1,2] do
    for e in [0,1,2] do
      let out←checkUniverse c e
      actions:=actions+out.1
      cells:=cells+out.2
  let finished←IO.monoMsNow
  IO.println s!"masked finite construction: universes=9 actions={actions} cells={cells} mismatches=0 elapsed_ms={finished-started}"

#print axioms REWB.MaskedFiniteConstruction.vectors_value
#print axioms REWB.MaskedFiniteConstruction.enumeration_value
#print axioms REWB.MaskedFiniteConstruction.lookup_value
#print axioms REWB.MaskedFiniteConstruction.lookup_work
#print axioms REWB.MaskedFiniteConstruction.index_value
#print axioms REWB.MaskedFiniteConstruction.index_work
#print axioms REWB.MaskedFiniteConstruction.decode_value
#print axioms REWB.MaskedFiniteConstruction.decode_work
#print axioms REWB.MaskedFiniteConstruction.encode_value
#print axioms REWB.MaskedFiniteConstruction.encode_work
#print axioms REWB.MaskedFiniteConstruction.rightAction_value
#print axioms REWB.MaskedFiniteConstruction.rightAction_work
#print axioms REWB.MaskedFiniteConstruction.bankAction_value
#print axioms REWB.MaskedFiniteConstruction.bankAction_work
#print axioms REWB.MaskedFiniteConstruction.prepare_value
#print axioms REWB.MaskedFiniteConstruction.prepare_work
#print axioms REWB.MaskedFiniteConstruction.prepare_fixed
#print axioms REWB.MaskedFiniteConstruction.bankAction_fixed
