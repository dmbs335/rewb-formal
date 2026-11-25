import REWB.MaskedAllStartFullCostRowsRegression

open REWB
namespace FullCostRowsSmoke

def all : DFA (Fin 1) :=
  ⟨1,⟨0,by decide⟩,(fun _ _=>⟨0,by decide⟩),(fun _=>true)⟩

def checkTable (n : Nat) : IO Nat := do
  let make:=fun i : Fin n=>((2*i.val+1,7+i.val),11+i.val)
  let actual:=MaskedAllStart.FullCost.Table.build make
  let old:=BoundaryRange.Table.build fun i=>(make i).1
  let expectedFull:=(List.range n).foldl (fun total i=>total+(11+i+3)) 1+10*n+5
  if actual.1.work != old.work || actual.2 != expectedFull then
    throw (IO.userError s!"table ledger mismatch n={n}")
  for i in List.finRange n do
    if BoundaryRange.Table.get actual.1 i != 2*i.val+1 then
      throw (IO.userError s!"table payload mismatch n={n} i={i.val}")
  return n+2

def checkRow (text : Array (Fin 1)) (source target expected : Array Bool) : IO Nat := do
  let actual:=MaskedAllStart.FullCost.Rows.row all all all text ⟨0,by decide⟩ source target
  let old:=MaskedAllStart.Rows.row all all all text ⟨0,by decide⟩ source target
  if actual.1.bits != expected || actual.1.bits != old.bits ||
      actual.1.work != old.work || actual.1.fixedPatternBuilds != old.fixedPatternBuilds then
    throw (IO.userError s!"row mismatch n={text.size}")
  if actual.2=0 then
    throw (IO.userError s!"row work vanished n={text.size}")
  return expected.size

def checkPrefix : IO Nat := do
  let w : Word (Fin 1):=[⟨0,by decide⟩]
  let actual:=MaskedAllStart.FullCost.Rows.prefixRows all all all w ⟨0,by decide⟩ 1
  let old:=MaskedAllStart.Rows.prefixRows all all all w ⟨0,by decide⟩ 1
  if actual.1.work != old.work || actual.1.fixedPatternBuilds != old.fixedPatternBuilds then
    throw (IO.userError "prefix ledger mismatch")
  for c in List.finRange (BoundaryRange.TableColor.count all) do
    if actual.1.bits.get c != old.bits.get c then
      throw (IO.userError "prefix bitmap mismatch")
  IO.println s!"full-cost prefix n=1 fullWork={actual.2} oldWork={actual.1.work}"
  return BoundaryRange.TableColor.count all

def main : IO Unit := do
  let mut checks:=0
  for n in [0,1,3,17,257] do
    checks:=checks+(←checkTable n)
  IO.println s!"full-cost stored-table checks={checks}: PASS"
  checks:=checks+(←checkRow #[] #[true] #[true] #[true])
  let text : Array (Fin 1):=#[⟨0,by decide⟩]
  checks:=checks+(←checkRow text #[true,true] #[true,true] #[true,true])
  checks:=checks+(←checkRow text #[true,false] #[true,true] #[true,false])
  checks:=checks+(←checkRow text #[true,true] #[false,false] #[false,false])
  checks:=checks+(←checkPrefix)
  IO.println s!"full-cost rows: 4 rows + 1 prefix, totalChecks={checks}, 0 mismatches"

end FullCostRowsSmoke
def main : IO Unit:=FullCostRowsSmoke.main
