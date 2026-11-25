import REWB

/-! Optional interpreted runtime probes. These are separate from the
    kernel proof gate. The P1 probe can be expensive even on short text. -/
open REWB

private def allBits : DFA (Fin 2) :=
  ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>true⟩
private def pattern : SevenDFA (Fin 2) :=
  ⟨allBits,allBits,allBits,allBits,allBits,allBits,allBits⟩

def main (args : List String) : IO Unit := do
  match args.headD "p2" with
  | "p1" =>
    let r:=CountedSmallPeriodP1.solve pattern (fun _=>0) 3 1
    IO.println s!"accepted={r.answer}, modulus={r.modulus}, modulusSteps={r.modulusSteps}, sortSteps={r.sortSteps}"
  | "modulus" =>
    IO.println (ActualModulus.formula (List.replicate 30000 [])).2
    IO.println (ActualModulus.formula [[.dvd 6 (.lit 0),.dvd 6 (.lit 0),.dvd 4 (.lit 0)]]).1
  | _ =>
    let r:=ArrayText.solveWord pattern [0,0,0] 0 1
    IO.println s!"accepted={r.accepted}, projectionSteps={r.projectionSteps}, runComparisons={r.runComparisons}"
