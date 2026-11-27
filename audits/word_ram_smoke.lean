import REWB.WordRAMArithmeticWords
import REWB.WordRAMAppend
import REWB.WordRAMLCMFoldWords

/-! Execute the independent instruction interpreter, checking outputs,
exact halting times, frame preservation and finite-word overflow traps.
These finite probes supplement the universal kernel proofs. -/
namespace REWB.WordRAM.Audit
open Arithmetic ListHeap Lists

def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def readList (heap : Nat → Nat) : Nat → Nat → Option (List Nat)
  | 0, p => if p = 0 then some [] else none
  | fuel+1, p =>
    if p = 0 then some [] else
      (readList heap fuel (heap (p+1))).map (heap p :: ·)

def checkArithmetic (m n : Nat) : IO Unit := do
  let capacity := (max m n)*(max m n)+(max m n)+10
  match runWordSteps capacity gcdProgram (gcdSteps m n) (gcdInput m n) with
  | none => throw (IO.userError s!"GCD trapped: {m}, {n}")
  | some out =>
    check (out.halted && out.regs 1 = Nat.gcd m n) "GCD output/halting"
    check ((wordStep capacity gcdProgram out).isNone) "GCD continued after halt"
  match runWordSteps capacity lcmProgram (lcmSteps m n) (lcmInput m n) with
  | none => throw (IO.userError s!"LCM trapped: {m}, {n}")
  | some out =>
    check (out.halted && out.regs 0 = Nat.lcm m n) "LCM output/halting"
    check (out.regs 3 = m && out.regs 4 = n) "LCM saved operands"
    check ((wordStep capacity lcmProgram out).isNone) "LCM continued after halt"
  match runWordSteps capacity lcmProgram (lcmSteps m n-1) (lcmInput m n) with
  | none => throw (IO.userError "LCM failed before final halt")
  | some out => check (!out.halted) "LCM instruction count overestimated"
  check ((runWordSteps capacity lcmProgram (lcmSteps m n+1) (lcmInput m n)).isNone)
    "LCM accepted an extra instruction after halt"

def listInput (xs ys : List Nat) : State :=
  let first := copyReverse (fun _ => 0) 1 0 xs.reverse
  let second := copyReverse first.heap first.frontier 0 ys.reverse
  { regs := fun r => if r = 0 then first.pointer else if r = 1 then second.pointer
      else if r = 2 then second.frontier else 0
    heap := second.heap }

def checkReverse (xs ys : List Nat) : IO Unit := do
  let initial := listInput xs ys
  let capacity := 1024
  let steps := 11*xs.length+4
  match runWordSteps capacity reverseProgram steps initial with
  | none => throw (IO.userError "reverse trapped")
  | some out =>
    check (out.halted) "reverse did not halt at exact count"
    check (readList out.heap (xs.length+ys.length+1) (out.regs 1) = some (xs.reverse++ys))
      "reverse linked-list payload/order"
    check (out.regs 2 = initial.regs 2+2*xs.length) "reverse allocation count"
    for a in List.range (initial.regs 2) do
      check (out.heap a = initial.heap a) "reverse changed an existing cell"
  match runWordSteps capacity reverseProgram (steps-1) initial with
  | none => throw (IO.userError "reverse failed before final halt")
  | some out => check (!out.halted) "reverse instruction count overestimated"
  check ((runWordSteps capacity reverseProgram (steps+1) initial).isNone)
    "reverse accepted an extra instruction after halt"

def checkAppend (xs ys : List Nat) : IO Unit := do
  let initial := listInput xs ys
  let capacity := 1024
  let steps := 22*xs.length+9
  match runWordSteps capacity appendProgram steps initial with
  | none => throw (IO.userError "append trapped")
  | some out =>
    check (out.halted) "append did not halt at exact count"
    check (readList out.heap (xs.length+ys.length+1) (out.regs 1) = some (xs++ys))
      "append linked-list payload/order"
    check (out.regs 2 = initial.regs 2+4*xs.length) "append allocation count"
    for a in List.range (initial.regs 2) do
      check (out.heap a = initial.heap a) "append changed an existing cell"
  match runWordSteps capacity appendProgram (steps-1) initial with
  | none => throw (IO.userError "append failed before final halt")
  | some out => check (!out.halted) "append instruction count overestimated"
  check ((runWordSteps capacity appendProgram (steps+1) initial).isNone)
    "append accepted an extra instruction after halt"

def checkFold (xs : List Nat) : IO Unit := do
  let cells := copyReverse (fun _ => 0) 1 0 xs.reverse
  let initial := LCMFold.input cells.pointer cells.heap
  let capacity := 1000000
  let steps := LCMFold.steps xs
  match runWordSteps capacity LCMFold.program steps initial with
  | none => throw (IO.userError "connected LCM fold trapped")
  | some out =>
    check (out.halted && out.regs 5 = 0) "LCM fold null termination"
    check (out.regs 8 = xs.foldl Nat.lcm 1) "LCM fold result"
    for a in List.range (cells.frontier+10) do
      check (out.heap a = cells.heap a) "LCM fold modified input memory"
  match runWordSteps capacity LCMFold.program (steps-1) initial with
  | none => throw (IO.userError "LCM fold failed before final halt")
  | some out => check (!out.halted) "LCM fold instruction count overestimated"
  check ((runWordSteps capacity LCMFold.program (steps+1) initial).isNone)
    "LCM fold accepted an extra instruction after halt"

def main : IO Unit := do
  for m in List.range 21 do
    for n in List.range 21 do checkArithmetic m n
  for n in List.range 13 do
    for ys in [[],[0],[5,0,9]] do
      checkReverse ((List.range n).map (fun i => (7*i)%23)) ys
      checkAppend ((List.range n).map (fun i => (7*i)%23)) ys
  check ((runWordSteps 32 lcmProgram (lcmSteps 7 8) (lcmInput 7 8)).isNone)
    "LCM failed to trap on its product overflow"
  check ((runWordSteps 9 lcmProgram (lcmSteps 0 0) (lcmInput 0 0)).isNone)
    "LCM failed to trap on an instruction address overflow"
  let s := listInput (List.range 6) []
  check ((runWordSteps (s.regs 2+12) reverseProgram 70 s).isNone)
    "reverse failed to trap on its allocation frontier overflow"
  let longSource := listInput (List.range 10) []
  check ((runWordSteps (longSource.regs 2+40) appendProgram 229 longSource).isNone)
    "append failed to trap on its allocation frontier overflow"
  for xs in [[],[0],[1],[6,10,15],[2,3,4,6,12],[6,0,9],List.replicate 20 6] do
    checkFold xs
  IO.println "word-RAM: arithmetic pairs=441, reverse fixtures=39, append fixtures=39, connected LCM folds=7, overflow traps=4, exact-step/frame/output mismatches=0"

end REWB.WordRAM.Audit

def main : IO Unit := REWB.WordRAM.Audit.main
