import REWB.BoundaryBorderRegression

open REWB REWB.BoundaryBorder REWB.Periodic REWB.LCEIndex

def binary (n code : Nat) : Array (Fin 2) :=
  ((List.range n).map fun i=>(⟨(code/2^i)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2)).toArray

def selected (choice : Choice) (p : Nat) : Bool :=
  match choice with
  | .empty => false
  | .point x => decide (p=x)
  | .progression first step lo hi => decide (Member first step lo hi p)

def brute (text : Array (Fin 2)) (first q lo hi a j p : Nat) : Bool :=
  let f:=fun i=>text[i]?.getD 0
  decide (Member first q lo hi p ∧ p≤a ∧ j+(a-p)≤text.size) &&
    decide (segment f p (a-p)=segment f j (a-p))

def main : IO Unit := do
  let begin ← IO.monoMsNow
  let mut calls:=0
  let mut points:=0
  let mut bands:=0
  let mut empties:=0
  let mut checks:=0
  for n in [0:7] do
    for code in [0:2^n] do
      let text:=binary n code
      let f:=fun i=>text[i]?.getD (0 : Fin 2)
      let index:=prepare f n
      for first in [0:n] do
        for q in [1:n-first+1] do
          let right:=first+(extend index n first q).extent
          let hi:=right-q
          for j in [0:n-q+1] do
            if segment f first q==segment f j q then
              for a in [0:n+1] do
                for lo in [first,min hi (first+q)] do
                  let out:=select index n first q lo hi a j
                  unless out.work≤39*(n.log2+1)+34 do
                    throw (IO.userError "border selector exceeded the three-LCE work bound")
                  calls:=calls+1
                  match out.choice with
                  | .empty => empties:=empties+1
                  | .point _ => points:=points+1
                  | .progression _ _ _ _ => bands:=bands+1
                  for p in [0:n+2] do
                    unless selected out.choice p==brute text first q lo hi a j p do
                      throw (IO.userError s!"border mismatch n={n}, code={code}, first={first}, q={q}, window={lo}:{hi}, a={a}, j={j}, p={p}, choice={repr out.choice}")
                    checks:=checks+1
  let finish ← IO.monoMsNow
  IO.println s!"border component calls={calls}, physical membership checks={checks}, AP bands={bands}, exceptional points={points}, empty exceptions={empties}, mismatches=0 ({finish-begin} ms)"
  let n:=4096
  let text:=binary n 0
  let f:=fun i=>text[i]?.getD (0 : Fin 2)
  let index:=prepare f n
  for q in [1,2,1024,2048] do
    let out:=select index n 0 q 0 (n-q) 2048 2048
    unless out.work≤39*(n.log2+1)+34 do
      throw (IO.userError "large-period selector work depends on the period magnitude")
    for p in [0:2050] do
      unless selected out.choice p==brute text 0 q 0 (n-q) 2048 2048 p do
        throw (IO.userError "large-period selector mismatch")
    IO.println s!"border n={n}, q={q}, work={out.work}, choice={repr out.choice}; no period/residue scan in selector"
