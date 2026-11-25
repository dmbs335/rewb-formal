import REWB.MaskedEmptyRegression

open REWB REWB.MaskedEmpty REWB.MaskedEmpty.Regression
open REWB.MaskedProgression (readMask)

def binaryWord (n code : Nat) : Word Nat :=
  (List.range n).map (fun i=>(code/2^i)%2)

def mask (n code : Nat) : Array Bool :=
  ((List.range n).map (fun i=>decide ((code/2^i)%2=1))).toArray

def brute (B C E : DFA Nat) (w : Word Nat) (source target : Array Bool) (s : Nat) : Bool :=
  (readMask source s && B.final B.initial) &&
    (List.range (w.length+1)).any (fun j=>
      decide (s≤j) && readMask target j &&
        C.final (C.run C.initial (Spec.slice w s j)) &&
        E.final (E.run E.initial (Spec.slice w j w.length)))

def check (B C E : DFA Nat) (w : Word Nat) (source target : Array Bool) : IO Nat := do
  let out:=solve B C E w source target
  unless out.answers.size=w.length+1 &&
      out.work=(12*C.stateCount+6*E.stateCount+64)*(w.length+1) do
    throw (IO.userError "empty-capture size or linear work ledger mismatch")
  for s in [0:w.length+3] do
    unless readMask out.answers s == brute B C E w source target s do
      throw (IO.userError s!"empty-capture mismatch word={w}, source={source}, target={target}, s={s}")
  return w.length+3

def main : IO Unit := do
  let begin ← IO.monoMsNow
  let dfas:=[allWords,epsilon,nonempty,endsOne]
  let mut scans:=0
  let mut bits:=0
  for n in [0:5] do
    for code in [0:2^n] do
      let w:=binaryWord n code
      for targetCode in [0:2^(n+1)] do
        let target:=mask (n+1) targetCode
        for source in [Array.replicate (n+1) true,mask (n+1) (targetCode+3),#[]] do
          for B in [epsilon,nonempty] do
            for C in dfas do
              for E in dfas do
                bits:=bits+(←check B C E w source target)
                scans:=scans+1
  for n in [0:32] do
    let w:=(List.range n).map (fun i=>(i*17+3)%2)
    for C in dfas do
      for E in dfas do
        bits:=bits+(←check epsilon C E w (mask (n/2) 173) (mask (n/3) 213))
        scans:=scans+1
  let finish ← IO.monoMsNow
  IO.println s!"empty-capture scans={scans}, brute boundary checks={bits}, epsilon/positive-B, arbitrary/short masks and noninjective transitions passed ({finish-begin} ms)"
  let n:=100000
  let w:=(List.range n).map (fun i=>i%2)
  let source:=Array.replicate (n+1) true
  let target:=(Array.replicate (n+1) false).set! n true
  let out:=solve epsilon endsOne epsilon w source target
  unless out.answers.size=n+1 && out.work=100*(n+1) &&
      out.answers[n]?.getD true=false &&
      (out.answers.extract 0 n).all id do
    throw (IO.userError "deep empty-capture scan failed")
  IO.println s!"stack-safe backwards scan n={n}, answers={out.answers.size}, work={out.work}; terminal boundary retained, no mismatches"
