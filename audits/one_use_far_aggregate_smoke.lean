import REWB.OneUseRangeFarAggregateRegression

/-! Compiled-path audit against an independent endpoint scan.  Reference
word scans occur only in this file.  The deep profile checks every query
after one actual linear DP build. -/
open REWB
open REWB.OneUseRange.FarAggregate

def auditAutomata : Array (DFA Bool) := #[
  Regression.any,
  ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>false⟩,
  Regression.lastTrue,
  ⟨2,⟨0,by decide⟩,fun q _=>⟨1-q.val,by omega⟩,fun q=>decide (q.val=0)⟩,
  ⟨2,⟨1,by decide⟩,fun _ c=>if c then ⟨1,by decide⟩ else ⟨0,by decide⟩,
    fun q=>decide (q.val=0)⟩,
  ⟨2,⟨0,by decide⟩,fun _ _=>⟨1,by decide⟩,fun q=>decide (q.val=0)⟩]

def word (n code : Nat) : Array Bool :=
  (List.range n |>.map (fun i=>Nat.testBit code i)).toArray

def reference (A : DFA Bool) (v : Array Bool) (bits : Array Bool) (l : Nat) : Bool :=
  (List.range (v.size+1)).any (fun i=> decide (l≤i) && (bits[i]?.getD false) &&
    A.final (A.run A.initial ((v.toList.drop l).take (i-l))))

def check (A : DFA Bool) (v : Array Bool) (bits : Array Bool) : IO Nat := do
  let idx := build A v bits
  unless idx.length==v.size && idx.answers.size==v.size+1 do
    throw <| IO.userError "cached size mismatch"
  unless idx.work==v.size*(6*A.stateCount+6)+3*A.stateCount+7 &&
      idx.work≤(6*A.stateCount+7)*(v.size+1) do
    throw <| IO.userError "build work mismatch"
  for l in List.range (v.size+4) do
    let result := query idx l
    let expected := reference A v bits l
    unless result.1==expected && result.2≤4 do
      throw <| IO.userError s!"query mismatch v={v} bits={bits} l={l} got={result.1} expected={expected}"
  return v.size+4

def main : IO Unit := do
  let mut texts := 0
  let mut builds := 0
  let mut queries := 0
  for n in List.range 7 do
    for code in List.range (2^n) do
      let v := word n code
      texts := texts+1
      for mask in List.range (2^(n+1)) do
        let bits := word (n+1) mask
        for A in auditAutomata do
          queries := queries + (←check A v bits)
          builds := builds+1
      for bits in #[#[], #[true], word (n/2) code, word (n+4) (2^(n+4)-1)] do
        for A in auditAutomata do
          queries := queries + (←check A v bits)
          builds := builds+1
  IO.println s!"far aggregate small texts={texts} builds={builds} queries={queries}"
  let n := 200000
  let v := (List.range n |>.map (fun i=>decide (i%2=1))).toArray
  let bits := (Array.replicate n false).push true
  let idx := build Regression.lastTrue v bits
  unless idx.length==n && idx.answers.size==n+1 &&
      idx.work≤(6*Regression.lastTrue.stateCount+7)*(n+1) do
    throw <| IO.userError "deep cache/build work mismatch"
  for l in List.range (n+3) do
    let result := query idx l
    unless result.1==decide (l<n) && result.2≤4 do
      throw <| IO.userError s!"deep mismatch at {l}"
  IO.println s!"far aggregate deep n={n} queries={n+3} buildWork={idx.work} queryWork≤4"
