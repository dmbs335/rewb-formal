import REWB.MaskedEmptyBatchRegression

open REWB REWB.MaskedEmpty REWB.MaskedEmpty.SourceBatch
open REWB.MaskedEmpty.SourceBatch.Regression (allWords nonempty)
open REWB.MaskedProgression (readMask)

def epsilon : DFA (Fin 2) :=
  ⟨2,0,fun _ _=>1,fun q=>decide (q.val=0)⟩
def lastOne : DFA (Fin 2) :=
  ⟨2,0,fun _ c=>c,fun q=>decide (q.val=1)⟩

def binary (n code : Nat) : Array (Fin 2) :=
  ((List.range n).map fun i=>(⟨(code/2^i)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2)).toArray
def mask (n code : Nat) : Array Bool :=
  ((List.range n).map fun i=>decide ((code/2^i)%2=1)).toArray

def expected (B C E : DFA (Fin 2)) (w : Word (Fin 2))
    (source target : Array Bool) (s : Nat) : Bool :=
  readMask source s && B.final B.initial && (List.range (w.length+1)).any (fun j=>
    decide (s≤j) && readMask target j && C.final (C.run C.initial (Spec.slice w s j)) &&
      E.final (E.run E.initial (Spec.slice w j w.length)))

def check (B C E : DFA (Fin 2)) (text : Array (Fin 2)) (source target : Array Bool) : IO Nat := do
  let out:=start B C E text 0 source target 3
  let expectedReports:=(List.range (text.size+1)).filter (expected B C E text.toList source target)
  unless out.reported==expectedReports && out.reported.eraseDups==out.reported &&
      out.sources.requests=out.reported.length &&
      out.work≤(12*C.stateCount+6*E.stateCount+80)*(text.size+1)+
        MaskedMutableProgression.Batch.totalBudget 2 text.size (text.size+1) do
    throw (IO.userError "empty-to-mutable source initialization mismatch")
  let mut checks:=0
  for p in [0:text.size+3] do
    let wanted:=decide (p≤text.size) && readMask source p && !expectedReports.contains p
    unless (MaskedMutableProgression.member out.sources.singleton p).1==wanted do
      throw (IO.userError "empty reports did not delete precisely the reported global sources")
    for id in [0:out.sources.runs.size] do
      match out.sources.runs[id]?,out.sources.indexes[id]? with
      | some run,some row =>
        let inRun:=decide (run.lo≤p ∧ p≤run.hi)
        unless (MaskedMutableProgression.member row p).1==(wanted && inRun) do
          throw (IO.userError "empty reports did not delete the same physical source from a run row")
      | _,_ => throw (IO.userError "actual run ID lost its source row")
    checks:=checks+1
  return checks

def main : IO Unit := do
  let mut builds:=0
  let mut checks:=0
  for n in [0:5] do
    for code in [0:2^n] do
      let text:=binary n code
      for source in [Array.replicate (n+1) true,mask (n+1) (code+7),mask (n/2) (code+3)] do
        for target in [mask (n+1) (code*3+5),Array.replicate (n+1) true,#[]] do
          for profile in [(allWords,allWords,epsilon),(allWords,lastOne,allWords),(nonempty,allWords,allWords)] do
            checks:=checks+(←check profile.1 profile.2.1 profile.2.2 text source target)
            builds:=builds+1
  IO.println s!"empty-to-source batch builds={builds}, checked physical positions={checks}, exact one-shot reports and all run/global source deletions passed"
  let n:=512
  let out:=start allWords allWords epsilon (Array.replicate n (0 : Fin 2)) 0
    (Array.replicate (n+1) true) ((Array.replicate (n+1) false).set! n true) 3
  unless out.reported.length=n+1 && out.sources.requests=n+1 &&
      out.sources.sources.memberships=0 &&
      out.sources.singleton.tree.entries.isEmpty do
    throw (IO.userError "deep empty branch did not exhaust the actual mutable source indexes")
  IO.println s!"unary n={n}, reported={out.reported.length}, delivered={out.sources.delivered}, totalWork={out.work}; targets were read independently"
