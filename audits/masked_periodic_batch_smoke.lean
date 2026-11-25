import REWB.MaskedPeriodicBatchRegression

open REWB REWB.Spec REWB.MaskedPeriodic.Batch
open REWB.MaskedPeriodic.Batch.Regression
open REWB.MaskedProgression (readMask)

def accept (d : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := d.final (d.run d.initial w)

-- Independent exhaustive reference: its runs come from the bounded
-- semantic reference enumerator; only this test scans L and k.
def expected (b c e : DFA (Fin 2)) (w : Array (Fin 2)) (source target : Array Bool) (s : Nat) : Bool :=
  readMask source s &&
    (RunExtension.enumerate (ArrayText.read w 0) w.size).any fun R=>
      decide (R.lo≤s ∧ 3*R.period≤R.hi-R.lo) &&
      (List.range (w.size+1)).any fun L=>
        (List.range (w.size+1)).any fun k=>
          let j:=s+k*R.period
          decide (2*R.period≤L ∧ s+L≤j ∧ j+L≤R.hi) && readMask target j &&
            decide (slice w.toList s (s+L)=slice w.toList j (j+L)) &&
            accept b (slice w.toList s (s+L)) && accept c (slice w.toList (s+L) j) &&
            accept e (w.toList.drop (j+L))

def check (b c e : DFA (Fin 2)) (w : Array (Fin 2)) (source target : Array Bool) : IO Nat := do
  let got:=solve b c e w 0 source target
  unless got.output.hits.size=w.size+1 do throw (IO.userError "batch output size mismatch")
  let mut hits:=0
  for s in [0:w.size+2] do
    let wanted:=expected b c e w source target s
    unless readMask got.output.hits s=wanted do
      throw (IO.userError s!"periodic batch mismatch text={repr w.toList} source={s} wanted={wanted}")
    if wanted then hits:=hits+1
  let mass:=6*w.size*(w.size.log2+1)
  unless got.output.calls≤mass && got.output.scanWork≤6*mass &&
      got.output.preparationWork≤w.size+1+preparationLimit w.size*mass do
    throw (IO.userError "batch scan/prefix ledger exceeds proved span budget")
  unless got.indexProducts=(w.size.log2+1)*w.size do
    throw (IO.userError "batch did not preserve actual shared-index counter")
  unless got.enumerationWork≤MaskedRunEnumerationCost.coefficient 2*(w.size+1)*
      ((w.size+1).log2+1)^2 do throw (IO.userError "enumeration exceeds closed bound")
  return hits

def binary (n code : Nat) : Array (Fin 2) :=
  Array.ofFn fun i : Fin n=>⟨(code/2^i.val)%2,Nat.mod_lt _ (by decide)⟩

def main : IO Unit := do
  let start ← IO.monoMsNow
  let mut cases:=0
  let mut hits:=0
  for n in [0:7] do
    for code in [0:2^n] do
      let w:=binary n code
      let source:=Array.ofFn fun i : Fin (n+1)=>decide (i.val%3≠1)
      let target:=Array.ofFn fun i : Fin n=>decide ((i.val+code)%3≠0)
      hits:=hits+(←check universal universal universal w source target)
      cases:=cases+1
  let words : List (Array (Fin 2)):=
    [#[],#[1,1,1,1,1,1],#[0,1,0,1,0,1,0,1,0,1,0,1],
      #[1,0,0,1,0,0,1,0,0,1,0,0,1,0,0],#[0,1,1,1,1,1,1,0,0,0,0,0,1]]
  for w in words do
    let all:=Array.replicate (w.size+1) true
    let scattered:=Array.ofFn fun i : Fin (w.size+1)=>decide (i.val%3=0 ∨ i.val%5=2)
    for (source,target) in [(all,scattered),(scattered,all),(all,#[true,false,true]),(#[],all)] do
      hits:=hits+(←check universal universal universal w source target)
      cases:=cases+1
  for (b,e) in [(odd,universal),(universal,even)] do
    let w: Array (Fin 2):=#[0,1,0,1,0,1,0,1,0,1,0,1,0,1,1]
    hits:=hits+(←check b universal e w (Array.replicate 16 true)
      #[false,false,false,false,false,false,false,true,false,true,false,false,false,true])
    cases:=cases+1
  let finish ← IO.monoMsNow
  IO.println s!"periodic all-source batches={cases} acceptedSources={hits} mismatches=0 durationMs={finish-start}"
  IO.println "Cases cover empty/truncated masks, source filtering, multiple runs, phase shifts and full-input suffixes."
  IO.println "The measured query ledger retains finite-compiler construction exclusions."
