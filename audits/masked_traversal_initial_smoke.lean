import REWB.MaskedTraversalAnswersRegression

/-! Independent literal cuts and bounded semantic run enumeration check
the actual empty/periodic union and the real globally erased source rows.
The final output-list checks exercise only fresh reference positions;
they are an audit of bitmap accumulation, not a replacement traversal.
-/
namespace REWB.MaskedTraversalInitial.Audit
open REWB.Spec REWB.MaskedProgression

abbrev all : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def nonempty : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>q==1⟩
def odd : DFA (Fin 2) := ⟨2,0,fun q _=>if q==0 then 1 else 0,fun q=>q==1⟩
def accept (A : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := A.final (A.run A.initial w)

def original (B C E : DFA (Fin 2)) (text : Array (Fin 2)) (source target : Array Bool) (p : Nat) : Bool :=
  readMask source p && (List.range (text.size+1)).any fun L=>
    (List.range (text.size+1)).any fun j=>
      decide (p+L≤j ∧ j+L≤text.size) && readMask target j &&
      decide (slice text.toList p (p+L)=slice text.toList j (j+L)) &&
      accept B (slice text.toList p (p+L)) && accept C (slice text.toList (p+L) j) &&
      accept E (slice text.toList (j+L) text.size)

def handled (B C E : DFA (Fin 2)) (text : Array (Fin 2)) (source target : Array Bool) (p : Nat) : Bool :=
  let w:=text.toList
  let empty:=accept B [] && (List.range (text.size+1)).any fun j=>
    decide (p≤j) && readMask target j && accept C (slice w p j) && accept E (w.drop j)
  let periodic:=(RunExtension.enumerate (ArrayText.read text 0) text.size).any fun R=>
    decide (R.lo≤p ∧ 3*R.period≤R.hi-R.lo) &&
    (List.range (text.size+1)).any fun L=>(List.range (text.size+1)).any fun k=>
      let j:=p+k*R.period
      decide (2*R.period≤L ∧ p+L≤j ∧ j+L≤R.hi) && readMask target j &&
      decide (slice w p (p+L)=slice w j (j+L)) &&
      accept B (slice w p (p+L)) && accept C (slice w (p+L) j) && accept E (w.drop (j+L))
  readMask source p && (empty || periodic)

def check (B C E : DFA (Fin 2)) (text : Array (Fin 2)) (source target : Array Bool) : IO (Nat×Nat) := do
  let n:=text.size
  let initial:=start B C E text 0 source target 1
  let expected:=(List.range (n+1)).filter (handled B C E text source target)
  unless initial.answers.history=expected && initial.answers.count=expected.length do
    throw (IO.userError s!"initial union/history mismatch text={repr text.toList}")
  unless initial.answers.bits.size=n+1 && initial.answers.history.Nodup do throw (IO.userError "initial output shape")
  unless initial.sources.requests=expected.length do throw (IO.userError "initial source requests duplicated")
  unless initial.accountedWork≤initialBudget B C E n do throw (IO.userError "initial component budget")
  for p in [0:n+2] do
    unless readMask initial.answers.bits p=handled B C E text source target p do throw (IO.userError "initial output bit")
    unless (MaskedMutableProgression.member initial.sources.singleton p).1=
        (decide (p≤n) && readMask source p && !expected.contains p) do throw (IO.userError "initial source not removed")
  let repeated:=MaskedMutableProgression.Batch.eraseMany expected initial.sources
  unless repeated.delivered=initial.sources.delivered do throw (IO.userError "initial reverse membership redelivered")
  unless repeated.runs=initial.sources.runs && initial.sources.n=n && initial.sources.modulus=1 do
    throw (IO.userError "run provenance/metadata changed")
  let fresh:=(List.range (n+1)).filter fun p=>original B C E text source target p && !expected.contains p
  let accumulated:=MaskedTraversalAnswers.push fresh initial.answers
  unless accumulated.history=fresh.reverse++expected && accumulated.count=expected.length+fresh.length &&
      accumulated.history.Nodup && accumulated.count≤n+1 && accumulated.work=initial.answers.work+6*fresh.length do
    throw (IO.userError "output-sensitive accumulation")
  for p in [0:n+2] do
    unless readMask accumulated.bits p=original B C E text source target p do throw (IO.userError "accumulated bitmap reference mismatch")
  return (expected.length,fresh.length)

end REWB.MaskedTraversalInitial.Audit

def main : IO Unit := do
  let begin←IO.monoMsNow
  let mut cases:=0
  let mut initialHits:=0
  let mut residualHits:=0
  let words : List (Array (Fin 2)):=
    [#[],#[0,0,0],#[0,0,0,0,0,0,0,0],#[0,1,0,1,0,1,0,1,1],#[1,0,0,1,0,0,1,0,0,1,0,0]]
  for text in words do
    let full:=Array.replicate (text.size+1) true
    let source:=Array.ofFn fun p : Fin (text.size+1)=>decide (p.val%3 != 1)
    let target:=Array.ofFn fun p : Fin (text.size+1)=>decide (p.val%2=0)
    for (b,s,t) in [(REWB.MaskedTraversalInitial.Audit.all,full,target),
        (REWB.MaskedTraversalInitial.Audit.nonempty,source,full),
        (REWB.MaskedTraversalInitial.Audit.odd,full,#[false,false,true,false,true])] do
      let (a,r)←REWB.MaskedTraversalInitial.Audit.check b REWB.MaskedTraversalInitial.Audit.all
        REWB.MaskedTraversalInitial.Audit.all text s t
      cases:=cases+1
      initialHits:=initialHits+a
      residualHits:=residualHits+r
  let finish←IO.monoMsNow
  IO.println s!"initial union: cases={cases} initialHits={initialHits} freshResidualHits={residualHits} mismatches=0 elapsed={finish-begin}ms"
  IO.println "Actual empty/periodic solves, singleton erasures, one-shot reverse memberships and output bitmap/history agree."
  IO.println "Initialization cost retains the periodic component ledger's explicit compiler exclusions."
