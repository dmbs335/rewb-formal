import REWB.MaskedAllStartRegression
import REWB.MaskedTraversalExecuteCostTotal

/-! Public entry point versus an independent literal finite witness
search. The test supplies only DFAs/text/source/target arrays, including
empty and short masks, with a two-state B in the bounded default.
The explicitly optional --broad probe adds two-state C/E cases; those
full finite-map preparations exceed the default runtime gate on this
runner. Correctness remains universally kernel checked.
-/
namespace REWB.MaskedAllStart.Audit
open REWB.MaskedCluster

def any : DFA (Fin 2):=⟨1,0,fun _ _=>0,fun _=>true⟩
def odd : DFA (Fin 2):=⟨2,0,fun q _=>if q=0 then 1 else 0,fun q=>q==1⟩

def direct (B C E : DFA (Fin 2)) (w : Word (Fin 2)) (source target : Array Bool) (s : Nat) : Bool :=
  source[s]?.getD false && (List.range (w.length+1)).any fun L=>
    (List.range (w.length+1)).any fun j=>
      decide (s+L≤j ∧ j+L≤w.length) && target[j]?.getD false &&
        decide (Spec.slice w s (s+L)=Spec.slice w j (j+L)) &&
        B.final (B.run B.initial (Spec.slice w s (s+L))) &&
        C.final (C.run C.initial (Spec.slice w (s+L) j)) &&
        E.final (E.run E.initial (Spec.slice w (j+L) w.length))

def probe (B C E : DFA (Fin 2)) (text : Array (Fin 2)) (source target : Array Bool) : IO (Nat×Nat×Nat×Nat) := do
  let n:=text.size
  let out:=solve B C E text 0 source target
  unless out.bits.size=n+1 do throw (IO.userError "public output shape changed")
  unless out.output.global.answers.count≤n+1 do throw (IO.userError "duplicate physical output")
  unless out.output.global.answers.history.length=out.output.global.answers.count do throw (IO.userError "history count mismatch")
  unless out.accountedWork≤MaskedAllStart.preparationBudget B C E n+MaskedTraversalExecute.Cost.executionBudget B C E n do
    throw (IO.userError "public accounted-work bound failed")
  unless out.fixedPatternBuilds≤4*((n+1)*(n+1).log2+(n+1))+2*(n+1)+1 do
    throw (IO.userError "public action-build bound failed")
  unless out.output.global.store.sources.delivered≤6*n*(n.log2+1) do
    throw (IO.userError "public source-fanout bound failed")
  unless out.output.global.stats.reported≤n+1 do
    throw (IO.userError "public report bound failed")
  let mut hits:=0
  for s in List.range (n+2) do
    let got:=out.bits[s]?.getD false
    let expected:=direct B C E text.toList source target s
    unless got=expected do
      throw (IO.userError s!"public solve mismatch text={text.toList}, source={s}, got={got}, expected={expected}")
    let live:=(MaskedMutableProgression.member out.output.global.store.sources.singleton s).1
    unless live=(source[s]?.getD false && !got) do throw (IO.userError "public source partition mismatch")
    if got then hits:=hits+1
  return (n+2,hits,out.output.global.stats.bands,out.output.global.stats.reported)

def run (broad : Bool) : IO Unit := do
  let begin←IO.monoMsNow
  let cases : List (DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)×Array (Fin 2)×Array Bool×Array Bool):=
    [(odd,any,any,#[],#[true],#[true]),
     (any,any,any,#[],#[true],#[true]),
     (any,any,any,#[],#[true],#[]),
     (odd,any,any,#[0,0],#[true,true,true],#[true,true,true]),
     (odd,any,any,#[0,1],#[true,true,true],#[true,true,true]),
     (odd,any,any,#[0,1,0],#[true],#[false,false,true]),
     (odd,any,any,#[0,1,0,1],#[true,false,true,true],#[false,true,false,true]),
     (odd,any,any,#[0,0,0,0,0,0],#[true,true,false,true,true,true,true],#[false,false,true,false,true,true]),
     (odd,any,any,#[0,1,0,1,0,1,1,0],#[true,false,true,true,false,true,true,true],#[false,true,false,true,true,false,false,true]),
     (odd,any,any,#[0,1,1,0,0,1,0,1,1,0],#[true,true,true,true,true,true,true,true,true,true],#[false,false,true,false,true,true,false,false,true,true])]
  let cases:=if broad then cases ++
    [(odd,odd,any,#[0,1,0],#[true,false,false,false],#[false,false,true,false]),
     (odd,any,odd,#[0,0,1],#[true,false,false,false],#[false,true,false,false]),
     (odd,odd,any,#[0,1,0,0,1,0],#[true,true,true,true,true,true,true],#[true,false,true,true,false,true,true]),
     (odd,any,odd,#[0,0,1,0,1,0],#[true,true,true,true,true,true,true],#[true,true,false,true,true,true,true]),
     (any,odd,odd,#[0,1,0],#[true,false,true,true],#[true,false,true,true])] else cases
  let mut comparisons:=0
  let mut hits:=0
  let mut bands:=0
  let mut reported:=0
  let mut done:=0
  for (b,c,e,w,source,target) in cases do
    let (a,h,k,r)←probe b c e w source target
    comparisons:=comparisons+a
    hits:=hits+h
    bands:=bands+k
    reported:=reported+r
    done:=done+1
    IO.println s!"public fixture {done}: length={w.size}, positives={h}, bands={k}, new reports={r}"
    (←IO.getStdout).flush
  let finish←IO.monoMsNow
  IO.println s!"public solve: cases={done}, comparisons={comparisons}, positives={hits}, actual bands={bands}, band reports={reported}, mismatches=0, elapsed={finish-begin} ms"
  IO.println "solve_correct is unconditional for the actual public solver; full running-time closure remains the separate cost track."

end REWB.MaskedAllStart.Audit

def main (args : List String) : IO Unit:=REWB.MaskedAllStart.Audit.run (args.contains "--broad")

#print axioms REWB.MaskedTraversalExecute.State.Valid.with_stats
#print axioms REWB.MaskedTraversalExecute.snapshot
#print axioms REWB.MaskedTraversalExecute.apply_anchor_size
#print axioms REWB.MaskedTraversalExecute.refreshCurrent_size
#print axioms REWB.MaskedTraversalExecute.eraseCurrent_size
#print axioms REWB.MaskedTraversalExecute.eraseMany_size
#print axioms REWB.MaskedTraversalExecute.band_prepared
#print axioms REWB.MaskedTraversalExecute.band_valid
#print axioms REWB.MaskedTraversalExecute.Effect.refl
#print axioms REWB.MaskedTraversalExecute.Effect.mono
#print axioms REWB.MaskedTraversalExecute.Effect.trans
#print axioms REWB.MaskedTraversalExecute.Effect.history
#print axioms REWB.MaskedTraversalExecute.Effect.saved
#print axioms REWB.MaskedTraversalExecute.band_effect
#print axioms REWB.MaskedTraversalExecute.import_support
#print axioms REWB.MaskedTraversalExecute.merge_patches_supported
#print axioms REWB.MaskedTraversalExecute.merge_dirty_supported
#print axioms REWB.MaskedTraversalExecute.fresh_valid
#print axioms REWB.MaskedTraversalExecute.leaf_valid
#print axioms REWB.MaskedTraversalExecute.initial_none_valid
#print axioms REWB.MaskedTraversalExecute.initial_crossing_valid
#print axioms REWB.MaskedTraversalExecute.merge_valid
#print axioms REWB.MaskedTraversalExecute.initial_effect
#print axioms REWB.MaskedTraversalExecute.fresh_effect
#print axioms REWB.MaskedTraversalExecute.leaf_effect
#print axioms REWB.MaskedTraversalExecute.merge_effect
#print axioms REWB.MaskedTraversalExecute.band_exhausted
#print axioms REWB.MaskedTraversalExecute.walk_preserves
#print axioms REWB.MaskedTraversalExecute.edge_preserves
#print axioms REWB.MaskedTraversalExecute.build_preserves
#print axioms REWB.MaskedTraversalExecute.suffix_preserves
#print axioms REWB.MaskedAllStart.solve_preserves
#print axioms REWB.MaskedAllStart.solve_correct
#print axioms REWB.MaskedAllStart.solve_size
#print axioms REWB.MaskedAllStart.solve_count
#print axioms REWB.MaskedAllStart.solve_nodup
#print axioms REWB.MaskedAllStart.solve_sources_valid
#print axioms REWB.MaskedAllStart.Regression.disabled_source
#print axioms REWB.MaskedAllStart.Regression.empty_target
#print axioms REWB.MaskedAllStart.Regression.separated_one_letter
