import REWB.MaskedAllStartFullCost

/-! Bounded actual public execution comparisons. Proof-only uniform
coefficients are deliberately not evaluated by this executable: their
large finite families are certified by the separate kernel audit.
The test compares old fields, concrete source erasure and literal word
witnesses after executing the new measured production path. -/
namespace REWB.MaskedAllStart.FullCost.Audit

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

def sameStats (a b : MaskedTraversalExecute.Stats) : Bool :=
  a.work=b.work && a.bands=b.bands && a.queryCalls=b.queryCalls &&
    a.reported=b.reported && a.actionBuilds=b.actionBuilds

def probe (B C E : DFA (Fin 2)) (text : Array (Fin 2)) (source target : Array Bool) :
    IO (Nat×Nat×Nat×Nat×Nat) := do
  let n:=text.size
  let measured:=FullCost.solve B C E text 0 source target
  let out:=measured.1
  let old:=MaskedAllStart.solve B C E text 0 source target
  unless out.bits=old.bits && out.accountedWork=old.accountedWork &&
      out.fixedPatternBuilds=old.fixedPatternBuilds do
    throw (IO.userError "full-cost public result changed")
  unless sameStats out.output.global.stats old.output.global.stats do
    throw (IO.userError "full-cost old execution counters changed")
  unless out.output.global.anchors=old.output.global.anchors &&
      out.output.global.answers.history=old.output.global.answers.history &&
      out.output.global.answers.count=old.output.global.answers.count &&
      out.output.global.answers.work=old.output.global.answers.work do
    throw (IO.userError "full-cost anchors or answer history changed")
  unless out.output.global.store.sources.updateWork=old.output.global.store.sources.updateWork &&
      out.output.global.store.sources.delivered=old.output.global.store.sources.delivered do
    throw (IO.userError "full-cost source fanout changed")
  unless out.bits.size=n+1 && out.output.global.answers.count≤n+1 && measured.2>0 do
    throw (IO.userError "full-cost output shape or empty ledger")
  let mut hits:=0
  for s in List.range (n+2) do
    let got:=out.bits[s]?.getD false
    let expected:=direct B C E text.toList source target s
    unless got=expected do
      throw (IO.userError s!"full-cost literal witness mismatch n={n}, source={s}")
    let live:=(MaskedMutableProgression.member out.output.global.store.sources.singleton s).1
    unless live=(source[s]?.getD false && !got) do
      throw (IO.userError "full-cost actual source partition mismatch")
    if got then hits:=hits+1
  return (n+2,hits,out.output.global.stats.bands,out.output.global.stats.reported,measured.2)

def runAudit : IO Unit := do
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
  let mut comparisons:=0
  let mut positives:=0
  let mut bands:=0
  let mut reports:=0
  let mut done:=0
  let mut work:=0
  for (b,c,e,w,source,target) in cases do
    IO.println s!"full-cost fixture {done+1} begins: length={w.size}"
    (←IO.getStdout).flush
    let (count,hits,bs,rs,units)←probe b c e w source target
    comparisons:=comparisons+count
    positives:=positives+hits
    bands:=bands+bs
    reports:=reports+rs
    work:=work+units
    done:=done+1
    IO.println s!"full-cost fixture {done}: positives={hits}, bands={bs}, reports={rs}, returned work={units}"
    (←IO.getStdout).flush
  unless reports>0 do throw (IO.userError "full-cost audit did not exercise actual reporting")
  let finish←IO.monoMsNow
  IO.println s!"full-cost public solve: cases={done}, comparisons={comparisons}, positives={positives}, bands={bands}, reports={reports}, total returned work={work}, mismatches=0, elapsed={finish-begin} ms"

end REWB.MaskedAllStart.FullCost.Audit

def main : IO Unit := REWB.MaskedAllStart.FullCost.Audit.runAudit
