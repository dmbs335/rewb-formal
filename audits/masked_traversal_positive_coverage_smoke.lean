import REWB.MaskedTraversalPositiveCoverageRegression

/-! Independent original-cut checks against the actual empty/periodic
initialization and the actual built suffix driver's emitted bands. The
flattening and exhaustive scans occur only in this audit. Production
coverage is proof-only; its representative reads the cached tree field. -/
namespace REWB.MaskedTraversalPositiveCoverage.Audit
open REWB.Spec REWB.MaskedProgression REWB.MaskedClusterDescriptor REWB.MaskedRunDiscovery

abbrev all : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
abbrev odd : DFA (Fin 2) := ⟨2,0,fun q _=>if q==0 then 1 else 0,fun q=>q==1⟩
abbrev eps : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>q==0⟩

def accepted (A : DFA α) (w : Word α) : Bool := A.final (A.run A.initial w)
def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)
def binary (n code : Nat) : Array (Fin 2) :=
  Array.ofFn fun i : Fin n=>⟨(code/2^i.val)%2,Nat.mod_lt _ (by decide)⟩

/-- The reference enumerates original a,j,t cuts, without assuming equal
capture lengths, periodic runs, classes, owners, or a band assignment. -/
def originalCuts (B C E : DFA (Fin 2)) (w : Word (Fin 2)) (target : Array Bool) (p : Nat) :
    List (Nat×Nat×Nat) :=
  (List.range (w.length+1)).flatMap fun a=>
    (List.range (w.length+1)).flatMap fun j=>
      ((List.range (w.length+1)).filter fun t=>decide (p≤a ∧ a≤j ∧ j≤t) &&
        readMask target j && (slice w p a==slice w j t) && accepted B (slice w p a) &&
        accepted C (slice w a j) && accepted E (slice w t w.length)).map fun t=>(a,j,t)

def bandGood (B C E : DFA (Fin 2)) (w : Word (Fin 2)) (capacity : Nat)
    (source target : Array Bool) (removed : List Nat) (b : MaskedTraversalEdge.Band h) (p : Nat) : Bool :=
  MaskedCluster.Mutable.Batch.currentBit source removed p && decide (p∈b.snapshot.occurrences.entries) &&
    (List.range (w.length+1)).any fun L=>decide (b.lo≤L ∧ L≤b.hi) &&
      b.snapshot.occurrences.entries.any fun j=>readMask target j &&
        ((locate b.snapshot capacity p).1!=(locate b.snapshot capacity j).1) &&
        decide (p+L≤j ∧ j+L≤w.length) && accepted B (slice w p (p+L)) &&
        accepted C (slice w (p+L) j) && accepted E (slice w (j+L) w.length)

structure Stats where
  cases : Nat := 0
  bands : Nat := 0
  classes : Nat := 0
  assignments : Nat := 0
  sources : Nat := 0
  emptyHits : Nat := 0
  periodicHits : Nat := 0
  remainingSources : Nat := 0
  remainingWitnesses : Nat := 0
  laterWitnesses : Nat := 0
  deriving Repr

def plus (a b : Stats) : Stats :=
  ⟨a.cases+b.cases,a.bands+b.bands,a.classes+b.classes,a.assignments+b.assignments,
    a.sources+b.sources,a.emptyHits+b.emptyHits,a.periodicHits+b.periodicHits,
    a.remainingSources+b.remainingSources,a.remainingWitnesses+b.remainingWitnesses,
    a.laterWitnesses+b.laterWitnesses⟩

def fixture (B C E : DFA (Fin 2)) (text : Array (Fin 2)) (salt : Nat) : IO Stats := do
  let n:=text.size
  let w:=text.toList
  let height:=(n+1).log2+1
  let capacity:=2^height
  let source:=Array.ofFn fun p : Fin (n+1)=>decide ((p.val+salt)%3≠1)
  let target:=Array.ofFn fun p : Fin (n+1)=>decide ((p.val+salt)%3≠2)
  let initial:=MaskedTraversalInitial.start B C E text 0 source target 2
  let removed:=initial.answers.history
  let later:=removed++(List.range (n+1)).filter fun p=>decide ((p+salt)%5=1)
  let driver:=MaskedTraversalDriver.run height (prepareSuffixes text 0).trie.tree
  let bands:=driver.plan.bandView
  let mut stats:Stats:={cases:=1,bands:=bands.length}
  for b in bands do
    let xs:=b.snapshot.occurrences.entries
    let base:=representative b
    check (decide (0<b.lo ∧ b.lo≤b.hi ∧ base+b.hi≤n ∧ base∈xs)) "invalid emitted band metadata"
    check (xs.head?==some base) "representative disagreed with actual cached minimum"
    for L in List.range (n+1) do
      if b.lo≤L && L≤b.hi then
        let expected:=(List.range (n+1)).filter fun p=>decide (p+L≤n) &&
          (slice w p (p+L)==slice w base (base+L))
        check (xs==expected) "emitted snapshot was not the complete original prefix class"
        stats:={stats with classes:=stats.classes+1}
  for p in List.range (n+1) do
    for L in List.range (n+1) do
      if 0<L && p+L≤n then
        let selected:=bands.filter fun b=>decide (b.lo≤L ∧ L≤b.hi ∧ p∈b.snapshot.occurrences.entries)
        check (selected.length==1) "positive source/length was absent or duplicated in actual driver"
        stats:={stats with assignments:=stats.assignments+1}
    let cuts:=originalCuts B C E w target p
    let expected:=readMask source p && !cuts.isEmpty
    let initialBit:=readMask initial.answers.bits p
    let remaining:=bands.any fun b=>bandGood B C E w capacity source target removed b p
    check ((initialBit || remaining)==expected) "actual initial/emitted-band union disagreed with original cut predicate"
    let live:=MaskedCluster.Mutable.Batch.currentBit source removed p
    check ((MaskedMutableProgression.member initial.sources.singleton p).1==live) "actual initialized mutable source disagreed with recorded history"
    stats:={stats with
      sources:=stats.sources+1
      emptyHits:=stats.emptyHits+(if readMask initial.empty.answers p then 1 else 0)
      periodicHits:=stats.periodicHits+(if readMask initial.periodic.output.hits p then 1 else 0)
      remainingSources:=stats.remainingSources+(if remaining then 1 else 0)}
    if live then
      for (a,j,t) in cuts do
        check (p<a && t==j+(a-p)) "unreported original witness was empty or had unequal capture lengths"
        let L:=a-p
        let selected:=bands.filter fun b=>decide (b.lo≤L ∧ L≤b.hi ∧ p∈b.snapshot.occurrences.entries)
        let [b]:=selected | throw (IO.userError "remaining original witness lacked a unique actual band")
        check (decide (j∈b.snapshot.occurrences.entries)) "copy target absent from actual complete snapshot"
        check ((locate b.snapshot capacity p).1!=(locate b.snapshot capacity j).1) "periodically unreported pair retained equal actual owners"
        check (bandGood B C E w capacity source target removed b p) "unique actual band did not carry BandGood"
        stats:={stats with remainingWitnesses:=stats.remainingWitnesses+1}
        if MaskedCluster.Mutable.Batch.currentBit source later p then
          check (bandGood B C E w capacity source target later b p) "later live witness lost its assigned band"
          stats:={stats with laterWitnesses:=stats.laterWitnesses+1}
  return stats

def run : IO Unit := do
  let begin←IO.monoMsNow
  IO.println "positiveCoverageStart"
  (←IO.getStdout).flush
  let mut stats:Stats:={}
  for n in List.range 5 do
    for code in List.range (2^n) do
      stats:=plus stats (←fixture all all all (binary n code) code)
    IO.println s!"positiveCoverageLength n={n} cases={stats.cases}"
    (←IO.getStdout).flush
  IO.println s!"positiveCoverageBinary {repr stats}"
  (←IO.getStdout).flush
  stats:=plus stats (←fixture odd all all #[0,0] 0)
  stats:=plus stats (←fixture odd all all (Array.replicate 8 0) 0)
  stats:=plus stats (←fixture all all eps #[0,1,0,0,1,0,1,0,0,1,0,0,1,0] 1)
  check (stats.emptyHits>0 && stats.periodicHits>0 && stats.remainingSources>0 && stats.laterWitnesses>0)
    "initial/periodic/distinct/later-live branch coverage missing"
  let finish←IO.monoMsNow
  IO.println s!"positiveCoverageComplete {repr stats} mismatches=0 elapsed={finish-begin}ms"

end REWB.MaskedTraversalPositiveCoverage.Audit

def main : IO Unit := REWB.MaskedTraversalPositiveCoverage.Audit.run
