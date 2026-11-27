import REWB.MaskedRunCatalogRegression

/-! Independent direct-letter and direct-mask audit of the immutable
catalog over one actual mutable-source batch. All run scans, AP scans and
maximal-period extensions below are references used only by this audit. -/
open REWB REWB.RunGeometry REWB.MaskedRunCatalog

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def countRef (target : Array Bool) (base step i : Nat) : Nat :=
  (List.range (i+1)).foldl (fun out k=>
    out+(if k%step=i%step && target[base+k]?.getD false then 1 else 0)) 0

private def apRef (target : Array Bool) (R : Bounds) (K s lo hi residue : Nat) : Bool :=
  (List.range (hi+1)).any fun k=>
    let p:=s+k*R.period
    decide (lo≤k ∧ k%K=residue ∧ R.lo≤p ∧ p≤R.hi) && target[p]?.getD false

private structure Stats where
  texts : Nat := 0
  runs : Nat := 0
  lookups : Nat := 0
  counts : Nat := 0
  aps : Nat := 0
  dense : Nat := 0
  points : Nat := 0
  maxLookup : Nat := 0
  maxDiscovery : Nat := 0

private def referenceRun (text : Array (Fin 2)) (first q L : Nat) : Bounds := Id.run do
  let mut lo:=first
  let mut hi:=first+q+L
  while lo>0 && text[lo-1]?.getD 0==text[lo-1+q]?.getD 0 do lo:=lo-1
  while hi<text.size && text[hi-q]?.getD 0==text[hi]?.getD 0 do hi:=hi+1
  return ⟨lo,hi,q⟩

private def checkEntries (text : Array (Fin 2)) (target : Array Bool) (K : Nat)
    (out : Prepared) (stats : Stats) : IO Stats := do
  let catalog:=out.catalog
  let st:=out.sources
  let h:=width text.size
  require (catalog.width==h && catalog.length==text.size && catalog.modulus==K) "cached catalog metadata"
  require (catalog.runs==st.runs && catalog.entries.size==st.runs.size) "shared source/target run IDs"
  require (catalog.cells≤6*text.size*(text.size.log2+1)) "target span mass"
  require (catalog.work≤401*(text.size+1)*h^2) "catalog construction counter"
  require (out.work≤(MaskedRunEnumerationCost.coefficient 2+401)*(text.size+1)*h^2+
    MaskedMutableProgression.Batch.sourcePreparationBudget text.size+3) "full prepared counter"
  let mut stats:={stats with texts:=stats.texts+1,runs:=stats.runs+st.runs.size}
  for id in [:st.runs.size] do
    if hid : id<st.runs.size then
      let R:=st.runs[id]
      let found:=lookup catalog R
      let direct:=lookupId catalog R
      require (direct.1==some id && direct.2≤26*h+12) "exact sparse run ID"
      require (found.2≤26*h+15) "lookup work"
      let value←match found.1 with
        | none=>throw (IO.userError "enumerated run missing")
        | some value=>pure value
      require (value.id==id && value.value.run==R) "catalog entry identity"
      require (value.value.counts.size==R.hi-R.lo+1) "target count array length"
      for i in [:value.value.counts.size+2] do
        let expected:=if i<value.value.counts.size then countRef target R.lo (K*R.period) i else 0
        require (MaskedProgression.readCount value.value.counts i==expected)
          s!"prefix n={text.size} run={repr R} K={K} i={i}"
        stats:={stats with counts:=stats.counts+1}
      for s in [R.lo,R.lo+1,R.hi] do
        for lo in [0,1,3] do
          for hi in [0,2,R.hi-R.lo+2] do
            for residue in [0,1,K] do
              let got:=MaskedProgression.ap value.value.counts R.lo R.period K s lo hi residue
              require (got.answer==apRef target R K s lo hi residue) "stored target AP query"
              require (got.slots+got.arithmetic≤39) "target AP counter"
              stats:={stats with aps:=stats.aps+1}
      let alias : Bounds:=⟨R.lo+2^h,R.hi,R.period⟩
      require (lookupId catalog alias).1.isNone "out-of-bound low-bit alias guard"
      stats:={stats with lookups:=stats.lookups+3,maxLookup:=max stats.maxLookup found.2}
  let after:=MaskedMutableProgression.Batch.eraseMany [0,2,0,text.size/2,text.size,text.size] st
  require (after.runs==st.runs) "source erases preserve catalog IDs"
  for id in [:catalog.entries.size] do
    if hi : id<catalog.entries.size then
      let old:=catalog.entries[id]
      require ((lookupId catalog old.run).1==some id) "retained target lookup after source erase"
  pure stats

private def checkAbsent (text : Array (Fin 2)) (catalog : Index) (stats : Stats) : IO Stats := do
  let mut stats:=stats
  for lo in [:text.size+2] do
    for hi in [:text.size+2] do
      for q in [:text.size+2] do
        let R : Bounds:=⟨lo,hi,q⟩
        let got:=lookupId catalog R
        let expected:=(catalog.runs.toList.zipIdx).find? (fun pair=>pair.1==R) |>.map Prod.snd
        require (got.1==expected) s!"absent triple n={text.size} R={repr R}"
        require (got.2≤26*catalog.width+12) "absent lookup counter"
        stats:={stats with lookups:=stats.lookups+1}
  pure stats

private def checkDescriptors (text : Array (Fin 2)) (catalog : Index) (stats : Stats) : IO Stats := do
  let classes:=MaskedSuffixClass.prepare text 0
  let h:=width text.size
  let capacity:=2^h
  let mut stats:=stats
  for L in [1:min 5 (text.size+1)] do
    for base in [:text.size-L+1] do
      let xs:=(List.range (text.size-L+1)).filter fun p=>text.extract p (p+L)==text.extract base (base+L)
      let current:=MaskedClusterLeaders.execute h L (xs.reverse.map MaskedClusterLeaders.Operation.insert)
      require (current.state.occurrences.entries==xs) "actual complete occurrence state"
      for first in current.state.leaders.entries do
        let desc:=MaskedClusterDescriptor.describeLeader current.state capacity first
        let d←match desc.1 with
          | none=>throw (IO.userError "actual leader has no descriptor")
          | some d=>pure d
        let got:=descriptorShared catalog classes d L
        require (got.2≤52*h+34) "shared descriptor discovery work"
        if d.repetitions=0 then
          require got.1.isNone "singleton skips run discovery"
          stats:={stats with points:=stats.points+1}
        else
          let found←match got.1 with
            | none=>throw (IO.userError s!"dense descriptor missing n={text.size} L={L} d={repr d}")
            | some found=>pure found
          let R:=referenceRun text d.first d.period L
          require (found.value.run==R && catalog.runs[found.id]?==some R) "direct-letter run and original ID"
          require (R.lo≤d.first && d.last+L≤R.hi && R.period==d.period) "whole component run containment"
          stats:={stats with dense:=stats.dense+1,maxDiscovery:=max stats.maxDiscovery got.2}
  pure stats

private def deep (n period K : Nat) : IO Unit := do
  let text : Array (Fin 2):=Array.ofFn fun i : Fin n=>⟨(if period=1 then 0 else (i.val%period)/2)%2,by omega⟩
  let source:=Array.replicate (n+1) true
  let target:=Array.ofFn fun i : Fin (n/2)=>decide (i.val%3=0)
  let out:=prepare text 0 source target K
  let stats←checkEntries text target K out {}
  let classes:=MaskedSuffixClass.prepare text 0
  let L:=2*period
  let xs:=(List.range (n-L+1)).filter fun p=>text.extract p (p+L)==text.extract 0 L
  let current:=MaskedClusterLeaders.execute (width n) L (xs.reverse.map MaskedClusterLeaders.Operation.insert)
  let d←match (MaskedClusterDescriptor.describeLeader current.state (2^width n) 0).1 with
    | none=>throw (IO.userError "deep descriptor missing")
    | some d=>pure d
  let found:=descriptorShared out.catalog classes d L
  require found.1.isSome "deep catalog discovery"
  require (found.2≤52*width n+34) "deep discovery counter"
  match found.1 with
  | none=>throw (IO.userError "deep unexpected none")
  | some f=>require (f.value.run==referenceRun text d.first d.period L && d.last+L≤f.value.run.hi) "deep maximal interval"
  IO.println s!"runCatalogDeep n={n} period={period} K={K} runs={stats.runs} cells={out.catalog.cells} catalogWork={out.catalog.work} lookupWork={stats.maxLookup} discoveryWork={found.2} shortTarget=true sourcePersistence=true"
  (←IO.getStdout).flush

def main : IO Unit := do
  let mut stats : Stats:={}
  for n in [:8] do
    for code in [:2^n] do
      let text : Array (Fin 2):=Array.ofFn fun i : Fin n=>⟨(code/2^i.val)%2,by omega⟩
      let K:=if code%3=0 then 1 else if code%3=1 then 2 else n+10
      let source:=Array.ofFn fun i : Fin (n+1)=>decide ((i.val+code)%3=0)
      let targetSize:=if code%5=0 then 0 else if code%3=0 then n+1 else n/2
      let target:=Array.ofFn fun i : Fin targetSize=>decide ((i.val+code)%2=0)
      let out:=prepare text 0 source target K
      stats←checkEntries text target K out stats
      if n≤5 then stats←checkAbsent text out.catalog stats
      if n≤6 then stats←checkDescriptors text out.catalog stats
    IO.println s!"runCatalogLength n={n} texts={stats.texts} runs={stats.runs} lookups={stats.lookups} dense={stats.dense}"
    (←IO.getStdout).flush
  require (0<stats.runs && 0<stats.dense && 0<stats.points) "catalog discovery branch coverage"
  IO.println s!"runCatalogTotal texts={stats.texts} runs={stats.runs} lookups={stats.lookups} counts={stats.counts} aps={stats.aps} dense={stats.dense} points={stats.points} maxLookup={stats.maxLookup} maxDiscovery={stats.maxDiscovery} exactIDs=true exactCounts=true"
  (←IO.getStdout).flush
  deep 1024 1 1
  deep 513 3 1000000007
