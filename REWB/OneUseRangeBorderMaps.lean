import REWB.BoundaryBorderRegularRows

/-! Six materialized range maps with a variable beginning for the A
context. The prefix starts at `base`, so this interface never silently
accepts sources before a requested lower bound. The existing finite
orbit representation and counted solver are reused unchanged. -/
namespace REWB.OneUseRange.Border.Regular
open REWB.BoundaryBorder.Regular REWB.Spec
variable {α : Type}

def maps (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (base pLo q pHi a t0 r : Nat) : MapResult A B E :=
  let pref:=BoundaryApplication.Range.query A ai base pLo
  let astep:=BoundaryApplication.Range.query A ai pLo (pLo+q)
  let bstep:=BoundaryApplication.Range.query B bi pLo (pLo+q)
  let btail:=BoundaryApplication.Range.query B bi pHi a
  let estep:=BoundaryApplication.Range.query E ei (t0-q) t0
  let etail:=BoundaryApplication.Range.query E ei t0 r
  ⟨⟨pref.map,astep.map,bstep.map,btail.map,estep.map,etail.map⟩,
    pref.work+astep.work+bstep.work+btail.work+estep.work+etail.work+12⟩

theorem maps_value (A B E : DFA α) (w : Word α) (base pLo q pHi a t0 r : Nat)
    (hbase : base≤pLo) (hp : pLo+q≤a) (hhi : pHi≤a) (ha : a≤w.length) (ht : t0≤r) (hr : r≤w.length) :
    (maps A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base pLo q pHi a t0 r).maps=
        wordMaps A B E (slice w base pLo) (slice w pLo (pLo+q)) (slice w pHi a)
          (slice w (t0-q) t0) (slice w t0 r) := by
  simp only [maps,wordMaps]
  rw [MaskedCluster.range_map A w base pLo hbase (by omega),
    MaskedCluster.range_map A w pLo (pLo+q) (by omega) (by omega),
    MaskedCluster.range_map B w pLo (pLo+q) (by omega) (by omega),
    MaskedCluster.range_map B w pHi a hhi ha,
    MaskedCluster.range_map E w (t0-q) t0 (by omega) (by omega),
    MaskedCluster.range_map E w t0 r ht hr]

theorem maps_work (A B E : DFA α) (w : Word α) (base pLo q pHi a t0 r : Nat)
    (hbase : base≤pLo) (hp : pLo+q≤a) (hhi : pHi≤a) (ha : a≤w.length) (ht : t0≤r) (hr : r≤w.length) :
    (maps A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base pLo q pHi a t0 r).work≤
        2*(A.stateCount+B.stateCount+E.stateCount)+48*(w.length.log2+2)+18 := by
  have h1:=BoundaryApplication.Range.query_work A w base pLo hbase (by omega)
  have h2:=BoundaryApplication.Range.query_work A w pLo (pLo+q) (by omega) (by omega)
  have h3:=BoundaryApplication.Range.query_work B w pLo (pLo+q) (by omega) (by omega)
  have h4:=BoundaryApplication.Range.query_work B w pHi a hhi ha
  have h5:=BoundaryApplication.Range.query_work E w (t0-q) t0 (by omega) (by omega)
  have h6:=BoundaryApplication.Range.query_work E w t0 r ht hr
  simp only [maps]
  omega


end REWB.OneUseRange.Border.Regular
