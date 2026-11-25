import REWB.OneUseRangeBorderMaps

/-! The finite two-orbit query with a clipped A-prefix beginning. The
same actual range indexes serve every `base`; no substring is copied
and no text index is rebuilt by a query. -/
namespace REWB.OneUseRange.Border.Regular
open REWB.BoundaryBorder.Regular REWB.Spec REWB.Periodic REWB.MaskedCluster REWB.MaskedPeriodic
variable {α : Type}

theorem prefix_slice (w : Word α) (fallback : α) (base pLo q m a j r k : Nat)
    (hbase : base≤pLo) (hg : Geometry w fallback pLo q m a j r) (hk : k≤m) :
    slice w base (pLo+k*q)=slice w base pLo++repeatWord (slice w pLo (pLo+q)) k := by
  have hm:=Nat.mul_le_mul_right q hk
  have hb:=hg.last
  have ht:=hg.sourceEnd
  have h:=MaskedCluster.prefix_factor w fallback base pLo (pLo+m*q) q 0 k hg.source
    (Nat.zero_le _) (by omega) (by omega) (by omega)
  simpa only [Nat.zero_mul,Nat.add_zero,Nat.sub_zero] using h

def Predicate (A B E : DFA α) (w : Word α) (base p a j r : Nat) : Prop :=
  A.accepts (slice w base p) ∧ B.accepts (slice w p a) ∧ E.accepts (slice w (endAt j a p) r)

def point (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (base p a j r : Nat) : Bool×Nat :=
  let x:=BoundaryApplication.Range.query A ai base p
  let y:=BoundaryApplication.Range.query B bi p a
  let z:=BoundaryApplication.Range.query E ei (endAt j a p) r
  (A.final (x.map.get A.initial) && B.final (y.map.get B.initial) && E.final (z.map.get E.initial),
    x.work+y.work+z.work+10)

theorem point_correct (A B E : DFA α) (w : Word α) (base p a j r : Nat)
    (hbase : base≤p) (hp : p≤a) (ha : a≤w.length) (ht : endAt j a p≤r) (hr : r≤w.length) :
    (point A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base p a j r).1=true ↔ Predicate A B E w base p a j r := by
  simp only [point,BoundaryApplication.Range.query_correct A w base p hbase (by omega),
    BoundaryApplication.Range.query_correct B w p a hp ha,
    BoundaryApplication.Range.query_correct E w (endAt j a p) r ht hr,
    Bool.and_eq_true,Predicate,DFA.accepts,and_assoc]

theorem point_work (A B E : DFA α) (w : Word α) (base p a j r : Nat)
    (hbase : base≤p) (hp : p≤a) (ha : a≤w.length) (ht : endAt j a p≤r) (hr : r≤w.length) :
    (point A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base p a j r).2≤
        A.stateCount+B.stateCount+E.stateCount+24*(w.length.log2+2)+13 := by
  have h1:=BoundaryApplication.Range.query_work A w base p hbase (by omega)
  have h2:=BoundaryApplication.Range.query_work B w p a hp ha
  have h3:=BoundaryApplication.Range.query_work E w (endAt j a p) r ht hr
  simp only [point]
  omega

def dense (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (base pLo q m a j r : Nat) : Bool×Nat :=
  let prepared:=maps A B E ai bi ei base pLo q (pLo+m*q) a (endAt j a pLo) r
  let orbits:=materialize A B E prepared.maps
  let found:=Counted.solve orbits.1.1 orbits.1.2 0 m
  (found.1,prepared.work+orbits.2+found.2+6)

theorem pair_physical (A B E : DFA α) (w : Word α) (fallback : α) (base pLo q m a j r k : Nat)
    (hbase : base≤pLo) (hg : Geometry w fallback pLo q m a j r) :
    PairAccepts
      (forward A B E (wordMaps A B E (slice w base pLo) (slice w pLo (pLo+q))
        (slice w (pLo+m*q) a) (slice w (endAt j a pLo-q) (endAt j a pLo))
        (slice w (endAt j a pLo) r))).data
      (backward A B E (wordMaps A B E (slice w base pLo) (slice w pLo (pLo+q))
        (slice w (pLo+m*q) a) (slice w (endAt j a pLo-q) (endAt j a pLo))
        (slice w (endAt j a pLo) r))).data 0 m k ↔
      k≤m ∧ Predicate A B E w base (pLo+k*q) a j r := by
  simp only [PairAccepts,Nat.zero_le,true_and,Nat.sub_zero,forward_words,backward_words]
  constructor
  · rintro ⟨hk,⟨hA,hE⟩,hB⟩
    refine ⟨hk,?_,?_,?_⟩
    · rwa [prefix_slice w fallback base pLo q m a j r k hbase hg hk]
    · rwa [capture w fallback pLo q m a j r k hg hk]
    · rwa [suffix w fallback pLo q m a j r k hg hk]
  · rintro ⟨hk,hA,hB,hE⟩
    refine ⟨hk,⟨?_,?_⟩,?_⟩
    · rwa [prefix_slice w fallback base pLo q m a j r k hbase hg hk] at hA
    · rwa [suffix w fallback pLo q m a j r k hg hk] at hE
    · rwa [capture w fallback pLo q m a j r k hg hk] at hB

theorem dense_correct (A B E : DFA α) (w : Word α) (fallback : α) (base pLo q m a j r : Nat)
    (hbase : base≤pLo) (hg : Geometry w fallback pLo q m a j r) :
    (dense A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base pLo q m a j r).1=true ↔
        ∃k,k≤m ∧ Predicate A B E w base (pLo+k*q) a j r := by
  have hb:=hg.bounds w fallback pLo q m a j r
  simp only [dense,materialize_value]
  rw [Counted.solve_correct,maps_value A B E w base pLo q (pLo+m*q) a (endAt j a pLo) r
    hbase (Nat.le_trans hb.1 hg.last) hg.last hg.sourceEnd hg.finish hg.right]
  exact exists_congr (pair_physical A B E w fallback base pLo q m a j r · hbase hg)

def denseBudget (A B E : DFA α) (n : Nat) : Nat :=
  2*(A.stateCount+B.stateCount+E.stateCount)+48*(n.log2+2)+
    24*(A.stateCount*E.stateCount)+8*B.stateCount+
    Counted.solveBudget (A.stateCount*E.stateCount) B.stateCount+32

theorem dense_work (A B E : DFA α) (w : Word α) (fallback : α) (base pLo q m a j r : Nat)
    (hbase : base≤pLo) (hg : Geometry w fallback pLo q m a j r) :
    (dense A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base pLo q m a j r).2≤denseBudget A B E w.length := by
  have hb:=hg.bounds w fallback pLo q m a j r
  have hm:=maps_work A B E w base pLo q (pLo+m*q) a (endAt j a pLo) r
    hbase (Nat.le_trans hb.1 hg.last) hg.last hg.sourceEnd hg.finish hg.right
  let prep:=(maps A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
    (BoundaryApplication.Range.build E w) base pLo q (pLo+m*q) a (endAt j a pLo) r).maps
  have hs:=Counted.solve_work (materialize A B E prep).1.1 (materialize A B E prep).1.2 0 m
  dsimp only [prep] at hs
  simp only [dense,materialize_work,denseBudget]
  omega

def query (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (base pLo q m a j r : Nat) : Bool×Nat :=
  if m=0 then let out:=point A B E ai bi ei base pLo a j r; (out.1,out.2+1)
  else let out:=dense A B E ai bi ei base pLo q m a j r; (out.1,out.2+1)

theorem query_correct (A B E : DFA α) (w : Word α) (fallback : α)
    (base pLo q m a j r : Nat) (hbase : base≤pLo) (hp : pLo≤a) (ha : a≤w.length)
    (ht : endAt j a pLo≤r) (hr : r≤w.length)
    (hg : 0<m→Geometry w fallback pLo q m a j r) :
    (query A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base pLo q m a j r).1=true ↔
        ∃k,k≤m ∧ Predicate A B E w base (pLo+k*q) a j r := by
  by_cases hm : m=0
  · subst m
    rw [query,if_pos rfl]
    change (point A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base pLo a j r).1=true ↔ _
    rw [point_correct A B E w base pLo a j r hbase hp ha ht hr]
    simp only [Nat.le_zero,Nat.zero_mul,Nat.add_zero,exists_eq_left]
  · have hh:=dense_correct A B E w fallback base pLo q m a j r hbase (hg (by omega))
    simpa only [query,if_neg hm] using hh

theorem query_work (A B E : DFA α) (w : Word α) (fallback : α)
    (base pLo q m a j r : Nat) (hbase : base≤pLo) (hp : pLo≤a) (ha : a≤w.length)
    (ht : endAt j a pLo≤r) (hr : r≤w.length)
    (hg : 0<m→Geometry w fallback pLo q m a j r) :
    (query A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) base pLo q m a j r).2≤denseBudget A B E w.length+1 := by
  by_cases hm : m=0
  · rw [query,if_pos hm]
    have hw:=point_work A B E w base pLo a j r hbase hp ha ht hr
    unfold denseBudget
    dsimp only
    omega
  · rw [query,if_neg hm]
    exact Nat.add_le_add_right (dense_work A B E w fallback base pLo q m a j r hbase (hg (by omega))) 1


end REWB.OneUseRange.Border.Regular
