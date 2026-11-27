import REWB.BoundaryBorderRegularGeometry

/-! Actual regular acceptance on a normalized candidate progression.
The zero-repetition case uses three direct range queries. The dense
case materializes finite orbit tables, constructs its formula, and runs
the counted existential solver. No all-true source mask is allocated. -/
namespace REWB.BoundaryBorder.Regular
open REWB.Spec REWB.Periodic REWB.MaskedCluster REWB.MaskedPeriodic
variable {α : Type}

theorem vector_map {k : Nat} {X Y : Type} (f : Fin k→X) (g : X→Y) :
    (Vector.ofFn f).map g=Vector.ofFn (fun i=>g (f i)) := by
  apply Vector.ext
  intro i hi
  simp

/-- Each finite vector records its scalar probes; the additional four
slots per entry charge pair storage, extraction and the counter pass.
This is a fixed-pattern table cost, independent of q and repetitions. -/
def materialize (A B E : DFA α) (maps : Maps A B E) :
    (Orbit (A.stateCount*E.stateCount)×Orbit B.stateCount)×Nat :=
  let step:=Vector.ofFn (fun z : Fin (A.stateCount*E.stateCount)=>
    (pack (maps.stepA.get (left z)) (maps.stepE.get (right z)),7))
  let yes:=Vector.ofFn (fun z : Fin (A.stateCount*E.stateCount)=>
    (A.final (left z) && E.final (maps.tailE.get (right z)),7))
  let tail:=Vector.ofFn (fun z : Fin B.stateCount=>(B.final (maps.tailB.get z),3))
  ((⟨step.map Prod.fst,pack (maps.prefixA.get A.initial) E.initial,yes.map Prod.fst⟩,
    ⟨maps.stepB,B.initial,tail.map Prod.fst⟩),
    BoundaryIndex.Counted.rowWork step+BoundaryIndex.Counted.rowWork yes+
    BoundaryIndex.Counted.rowWork tail+4*(2*(A.stateCount*E.stateCount)+B.stateCount)+8)

theorem materialize_value (A B E : DFA α) (maps : Maps A B E) :
    (materialize A B E maps).1=(forward A B E maps,backward A B E maps) := by
  simp only [materialize,forward,backward,productStep,vector_map]

theorem materialize_work (A B E : DFA α) (maps : Maps A B E) :
    (materialize A B E maps).2=24*(A.stateCount*E.stateCount)+8*B.stateCount+8 := by
  unfold materialize
  dsimp only
  rw [BoundaryIndex.Counted.rowWork_uniform _ 7 (by intro z; simp [BoundaryIndex.Table.get_ofFn]),
    BoundaryIndex.Counted.rowWork_uniform _ 7 (by intro z; simp [BoundaryIndex.Table.get_ofFn]),
    BoundaryIndex.Counted.rowWork_uniform _ 3 (by intro z; simp [BoundaryIndex.Table.get_ofFn])]
  omega

def Predicate (A B E : DFA α) (w : Word α) (p a j r : Nat) : Prop :=
  A.accepts (slice w 0 p) ∧ B.accepts (slice w p a) ∧ E.accepts (slice w (endAt j a p) r)

def point (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (p a j r : Nat) : Bool×Nat :=
  let x:=BoundaryApplication.Range.query A ai 0 p
  let y:=BoundaryApplication.Range.query B bi p a
  let z:=BoundaryApplication.Range.query E ei (endAt j a p) r
  (A.final (x.map.get A.initial) && B.final (y.map.get B.initial) && E.final (z.map.get E.initial),
    x.work+y.work+z.work+10)

theorem point_correct (A B E : DFA α) (w : Word α) (p a j r : Nat)
    (hp : p≤a) (ha : a≤w.length) (ht : endAt j a p≤r) (hr : r≤w.length) :
    (point A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) p a j r).1=true ↔ Predicate A B E w p a j r := by
  simp only [point,BoundaryApplication.Range.query_correct A w 0 p (Nat.zero_le _) (by omega),
    BoundaryApplication.Range.query_correct B w p a hp ha,
    BoundaryApplication.Range.query_correct E w (endAt j a p) r ht hr,
    Bool.and_eq_true,Predicate,DFA.accepts,and_assoc]

theorem point_work (A B E : DFA α) (w : Word α) (p a j r : Nat)
    (hp : p≤a) (ha : a≤w.length) (ht : endAt j a p≤r) (hr : r≤w.length) :
    (point A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) p a j r).2≤
        A.stateCount+B.stateCount+E.stateCount+24*(w.length.log2+2)+13 := by
  have h1:=BoundaryApplication.Range.query_work A w 0 p (Nat.zero_le _) (by omega)
  have h2:=BoundaryApplication.Range.query_work B w p a hp ha
  have h3:=BoundaryApplication.Range.query_work E w (endAt j a p) r ht hr
  simp only [point]
  omega

def dense (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (pLo q m a j r : Nat) : Bool×Nat :=
  let prepared:=maps A B E ai bi ei pLo q (pLo+m*q) a (endAt j a pLo) r
  let orbits:=materialize A B E prepared.maps
  let found:=Counted.solve orbits.1.1 orbits.1.2 0 m
  (found.1,prepared.work+orbits.2+found.2+6)

theorem pair_physical (A B E : DFA α) (w : Word α) (fallback : α) (pLo q m a j r k : Nat)
    (hg : Geometry w fallback pLo q m a j r) :
    PairAccepts
      (forward A B E (wordMaps A B E (slice w 0 pLo) (slice w pLo (pLo+q))
        (slice w (pLo+m*q) a) (slice w (endAt j a pLo-q) (endAt j a pLo))
        (slice w (endAt j a pLo) r))).data
      (backward A B E (wordMaps A B E (slice w 0 pLo) (slice w pLo (pLo+q))
        (slice w (pLo+m*q) a) (slice w (endAt j a pLo-q) (endAt j a pLo))
        (slice w (endAt j a pLo) r))).data 0 m k ↔
      k≤m ∧ Predicate A B E w (pLo+k*q) a j r := by
  simp only [PairAccepts,Nat.zero_le,true_and,Nat.sub_zero,forward_words,backward_words]
  constructor
  · rintro ⟨hk,⟨hA,hE⟩,hB⟩
    refine ⟨hk,?_,?_,?_⟩
    · rwa [prefix_slice w fallback pLo q m a j r k hg hk]
    · rwa [capture w fallback pLo q m a j r k hg hk]
    · rwa [suffix w fallback pLo q m a j r k hg hk]
  · rintro ⟨hk,hA,hB,hE⟩
    refine ⟨hk,⟨?_,?_⟩,?_⟩
    · rwa [prefix_slice w fallback pLo q m a j r k hg hk] at hA
    · rwa [suffix w fallback pLo q m a j r k hg hk] at hE
    · rwa [capture w fallback pLo q m a j r k hg hk] at hB

theorem dense_correct (A B E : DFA α) (w : Word α) (fallback : α) (pLo q m a j r : Nat)
    (hg : Geometry w fallback pLo q m a j r) :
    (dense A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) pLo q m a j r).1=true ↔
        ∃k,k≤m ∧ Predicate A B E w (pLo+k*q) a j r := by
  have hb:=hg.bounds w fallback pLo q m a j r
  simp only [dense,materialize_value]
  rw [Counted.solve_correct,maps_value A B E w pLo q (pLo+m*q) a (endAt j a pLo) r
    (Nat.le_trans hb.1 hg.last) hg.last hg.sourceEnd hg.finish hg.right]
  exact exists_congr (pair_physical A B E w fallback pLo q m a j r · hg)

def denseBudget (A B E : DFA α) (n : Nat) : Nat :=
  2*(A.stateCount+B.stateCount+E.stateCount)+48*(n.log2+2)+
    24*(A.stateCount*E.stateCount)+8*B.stateCount+
    Counted.solveBudget (A.stateCount*E.stateCount) B.stateCount+32

theorem dense_work (A B E : DFA α) (w : Word α) (fallback : α) (pLo q m a j r : Nat)
    (hg : Geometry w fallback pLo q m a j r) :
    (dense A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) pLo q m a j r).2≤denseBudget A B E w.length := by
  have hb:=hg.bounds w fallback pLo q m a j r
  have hm:=maps_work A B E w pLo q (pLo+m*q) a (endAt j a pLo) r
    (Nat.le_trans hb.1 hg.last) hg.last hg.sourceEnd hg.finish hg.right
  let prep:=(maps A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
    (BoundaryApplication.Range.build E w) pLo q (pLo+m*q) a (endAt j a pLo) r).maps
  have hs:=Counted.solve_work (materialize A B E prep).1.1 (materialize A B E prep).1.2 0 m
  dsimp only [prep] at hs
  simp only [dense,materialize_work,denseBudget]
  omega

def query (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (pLo q m a j r : Nat) : Bool×Nat :=
  if m=0 then let out:=point A B E ai bi ei pLo a j r; (out.1,out.2+1)
  else let out:=dense A B E ai bi ei pLo q m a j r; (out.1,out.2+1)

theorem query_correct (A B E : DFA α) (w : Word α) (fallback : α)
    (pLo q m a j r : Nat) (hp : pLo≤a) (ha : a≤w.length)
    (ht : endAt j a pLo≤r) (hr : r≤w.length)
    (hg : 0<m→Geometry w fallback pLo q m a j r) :
    (query A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) pLo q m a j r).1=true ↔
        ∃k,k≤m ∧ Predicate A B E w (pLo+k*q) a j r := by
  by_cases hm : m=0
  · subst m
    rw [query,if_pos rfl]
    change (point A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) pLo a j r).1=true ↔ _
    rw [point_correct A B E w pLo a j r hp ha ht hr]
    simp only [Nat.le_zero,Nat.zero_mul,Nat.add_zero,exists_eq_left]
  · have hh:=dense_correct A B E w fallback pLo q m a j r (hg (by omega))
    simpa only [query,if_neg hm] using hh

theorem query_work (A B E : DFA α) (w : Word α) (fallback : α)
    (pLo q m a j r : Nat) (hp : pLo≤a) (ha : a≤w.length)
    (ht : endAt j a pLo≤r) (hr : r≤w.length)
    (hg : 0<m→Geometry w fallback pLo q m a j r) :
    (query A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) pLo q m a j r).2≤denseBudget A B E w.length+1 := by
  by_cases hm : m=0
  · rw [query,if_pos hm]
    have hw:=point_work A B E w pLo a j r hp ha ht hr
    unfold denseBudget
    dsimp only
    omega
  · rw [query,if_neg hm]
    exact Nat.add_le_add_right (dense_work A B E w fallback pLo q m a j r (hg (by omega))) 1

end REWB.BoundaryBorder.Regular
