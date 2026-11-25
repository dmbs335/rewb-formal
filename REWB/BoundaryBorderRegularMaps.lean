import REWB.BoundaryBorderRegularFormula
import REWB.MaskedClusterCell

/-! Six shared range-map queries and a materialized A×E orbit. The
forward exponent advances A and E together; the backward exponent runs
B before its fixed tail. Noninjective DFA maps require no inverse. -/
namespace REWB.BoundaryBorder.Regular
open REWB.MaskedFiniteAction.Maps REWB.MaskedPeriodic REWB.Periodic REWB.Spec
variable {α : Type} {a e : Nat}

def pack (x : Fin a) (y : Fin e) : Fin (a*e) :=
  ⟨x.val*e+y.val,by
    have hb:=Nat.mul_le_mul_right e (Nat.succ_le_of_lt x.isLt)
    have hy:=y.isLt
    rw [Nat.succ_mul] at hb
    omega⟩

def left (q : Fin (a*e)) : Fin a :=
  ⟨q.val/e,by
    have he : 0<e := by
      by_cases hz : e=0
      · have hb:=q.isLt; simp only [hz,Nat.mul_zero] at hb; omega
      · omega
    exact (Nat.div_lt_iff_lt_mul he).mpr q.isLt⟩

def right (q : Fin (a*e)) : Fin e :=
  ⟨q.val%e,by
    apply Nat.mod_lt
    by_cases hz : e=0
    · have hb:=q.isLt; simp only [hz,Nat.mul_zero] at hb; omega
    · omega⟩

@[simp] theorem left_pack (x : Fin a) (y : Fin e) : left (pack x y)=x := by
  apply Fin.ext
  change (x.val*e+y.val)/e=x.val
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by have hh:=y.isLt; omega),Nat.div_eq_of_lt y.isLt]
  simp only [Nat.zero_add]

@[simp] theorem right_pack (x : Fin a) (y : Fin e) : right (pack x y)=y := by
  apply Fin.ext
  change (x.val*e+y.val)%e=y.val
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,Nat.zero_add,
    Nat.mod_eq_of_lt y.isLt]

def productStep (A : Map a) (E : Map e) : Map (a*e) :=
  Vector.ofFn (fun q=>pack (A.get (left q)) (E.get (right q)))

theorem product_orbit (A : Map a) (E : Map e) (x : Fin a) (y : Fin e) (k : Nat) :
    FiniteOrbit.orbit (productStep A E).get (pack x y) k=
      pack (FiniteOrbit.orbit A.get x k) (FiniteOrbit.orbit E.get y k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (productStep A E).get (FiniteOrbit.orbit (productStep A E).get (pack x y) k)=_
    rw [ih]
    simp only [productStep,BoundaryIndex.Table.get_ofFn,left_pack,right_pack,FiniteOrbit.orbit]

structure Maps (A B E : DFA α) where
  prefixA : Map A.stateCount
  stepA : Map A.stateCount
  stepB : Map B.stateCount
  tailB : Map B.stateCount
  stepE : Map E.stateCount
  tailE : Map E.stateCount

def forward (A B E : DFA α) (maps : Maps A B E) : Orbit (A.stateCount*E.stateCount) :=
  ⟨productStep maps.stepA maps.stepE,pack (maps.prefixA.get A.initial) E.initial,
    Vector.ofFn (fun q=>A.final (left q) && E.final (maps.tailE.get (right q)))⟩

def backward (A B E : DFA α) (maps : Maps A B E) : Orbit B.stateCount :=
  ⟨maps.stepB,B.initial,Vector.ofFn (fun q=>B.final (maps.tailB.get q))⟩

def wordMaps (A B E : DFA α) (pref V W U tail : Word α) : Maps A B E :=
  ⟨wordMap A pref,wordMap A V,wordMap B V,wordMap B W,wordMap E U,wordMap E tail⟩

theorem forward_words (A B E : DFA α) (pref V W U tail : Word α) (k : Nat) :
    (forward A B E (wordMaps A B E pref V W U tail)).data.test k=true ↔
      A.accepts (pref++repeatWord V k) ∧ E.accepts (repeatWord U k++tail) := by
  simp only [forward,wordMaps,Orbit.data,OrbitData.test,product_orbit,
    BoundaryIndex.Table.get_ofFn,left_pack,right_pack,wordMap_get,MaskedCluster.map_orbit,
    Bool.and_eq_true,DFA.accepts,DFA.run_append]

theorem backward_words (A B E : DFA α) (pref V W U tail : Word α) (k : Nat) :
    (backward A B E (wordMaps A B E pref V W U tail)).data.test k=true ↔
      B.accepts (repeatWord V k++W) := by
  simp only [backward,wordMaps,Orbit.data,OrbitData.test,BoundaryIndex.Table.get_ofFn,
    wordMap_get,MaskedCluster.map_orbit,DFA.accepts,DFA.run_append]

structure MapResult (A B E : DFA α) where
  maps : Maps A B E
  work : Nat

def maps (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (pLo q pHi a t0 r : Nat) : MapResult A B E :=
  let pref:=BoundaryApplication.Range.query A ai 0 pLo
  let astep:=BoundaryApplication.Range.query A ai pLo (pLo+q)
  let bstep:=BoundaryApplication.Range.query B bi pLo (pLo+q)
  let btail:=BoundaryApplication.Range.query B bi pHi a
  let estep:=BoundaryApplication.Range.query E ei (t0-q) t0
  let etail:=BoundaryApplication.Range.query E ei t0 r
  ⟨⟨pref.map,astep.map,bstep.map,btail.map,estep.map,etail.map⟩,
    pref.work+astep.work+bstep.work+btail.work+estep.work+etail.work+12⟩

theorem maps_value (A B E : DFA α) (w : Word α) (pLo q pHi a t0 r : Nat)
    (hp : pLo+q≤a) (hhi : pHi≤a) (ha : a≤w.length) (ht : t0≤r) (hr : r≤w.length) :
    (maps A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) pLo q pHi a t0 r).maps=
        wordMaps A B E (slice w 0 pLo) (slice w pLo (pLo+q)) (slice w pHi a)
          (slice w (t0-q) t0) (slice w t0 r) := by
  simp only [maps,wordMaps]
  rw [MaskedCluster.range_map A w 0 pLo (Nat.zero_le _) (by omega),
    MaskedCluster.range_map A w pLo (pLo+q) (by omega) (by omega),
    MaskedCluster.range_map B w pLo (pLo+q) (by omega) (by omega),
    MaskedCluster.range_map B w pHi a hhi ha,
    MaskedCluster.range_map E w (t0-q) t0 (by omega) (by omega),
    MaskedCluster.range_map E w t0 r ht hr]

theorem maps_work (A B E : DFA α) (w : Word α) (pLo q pHi a t0 r : Nat)
    (hp : pLo+q≤a) (hhi : pHi≤a) (ha : a≤w.length) (ht : t0≤r) (hr : r≤w.length) :
    (maps A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) pLo q pHi a t0 r).work≤
        2*(A.stateCount+B.stateCount+E.stateCount)+48*(w.length.log2+2)+18 := by
  have h1:=BoundaryApplication.Range.query_work A w 0 pLo (Nat.zero_le _) (by omega)
  have h2:=BoundaryApplication.Range.query_work A w pLo (pLo+q) (by omega) (by omega)
  have h3:=BoundaryApplication.Range.query_work B w pLo (pLo+q) (by omega) (by omega)
  have h4:=BoundaryApplication.Range.query_work B w pHi a hhi ha
  have h5:=BoundaryApplication.Range.query_work E w (t0-q) t0 (by omega) (by omega)
  have h6:=BoundaryApplication.Range.query_work E w t0 r ht hr
  simp only [maps]
  omega

end REWB.BoundaryBorder.Regular
