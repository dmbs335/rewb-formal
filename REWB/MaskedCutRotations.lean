import REWB.MaskedCutIndex

/-! All rotations use one doubled-word cut index.  The executable batch
performs one query for each rotation and materializes one finite table per
result.  It never enumerates the quadratic rotation/cut-position pairs.
-/
namespace REWB.MaskedCut.Rotations
open REWB.FiniteRelation
open REWB.RangeProducts (Ops product)
open REWB.Spec (slice)

variable {M : Type} [DecidableEq M]

structure Result (e : Enumeration M) where
  values : Array (Index.Result e)
  preparation : Nat
  products : Nat
  visits : Nat
  outputCells : Nat

def queries (o : Ops M) (e : Enumeration M) (idx : Index.Tree e) (q : Nat) :
    List (Index.Result e) :=
  (List.range q).map (fun h=>Index.query o e idx h h (h+q-1) (h+q))

def batch (o : Ops M) (e : Enumeration M) (period : List M) : Result e :=
  let prepared := Index.build o e (period++period)
  let results := queries o e prepared.1 period.length
  ⟨results.toArray,prepared.2,(results.map Index.Result.products).sum,
    (results.map Index.Result.visits).sum,results.length⟩

theorem batch_size (o : Ops M) (e : Enumeration M) (period : List M) :
    (batch o e period).values.size=period.length := by
  simp only [batch,queries,List.size_toArray,List.length_map,List.length_range]

theorem batch_preparation (o : Ops M) (e : Enumeration M) (period : List M) :
    (batch o e period).preparation=
      (Nat.log2 (2*period.length)+1)*(2*period.length) := by
  simp only [batch,Index.build_products,List.length_append,Nat.two_mul]

theorem batch_outputCells (o : Ops M) (e : Enumeration M) (period : List M) :
    (batch o e period).outputCells=period.length := by
  simp only [batch,queries,List.length_map,List.length_range]

theorem batch_get (o : Ops M) (e : Enumeration M) (period : List M)
    (h : Nat) (hh : h<period.length) :
    (batch o e period).values[h]?=some
      (Index.query o e (Index.build o e (period++period)).1 h h
        (h+period.length-1) (h+period.length)) := by
  simp only [batch,queries,List.getElem?_toArray,List.getElem?_map]
  rw [List.getElem?_range hh]
  rfl

private theorem sum_map_bound {X : Type} (xs : List X) (f : X→Nat) (C : Nat)
    (h : ∀ x,x∈xs→f x≤C) : (xs.map f).sum≤xs.length*C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy=>h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem batch_bounds (o : Ops M) (e : Enumeration M) (period : List M) :
    (batch o e period).products≤3*period.length ∧
    (batch o e period).visits≤3*period.length*(Nat.log2 (2*period.length)+2) := by
  have each (h : Nat) (hh : h∈List.range period.length) := by
    have hp : h<period.length := List.mem_range.mp hh
    have hb : h≤h+period.length-1 := by omega
    have he : h+period.length≤(period++period).length := by
      simp only [List.length_append]
      omega
    exact Index.query_bounds o e (period++period) h h (h+period.length-1)
      (h+period.length) (Nat.le_refl _) hb (by omega) he
  constructor
  · have hs := sum_map_bound (List.range period.length)
      (fun h=>(Index.query o e (Index.build o e (period++period)).1 h h
        (h+period.length-1) (h+period.length)).products) 3
      (fun h hh=>(each h hh).1)
    simpa only [batch,queries,List.map_map,List.length_range,Nat.mul_comm,
      Function.comp_def] using hs
  · have hs := sum_map_bound (List.range period.length)
      (fun h=>(Index.query o e (Index.build o e (period++period)).1 h h
        (h+period.length-1) (h+period.length)).visits)
      (3*(Nat.log2 (2*period.length)+2)) (fun h hh=>by
        simpa only [List.length_append,Nat.two_mul] using (each h hh).2)
    simpa only [batch,queries,List.map_map,List.length_range,Function.comp_def,
      Nat.mul_assoc,Nat.mul_left_comm] using hs

theorem batch_correct (o : Ops M) (e : Enumeration M) (period : List M)
    (h : Nat) (hh : h<period.length) (p s : M) :
    ((batch o e period).values[h]?).bind
      (fun result=>result.answer.map (fun table=>MatrixTable.denote table p s))=some true ↔
        ∃ rho,rho<period.length ∧
          product o (slice (period++period) h (h+rho))=p ∧
          product o (slice (period++period) (h+rho) (h+period.length))=s := by
  rw [batch_get o e period h hh]
  simp only [Option.bind]
  have hb : h≤h+period.length-1 := by omega
  have hn : h+period.length≤(period++period).length := by
    simp only [List.length_append]
    omega
  rw [Index.query_correct o e (period++period) h h (h+period.length-1)
    (h+period.length) p s (Nat.le_refl _) hb (by omega) hn]
  constructor
  · rintro ⟨i,hi,hj,hp,hs⟩
    refine ⟨i-h,by omega,?_,?_⟩
    · simpa only [Nat.add_sub_of_le hi] using hp
    · simpa only [Nat.add_sub_of_le hi] using hs
  · rintro ⟨rho,hr,hp,hs⟩
    exact ⟨h+rho,by omega,by omega,hp,hs⟩

/-- A cut-constrained short suffix and a separate common tail preserve
the joint cut.  For the periodic application, eta is the run-end residue. -/
structure SplitResult (e : Enumeration M) where
  cuts : Index.Result e
  tail : DyadicIndex.Result (Summary e)

def splitQuery (o : Ops M) (e : Enumeration M) (idx : Index.Tree e)
    (start eta q : Nat) : SplitResult e :=
  ⟨Index.query o e idx start start (start+eta) (start+eta),
    DyadicIndex.query (ops o e) idx (start+eta) (start+q)⟩

theorem splitQuery_correct (o : Ops M) (e : Enumeration M) (xs : List M)
    (start eta q : Nat) (he : eta≤q) (hn : start+q≤xs.length) (p s : M) :
    (splitQuery o e (Index.build o e xs).1 start eta q).cuts.answer.map
      (fun table=>MatrixTable.denote table p s)=some true ↔
        ∃ rho,rho≤eta ∧ product o (slice xs start (start+rho))=p ∧
          product o (slice xs (start+rho) (start+eta))=s := by
  rw [show (splitQuery o e (Index.build o e xs).1 start eta q).cuts=
      Index.query o e (Index.build o e xs).1 start start (start+eta) (start+eta) from rfl,
    Index.query_correct o e xs start start (start+eta) (start+eta) p s
      (Nat.le_refl _) (by omega) (Nat.le_refl _) (by omega)]
  constructor
  · rintro ⟨i,hi,hj,hp,hs⟩
    refine ⟨i-start,by omega,?_,?_⟩
    · simpa only [Nat.add_sub_of_le hi] using hp
    · simpa only [Nat.add_sub_of_le hi] using hs
  · rintro ⟨rho,hr,hp,hs⟩
    exact ⟨start+rho,by omega,by omega,hp,hs⟩

theorem splitQuery_tail (o : Ops M) (e : Enumeration M) (xs : List M)
    (start eta q : Nat) (he : eta≤q) (hn : start+q≤xs.length) :
    (splitQuery o e (Index.build o e xs).1 start eta q).tail.answer.map Summary.total=
      some (product o (slice xs (start+eta) (start+q))) := by
  change (DyadicIndex.query (ops o e) (Index.build o e xs).1
    (start+eta) (start+q)).answer.map Summary.total=_
  rw [Index.range_value o e xs (start+eta) (start+q) (by omega) hn]
  simp only [Option.map,trace_total]

theorem splitQuery_bounds (o : Ops M) (e : Enumeration M) (xs : List M)
    (start eta q : Nat) (he : eta≤q) (hn : start+q≤xs.length) :
    (splitQuery o e (Index.build o e xs).1 start eta q).cuts.products+
      (splitQuery o e (Index.build o e xs).1 start eta q).tail.products≤4 ∧
    (splitQuery o e (Index.build o e xs).1 start eta q).cuts.visits+
      (splitQuery o e (Index.build o e xs).1 start eta q).tail.visits≤
        4*(Nat.log2 xs.length+2) := by
  have hc := Index.query_bounds o e xs start start (start+eta) (start+eta)
    (Nat.le_refl _) (by omega) (Nat.le_refl _) (by omega)
  have ht := Index.range_bounds o e xs (start+eta) (start+q) (by omega) hn
  simp only [splitQuery]
  constructor <;> omega

end REWB.MaskedCut.Rotations
