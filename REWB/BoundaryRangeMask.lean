import REWB.BoundaryRangeFar

/-! Actual construction of the reversed target mask in the far-right
reduction. One already-built K range index serves every state variant.
Every boundary performs at most one measured range query. The bit vector
is materialized eagerly; later mask reads do not scan an interval. -/
namespace REWB.BoundaryRange.FarMask
open REWB.Spec (slice)
open REWB.BoundaryApplication
variable {α : Type}

def point (K : DFA α) (ranges : Range.Index K) (n g : Nat)
    (q k : Fin K.stateCount) (y : Nat) : Bool×Nat :=
  if y≤n ∧ g<n-y then
    let tr:=Range.query K ranges g (n-y)
    (decide (tr.map.get q=k),tr.work+6)
  else (false,5)

theorem point_correct (K : DFA α) (w : Word α) (g : Nat)
    (q k : Fin K.stateCount) (y : Nat) (hy : y≤w.length) :
    (point K (Range.build K w) w.length g q k y).1=
      farMask K w g q k (w.length-y) := by
  unfold point
  by_cases hg : g<w.length-y
  · rw [if_pos ⟨hy,hg⟩]
    simp only [farMask,hg,decide_true,Bool.true_and,
      Range.query_correct K w g (w.length-y) (by omega) (by omega)]
  · rw [if_neg (fun h=>hg h.2)]
    simp only [farMask,hg,decide_false,Bool.false_and]

def pointBudget (K : DFA α) (n : Nat) : Nat := K.stateCount+8*(n.log2+2)+7

theorem point_work (K : DFA α) (w : Word α) (g : Nat)
    (q k : Fin K.stateCount) (y : Nat) :
    (point K (Range.build K w) w.length g q k y).2≤pointBudget K w.length := by
  unfold point
  split
  · rename_i h
    have hh:=Range.query_work K w g (w.length-y) (by omega) (by omega)
    dsimp only
    unfold pointBudget
    omega
  · dsimp only
    unfold pointBudget
    omega

structure Result (n : Nat) where
  bits : Vector Bool (n+1)
  work : Nat

/-- The second pass copies the bits and sums the returned row counters.
The extra eight operations per boundary charge vector/list traversal
and output construction in the same unit array/scalar model. -/
def build (K : DFA α) (ranges : Range.Index K) (n g : Nat)
    (q k : Fin K.stateCount) : Result n :=
  let rows:=Vector.ofFn (fun y : Fin (n+1)=>point K ranges n g q k y.val)
  ⟨rows.map Prod.fst,(rows.toList.map Prod.snd).sum+8*(n+1)+3⟩

theorem build_get (K : DFA α) (ranges : Range.Index K) (n g : Nat)
    (q k : Fin K.stateCount) (y : Fin (n+1)) :
    (build K ranges n g q k).bits.get y=(point K ranges n g q k y.val).1 := by
  simp [build,Vector.get]

theorem build_correct (K : DFA α) (w : Word α) (g : Nat)
    (q k : Fin K.stateCount) (y : Fin (w.length+1)) :
    (build K (Range.build K w) w.length g q k).bits.get y=
      farMask K w g q k (w.length-y.val) := by
  rw [build_get,point_correct K w g q k y.val (by have hh:=y.isLt; omega)]

theorem build_bits (K : DFA α) (w : Word α) (g : Nat) (q k : Fin K.stateCount) :
    (build K (Range.build K w) w.length g q k).bits=
      Vector.ofFn (fun y : Fin (w.length+1)=>farMask K w g q k (w.length-y.val)) := by
  apply Vector.ext
  intro i hi
  change (build K (Range.build K w) w.length g q k).bits.get ⟨i,hi⟩=
    (Vector.ofFn (fun y : Fin (w.length+1)=>farMask K w g q k (w.length-y.val))).get ⟨i,hi⟩
  rw [BoundaryIndex.Table.get_ofFn,build_correct]

private theorem sum_map_bound {X : Type} (xs : List X) (f : X→Nat) (b : Nat)
    (hb : ∀x,x∈xs→f x≤b) : (xs.map f).sum≤xs.length*b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=hb x List.mem_cons_self
    have hs:=ih (fun y hy=>hb y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem build_work (K : DFA α) (w : Word α) (g : Nat) (q k : Fin K.stateCount) :
    (build K (Range.build K w) w.length g q k).work≤
      (w.length+1)*(pointBudget K w.length+8)+3 := by
  have hsum:=sum_map_bound
    (Vector.ofFn (fun y : Fin (w.length+1)=>point K (Range.build K w) w.length g q k y.val)).toList
    Prod.snd (pointBudget K w.length) (by
      intro x hx
      rw [Vector.toList_ofFn,List.mem_ofFn] at hx
      obtain ⟨y,hy⟩:=hx
      rw [←hy]
      exact point_work K w g q k y.val)
  simp only [Vector.length_toList] at hsum
  unfold build
  dsimp only
  simp only [Nat.mul_add]
  omega

end REWB.BoundaryRange.FarMask
