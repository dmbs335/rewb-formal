import REWB.BoundaryApplicationLift
import REWB.BoundaryIndexColors
import REWB.BoundaryIndexFixedEnd

/-! Materialized node acceptance rows. One shared bounded-cut index
answers every fixed finite (A state,D state) pair; the depth interval is
closed and includes both the empty repeat and the whole node label. The
result is an actual vector from D colors to encoded A-state subsets. -/
namespace REWB.BoundaryApplication.RTable
open REWB.BoundaryIndex
variable {σ : Nat}

structure Shared (A B D : DFA (Fin σ)) where
  index : BoundaryIndex.FixedEnd.Index A B D
  length : Nat
  buildProducts : Nat

def prepare (A B D : DFA (Fin σ)) (w : Word (Fin σ)) : Shared A B D :=
  let out:=BoundaryIndex.FixedEnd.build A B D w
  ⟨out.1,w.length,out.2⟩

structure Result (A D : DFA (Fin σ)) where
  map : Vector (Colors.Color A) D.stateCount
  products : Nat
  visits : Nat
  encodedRows : Nat

def compute (A B D : DFA (Fin σ)) (idx : Shared A B D) (endpoint depth : Nat) : Result A D :=
  let cells:=Vector.ofFn fun delta : Fin D.stateCount=>Vector.ofFn fun alpha : Fin A.stateCount=>
    BoundaryIndex.FixedEnd.query A B D idx.index endpoint depth 0 depth alpha delta
  let colors:=Vector.ofFn fun delta=>Colors.encode A (fun alpha=>(cells.get delta |>.get alpha).answer.getD false)
  ⟨colors,
    (List.ofFn fun delta=>(List.ofFn fun alpha=>(cells.get delta |>.get alpha).products).sum).sum,
    (List.ofFn fun delta=>(List.ofFn fun alpha=>(cells.get delta |>.get alpha).visits).sum).sum,
    D.stateCount⟩

theorem compute_value (A B D : DFA (Fin σ)) (idx : Shared A B D) (endpoint depth : Nat)
    (alpha : Fin A.stateCount) (delta : Fin D.stateCount) :
    Colors.select A alpha ((compute A B D idx endpoint depth).map.get delta)=
      (BoundaryIndex.FixedEnd.query A B D idx.index endpoint depth 0 depth alpha delta).answer.getD false := by
  simp only [compute,Table.get_ofFn,Colors.select,Colors.decode_encode]

private theorem getD_true (b : Option Bool) : b.getD false=true ↔ b=some true := by
  cases b with
  | none => simp only [Option.getD_none,Bool.false_eq_true,reduceCtorEq]
  | some b => simp only [Option.getD_some,Option.some.injEq]

theorem compute_correct (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (endpoint depth : Nat)
    (hd : depth≤endpoint) (he : endpoint≤w.length)
    (alpha : Fin A.stateCount) (delta : Fin D.stateCount) :
    Colors.select A alpha ((compute A B D (prepare A B D w) endpoint depth).map.get delta)=true ↔
      BoundaryIndex.FixedEnd.Predicate A B D w endpoint depth 0 depth alpha delta := by
  rw [compute_value,getD_true]
  exact BoundaryIndex.FixedEnd.query_correct A B D w endpoint depth 0 depth alpha delta
    (Nat.zero_le _) (Nat.le_refl _) hd he

private theorem sum_ofFn_le (n C : Nat) (f : Fin n→Nat) (hf : ∀i,f i≤C) :
    (List.ofFn f).sum≤n*C := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons]
    have hh:=ih (fun i=>f i.succ) (fun i=>hf i.succ)
    have hz:=hf 0
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem compute_bounds (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (endpoint depth : Nat)
    (hd : depth≤endpoint) (he : endpoint≤w.length) :
    (compute A B D (prepare A B D w) endpoint depth).products≤D.stateCount*(A.stateCount*6) ∧
      (compute A B D (prepare A B D w) endpoint depth).visits≤
        D.stateCount*(A.stateCount*(3*(w.length.log2+2))) ∧
      (compute A B D (prepare A B D w) endpoint depth).encodedRows=D.stateCount := by
  have hq:=fun alpha delta=>BoundaryIndex.FixedEnd.query_bounds A B D w endpoint depth 0 depth alpha delta
    (Nat.zero_le _) (Nat.le_refl _) hd he
  simp only [compute,Table.get_ofFn,prepare]
  refine ⟨?_,?_,True.intro⟩
  · apply sum_ofFn_le
    intro delta
    apply sum_ofFn_le
    intro alpha
    exact (hq alpha delta).1
  · apply sum_ofFn_le
    intro delta
    apply sum_ofFn_le
    intro alpha
    exact (hq alpha delta).2

def node (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Shared A B D) (t : TrieFor w) : Result A D :=
  compute A B D idx (idx.length-(representative w t).start) t.depth

theorem node_bounds (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (t : TrieFor w)
    (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[]) :
    (node A B D w (prepare A B D w) t).products≤D.stateCount*(A.stateCount*6) ∧
      (node A B D w (prepare A B D w) t).visits≤
        D.stateCount*(A.stateCount*(3*(w.length.log2+2))) ∧
      (node A B D w (prepare A B D w) t).encodedRows=D.stateCount := by
  have hc:=representative_common w fallback t hg (representative w t) (representative_mem w fallback t hg hn)
  have hb:=(representative w t).bounded
  have hsize:=reversed_size w
  have hlen : (prepare A B D w).length=w.length := rfl
  exact compute_bounds A B D w _ _ (by have hh:=hc.1; omega) (by omega)

theorem node_correct (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (t : TrieFor w)
    (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (alpha : Fin A.stateCount) (delta : Fin D.stateCount) :
    Colors.select A alpha ((node A B D w (prepare A B D w) t).map.get delta)=true ↔
      BoundaryIndex.FixedEnd.Predicate A B D w (w.length-(representative w t).start)
        t.depth 0 t.depth alpha delta := by
  have hc:=representative_common w fallback t hg (representative w t) (representative_mem w fallback t hg hn)
  have hb:=(representative w t).bounded
  have hsize:=reversed_size w
  have hlen : (prepare A B D w).length=w.length := rfl
  exact compute_correct A B D w _ _ (by have hh:=hc.1; omega) (by omega) alpha delta

/-- Only the fixed finite row encodings remain outside the inherited
matrix-product/visit counters. Each output is an integer color code. -/
def Result.work (A D : DFA (Fin σ)) (r : Result A D) : Nat :=
  r.products+8*r.visits+r.encodedRows

theorem node_work (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (t : TrieFor w)
    (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[]) :
    Result.work A D (node A B D w (prepare A B D w) t)≤
      D.stateCount*(A.stateCount*6)+8*(D.stateCount*(A.stateCount*(3*(w.length.log2+2))))+D.stateCount := by
  have hb:=node_bounds A B D w fallback t hg hn
  unfold Result.work
  omega

end REWB.BoundaryApplication.RTable
