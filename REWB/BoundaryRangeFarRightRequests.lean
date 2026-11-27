import REWB.BoundaryRangeMask
import REWB.BoundaryRangeTable
import REWB.OneUseRangeFarAggregateSound

/-! Actual finite target-mask requests for the far-right block branch.
The mask arrays are built eagerly from one K range index. `Ready`
relates finite output arrays to those exact requests; it does not
provide or assume a fast implementation that constructs the outputs. -/
namespace REWB.BoundaryRange.FarRight
open REWB.BoundaryApplication
open REWB.OneUseRange
variable {σ : Nat}

abbrev MaskRows (K : DFA (Fin σ)) (n : Nat) :=
  Table.Index (fun _ : Fin K.stateCount=>Table.Index (fun _ : Fin K.stateCount=>FarMask.Result n))

structure Requests (K : DFA (Fin σ)) (w : Word (Fin σ)) where
  ranges : Range.Index K
  masks : MaskRows K w.length
  length : Nat
  length_eq : length=w.length
  grid : Nat
  work : Nat

def prepare (K : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) : Requests K w :=
  let ranges:=Range.build K w
  let n:=w.length
  let masks:=Table.build fun q : Fin K.stateCount=>
    let row:=Table.build fun k : Fin K.stateCount=>
      let out:=FarMask.build K ranges n grid q k
      (out,out.work)
    (row,row.work)
  ⟨ranges,masks,n,rfl,grid,masks.work+StartIndex.rangeBuildWork K ranges+n+5⟩

def readMask {K : DFA (Fin σ)} {w : Word (Fin σ)} (requests : Requests K w)
    (q k : Fin K.stateCount) (y : Nat) : Bool :=
  let bits:=(Table.get (Table.get requests.masks q) k).bits
  bits.toArray[y]?.getD false

@[simp] theorem prepare_get (K : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat)
    (q k : Fin K.stateCount) :
    Table.get (Table.get (prepare K w grid).masks q) k=
      FarMask.build K (Range.build K w) w.length grid q k := by
  simp only [prepare,Table.get_build]

theorem readMask_correct (K : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat)
    (q k : Fin K.stateCount) (y : Nat) (hy : y≤w.length) :
    readMask (prepare K w grid) q k y=farMask K w grid q k (w.length-y) := by
  unfold readMask
  rw [prepare_get]
  dsimp only
  have hlt : y<w.length+1 := by omega
  rw [Array.getElem?_eq_getElem (by simpa using hlt)]
  change (FarMask.build K (Range.build K w) w.length grid q k).bits.get ⟨y,hlt⟩=_
  exact FarMask.build_correct K w grid q k ⟨y,hlt⟩

abbrev Input (K : DFA (Fin σ)) := Vector (Vector (Array Bool) K.stateCount) K.stateCount

def Ready (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input K) : Prop :=
  ∀q k : Fin K.stateCount,∀y,y≤w.length→
    (FarAggregate.bit ((bits.get q).get k) y=true ↔
      Spec.maskedStart (Automata.reverse B)
        (Automata.reverse (Automata.gap C K D C.initial k)) (Automata.reverse A)
        w.reverse (readMask (prepare K w grid) q k) y)

theorem masked_mask_congr (B C E : DFA α) (w : Word α) (mask other : Nat→Bool)
    (hm : ∀j,j≤w.length→mask j=other j) (i : Nat) :
    Spec.maskedStart B C E w mask i ↔ Spec.maskedStart B C E w other i := by
  constructor
  · rintro ⟨a,j,t,hia,haj,hjt,ht,hmask,he,hB,hC,hE⟩
    exact ⟨a,j,t,hia,haj,hjt,ht,(hm j (by omega)) ▸ hmask,he,hB,hC,hE⟩
  · rintro ⟨a,j,t,hia,haj,hjt,ht,hmask,he,hB,hC,hE⟩
    exact ⟨a,j,t,hia,haj,hjt,ht,(hm j (by omega)).symm ▸ hmask,he,hB,hC,hE⟩

theorem ready_original (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat)
    (bits : Input K) (ready : Ready A B C K D w grid bits)
    (q k : Fin K.stateCount) (y : Nat) (hy : y≤w.length) :
    FarAggregate.bit ((bits.get q).get k) y=true ↔
      Spec.maskedStart (Automata.reverse B)
        (Automata.reverse (Automata.gap C K D C.initial k)) (Automata.reverse A)
        w.reverse (fun z=>farMask K w grid q k (w.length-z)) y := by
  exact (ready q k y hy).trans (masked_mask_congr _ _ _ _ _ _
    (fun z hz=>readMask_correct K w grid q k z (by simpa using hz)) y)

def maskBudget (K : DFA (Fin σ)) (n : Nat) : Nat := (n+1)*(FarMask.pointBudget K n+8)+3

theorem prepare_masks_work (K : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) :
    (prepare K w grid).masks.work≤K.stateCount*(K.stateCount*(maskBudget K w.length+3)+4)+1 := by
  apply Table.build_work_le
  intro q
  apply Table.build_work_le
  intro k
  exact FarMask.build_work K w grid q k

def prepareBudget (K : DFA (Fin σ)) (n : Nat) : Nat :=
  K.stateCount*(K.stateCount*(maskBudget K n+3)+4)+1+StartIndex.rangeBound K n+n+5

theorem prepare_work (K : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) :
    (prepare K w grid).work≤prepareBudget K w.length := by
  have hh:=prepare_masks_work K w grid
  change (prepare K w grid).masks.work+StartIndex.rangeBuildWork K (Range.build K w)+w.length+5≤_
  rw [StartIndex.rangeBuildWork_build]
  unfold prepareBudget
  omega

end REWB.BoundaryRange.FarRight
