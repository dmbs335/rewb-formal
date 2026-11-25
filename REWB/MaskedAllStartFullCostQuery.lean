import REWB.MaskedAllStartFullCostBank
import REWB.MaskedFiniteConstruction
import REWB.PeriodicConstructionCutQuery
import REWB.MaskedClusterCut

/-! Cost-bearing joint-cut queries. The finite monoid range products and
the replay-map encoding are executed by their measured implementations.
The original cut answer and all four original counters are preserved.
The only structural hypothesis is the tiny-leaf property proved for the
actual shared text index; no answer or cost oracle is supplied. -/
namespace REWB.MaskedAllStart.FullCost.Query
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedCut.DFAIndex
variable {α : Type} {m : Nat}

def acceptCell (B C E : DFA α) (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (i j : Fin m) (cell : MatrixTable.Cell (Joint B C E)) : Bank.Result Bool :=
  let ⟨key,work⟩:=MaskedFiniteConstruction.encode (cell.2.1.2.1,cell.2.1.2.2)
  (cell.2.2 && B.final (cell.1.1.get B.initial) && bank.view key i j,work+7)

theorem acceptCell_value (B C E : DFA α) (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (i j : Fin m) (cell : MatrixTable.Cell (Joint B C E)) :
    (acceptCell B C E bank i j cell).1=MaskedCluster.Cut.acceptCell B C E bank i j cell := by
  simp only [acceptCell,MaskedCluster.Cut.acceptCell,MaskedFiniteConstruction.encode_value]

def cellCoefficient (c e : Nat) : Nat := MaskedFiniteConstruction.encodeBudget c e+8

theorem acceptCell_work (B C E : DFA α) (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (i j : Fin m) (cell : MatrixTable.Cell (Joint B C E)) :
    (acceptCell B C E bank i j cell).2+1≤cellCoefficient C.stateCount E.stateCount := by
  have hh:=MaskedFiniteConstruction.encode_work (cell.2.1.2.1,cell.2.1.2.2)
  dsimp only [acceptCell,cellCoefficient]
  omega

def scan (B C E : DFA α) (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (i j : Fin m) : List (MatrixTable.Cell (Joint B C E))→Bank.Result (Bool×Nat)
  | []=>((false,0),1)
  | cell::rest=>
    let ⟨hit,cellWork⟩:=acceptCell B C E bank i j cell
    let ⟨⟨later,probes⟩,restWork⟩:=scan B C E bank i j rest
    ((hit || later,probes+1),cellWork+restWork+1)

theorem scan_value (B C E : DFA α) (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (i j : Fin m) (cells : List (MatrixTable.Cell (Joint B C E))) :
    (scan B C E bank i j cells).1=BoundaryIndex.Counted.scan (MaskedCluster.Cut.acceptCell B C E bank i j) cells := by
  induction cells with
  | nil=>rfl
  | cons cell rest ih=>simp only [scan,BoundaryIndex.Counted.scan,acceptCell_value,ih]

theorem scan_work (B C E : DFA α) (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (i j : Fin m) (cells : List (MatrixTable.Cell (Joint B C E))) :
    (scan B C E bank i j cells).2≤cellCoefficient C.stateCount E.stateCount*cells.length+1 := by
  induction cells with
  | nil=>simp only [scan,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.le_refl]
  | cons cell rest ih=>
    have hh:=acceptCell_work B C E bank i j cell
    simp only [scan,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def cut (B C E : DFA α) (idx : MaskedCluster.Cut.Shared B C E)
    (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (representative lo hi old : Nat) (i j : Fin m) : Bank.Result MaskedCluster.Cut.Result :=
  if lo≤hi ∧ hi≤old ∧ representative+old≤idx.length then
    let ⟨cuts,indexWork⟩:=PeriodicConstruction.Cut.queryIndex B C E idx.tree
      representative (representative+lo) (representative+hi) (representative+old)
    match cuts.answer with
    | none=>(⟨false,cuts.products,cuts.visits,0,8⟩,indexWork+8)
    | some table=>
      let ⟨⟨hit,probes⟩,scanWork⟩:=scan B C E bank i j table.data
      (⟨hit,cuts.products,cuts.visits,probes,8⟩,indexWork+scanWork+8)
  else (⟨false,0,0,0,4⟩,4)

theorem cut_value (B C E : DFA α) (idx : MaskedCluster.Cut.Shared B C E)
    (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (representative lo hi old : Nat) (i j : Fin m) :
    (cut B C E idx bank representative lo hi old i j).1=
      MaskedCluster.Cut.query B C E idx bank representative lo hi old i j := by
  simp only [cut,MaskedCluster.Cut.query,PeriodicConstruction.Cut.queryIndex_value]
  split
  · cases hc : (MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) idx.tree
        representative (representative+lo) (representative+hi) (representative+old)).answer <;>
      simp only [hc,scan_value,MaskedCluster.Cut.scanCells]
  · rfl

def cutUnits (out : MaskedCluster.Cut.Result) : Nat :=
  out.products+out.visits+out.tupleProbes+out.arithmetic

def cutCoefficient (b c e : Nat) : Nat :=
  PeriodicConstruction.Cut.indexCoefficient b c e+cellCoefficient c e+10

theorem cutCoefficient_pos (b c e : Nat) : 1≤cutCoefficient b c e := by
  unfold cutCoefficient
  omega

theorem cut_work (B C E : DFA α) (idx : MaskedCluster.Cut.Shared B C E)
    (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (representative lo hi old : Nat) (i j : Fin m) (ht : PeriodicConstruction.Cut.Tiny idx.tree) :
    (cut B C E idx bank representative lo hi old i j).2≤
      cutCoefficient B.stateCount C.stateCount E.stateCount*
        cutUnits (cut B C E idx bank representative lo hi old i j).1 := by
  rw [cut_value]
  have hpos:=cutCoefficient_pos B.stateCount C.stateCount E.stateCount
  by_cases hg : lo≤hi ∧ hi≤old ∧ representative+old≤idx.length
  · have hx:=PeriodicConstruction.Cut.queryIndex_work B C E idx.tree
      representative (representative+lo) (representative+hi) (representative+old) ht
    have hp:=Nat.mul_le_mul_right
      ((MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) idx.tree representative
        (representative+lo) (representative+hi) (representative+old)).products+
       (MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) idx.tree representative
        (representative+lo) (representative+hi) (representative+old)).visits)
      (show PeriodicConstruction.Cut.indexCoefficient B.stateCount C.stateCount E.stateCount≤
        cutCoefficient B.stateCount C.stateCount E.stateCount by unfold cutCoefficient; omega)
    have hc : PeriodicConstruction.Cut.indexCoefficient B.stateCount C.stateCount E.stateCount+9≤
        cutCoefficient B.stateCount C.stateCount E.stateCount*8 := by
      unfold cutCoefficient
      omega
    simp only [Nat.mul_add,Nat.mul_one] at hx hp
    simp only [cut,MaskedCluster.Cut.query,hg,true_and,if_true,PeriodicConstruction.Cut.queryIndex_value]
    cases htable : (MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) idx.tree
        representative (representative+lo) (representative+hi) (representative+old)).answer with
    | none=>
      simp only [htable,cutUnits,Nat.add_zero,Nat.mul_add]
      omega
    | some table=>
      have hs:=scan_work B C E bank i j table.data
      have hq:=Nat.mul_le_mul_right table.data.length
        (show cellCoefficient C.stateCount E.stateCount≤cutCoefficient B.stateCount C.stateCount E.stateCount
          by unfold cutCoefficient; omega)
      simp only [htable,cutUnits,scan_value,MaskedCluster.Cut.scanCells,BoundaryIndex.Counted.scan_steps,Nat.mul_add]
      omega
  · have hh:=Nat.mul_le_mul_right 4 hpos
    simp only [cut,MaskedCluster.Cut.query,hg,if_false,cutUnits,Nat.zero_add]
    omega

theorem build_tiny (B C E : DFA α) (w : Word α) :
    PeriodicConstruction.Cut.Tiny (MaskedCluster.Cut.build B C E w).tree :=
  PeriodicConstruction.Cut.dfaBuild_tiny B C E w

end REWB.MaskedAllStart.FullCost.Query
