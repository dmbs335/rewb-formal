import REWB.PeriodicConstructionCache
import REWB.PhaseEqualityCache

/-! Equality-prefix tables retain every original comparison counter while
also accounting for both source reads, scalar updates, list construction,
finite row traversal, and materialized arrays. -/
namespace REWB.PeriodicConstruction.Cache
variable {α : Type} [DecidableEq α]

def equalScan (s : Nat→α) (a c : Nat) (same : Bool) :
    Nat→Result (List Bool×Nat)
  | 0=>(([same],0),2)
  | q+1=>
    let hit:=decide (s a=s c)
    let tail:=equalScan s (a+1) (c+1) (same && hit) q
    ((same::tail.1.1,tail.1.2+1),tail.2+10)

theorem equalScan_value (s : Nat→α) (a c : Nat) (same : Bool) (q : Nat) :
    (equalScan s a c same q).1=PhaseEqualityCache.scan s a c same q := by
  induction q generalizing a c same with
  | zero=>rfl
  | succ q ih=>simp only [equalScan,PhaseEqualityCache.scan,ih]

theorem equalScan_length (s : Nat→α) (a c : Nat) (same : Bool) (q : Nat) :
    (equalScan s a c same q).1.1.length=q+1 := by
  rw [equalScan_value,PhaseEqualityCache.scan_length]

theorem equalScan_work (s : Nat→α) (a c : Nat) (same : Bool) (q : Nat) :
    (equalScan s a c same q).2=10*q+2 := by
  induction q generalizing a c same with
  | zero=>rfl
  | succ q ih=>simp only [equalScan,ih,Nat.mul_add,Nat.mul_one]<;> omega

def equalPair (s : Nat→α) (q a c : Nat) : Result (Array Bool×Nat) :=
  let row:=equalScan s a c true q
  let out:=array row.1.1
  ((out.1,row.1.2),row.2+out.2+3)

theorem equalPair_value (s : Nat→α) (q a c : Nat) :
    (equalPair s q a c).1=
      let row:=PhaseEqualityCache.scan s a c true q
      (row.1.toArray,row.2) := by
  simp only [equalPair,array_value,equalScan_value]

def equalPairCost (q : Nat) : Nat := (10*q+2)+(2*(q+1)+1)+3

theorem equalPair_work (s : Nat→α) (q a c : Nat) :
    (equalPair s q a c).2=equalPairCost q := by
  simp only [equalPair,equalScan_work,array_work,equalScan_length,equalPairCost]

def equalRow (s : Nat→α) (q a : Nat) : Result (Array (Array Bool)×Nat) :=
  let domain:=CountedProjection.range q
  let rows:=collect (equalPair s q a) domain.1
  let out:=array rows.1.1
  ((out.1,rows.1.2),domain.2+rows.2+out.2+3)

theorem equalRow_value (s : Nat→α) (q a : Nat) :
    (equalRow s q a).1=PhaseEqualityCache.buildRow s q a := by
  simp only [equalRow,array_value,collect_value,CountedProjection.range_value,
    equalPair_value,PhaseEqualityCache.buildRow]

def equalRowCost (q : Nat) : Nat :=
  (2*q+1)+(q*(equalPairCost q+3)+1)+(2*q+1)+3

theorem equalRow_work (s : Nat→α) (q a : Nat) :
    (equalRow s q a).2=equalRowCost q := by
  have hc:=collect_work (equalPair s q a) (List.range q)
    (equalPairCost q) (equalPair_work s q a)
  rw [List.length_range] at hc
  simp only [equalRow,CountedProjection.range_value,range_work,array_work,
    collect_length,List.length_range,equalRowCost]
  rw [hc]

def equality (s : Nat→α) (q : Nat) : Result (PhaseEqualityCache.Table×Nat) :=
  let domain:=CountedProjection.range q
  let rows:=collect (equalRow s q) domain.1
  let out:=array rows.1.1
  ((out.1,rows.1.2),domain.2+rows.2+out.2+3)

theorem equality_value (s : Nat→α) (q : Nat) :
    (equality s q).1=PhaseEqualityCache.build s q := by
  simp only [equality,array_value,collect_value,CountedProjection.range_value,
    equalRow_value,PhaseEqualityCache.build]

def equalityCost (q : Nat) : Nat :=
  (2*q+1)+(q*(equalRowCost q+3)+1)+(2*q+1)+3

theorem equality_work (s : Nat→α) (q : Nat) :
    (equality s q).2=equalityCost q := by
  have hc:=collect_work (equalRow s q) (List.range q)
    (equalRowCost q) (equalRow_work s q)
  rw [List.length_range] at hc
  simp only [equality,CountedProjection.range_value,range_work,array_work,
    collect_length,List.length_range,equalityCost]
  rw [hc]

end REWB.PeriodicConstruction.Cache
