import REWB.BoundaryIndexMixed

/-! Heavy selection must use total source+target mass. The left child here
has mass 3 but only 1 target; the right child has mass 2 and 2 targets. -/
namespace REWB.BoundaryIndex.MixedRegression
open REWB.BoundaryIndex.Merge

private def ident : Vector (Fin 3) 3 := Counted.identity 3
private def collapse : Vector (Fin 3) 3 := Vector.ofFn (fun _=>0)

def rows : Array (Vector (Fin 2) 2) :=
  #[Vector.ofFn id,Vector.ofFn (fun _=>1),Vector.ofFn id,Vector.ofFn id,Vector.ofFn id]

def base : Tree 3 2 3 := (MergeBuild.prepare rows 3).1

def left : Mixed.Program 3 2 3 :=
  .node ident ident (.source 0) (.node ident ident (.source 1) (.target 2 1 0))

def right : Mixed.Program 3 2 3 := .node ident ident (.target 3 2 1) (.target 4 2 0)
def program : Mixed.Program 3 2 3 := .node collapse ident left right

def L := Mixed.execute base left
def R := Mixed.execute base right
def result := Mixed.execute base program

/-- Target-count and total-mass choices disagree on this input. -/
theorem mass_drives_choice :
    L.totalMass=3 ∧ L.state.cachedSize=1 ∧ R.totalMass=2 ∧ R.state.cachedSize=2 ∧
    Mixed.imported L.state R.state L.totalMass R.totalMass=2 ∧
    min L.state.cachedSize R.state.cachedSize=1 := by decide

/-- One target moves inside the right child; both right targets move at
its parent. Silent sources never enter the target position list. -/
theorem actual_counts : result.totalMass=5 ∧ result.state.cachedSize=3 ∧
    result.state.positions.length=3 ∧ result.transfers=3 := by decide

theorem exact_targets :
    (point result.state.tree 2).active 0 0=true ∧
    (point result.state.tree 3).active 2 1=true ∧
    (point result.state.tree 4).active 2 0=true := by decide

theorem silent_sources :
    (point result.state.tree 0).active 0 0=false ∧
    (point result.state.tree 1).active 2 1=false ∧
    (point result.state.tree 1).trans 0=1 := by decide

theorem prior_version : (point L.state.tree 2).active 1 0=true ∧
    (point result.state.tree 2).active 1 0=false := by decide

theorem distinct_targets : result.state.positions.Nodup :=
  Mixed.execute_nodup base program (by decide)

end REWB.BoundaryIndex.MixedRegression
