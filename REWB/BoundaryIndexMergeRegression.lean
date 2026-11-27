import REWB.BoundaryIndexMergeBuild

/-! Duplicate positions, noninjective child maps, retained versions and
unchanged text transitions in the actual persistent merge schedule. -/
namespace REWB.BoundaryIndex.MergeRegression
open REWB.BoundaryIndex.Merge
open REWB.BoundaryIndex.MergeSchedule

private def ident : Vector (Fin 3) 3 := Counted.identity 3
private def collapse : Vector (Fin 3) 3 := Vector.ofFn (fun _=>0)

def rows : Array (Vector (Fin 2) 2) :=
  #[Vector.ofFn id,Vector.ofFn (fun _=>1),Vector.ofFn id,Vector.ofFn id]

def left : Program 3 2 3 := .node ident ident (.leaf 0 1 0) (.leaf 2 2 1)
def right : Program 3 2 3 := .node collapse ident (.leaf 0 2 1) (.leaf 3 1 0)
def program : Program 3 2 3 := .node collapse ident left right

def base : Tree 3 2 3 := (MergeBuild.prepare rows 3).1
def result : MergeSchedule.Result 3 2 3 := execute base program
def earlier : MergeSchedule.Result 3 2 3 := execute base left

/-- Two branches share position zero. Their states coalesce into the same
color without losing either state. -/
theorem overlapping_positions :
    (point result.state.tree 0).active 0 0=true ∧
    (point result.state.tree 0).active 0 1=true := by decide

theorem other_positions :
    (point result.state.tree 2).active 0 1=true ∧
    (point result.state.tree 3).active 1 0=true := by decide

/-- The earlier left version keeps its original color. -/
theorem prior_version :
    (point earlier.state.tree 0).active 1 0=true ∧
    (point result.state.tree 0).active 1 0=false := by decide

theorem static_transition :
    (point result.state.tree 1).trans 0=1 ∧
    (point result.state.tree 1).trans 1=1 := by decide

/-- The list counts actual imported leaf records, including the duplicate.
Exactly four records cross a light edge in this balanced four-leaf tree. -/
theorem actual_counts : result.state.cachedSize=4 ∧ result.state.positions.length=4 ∧
    result.transfers=4 := by decide

def distinctProgram : Program 3 2 3 :=
  .node collapse ident (.node ident ident (.leaf 0 1 0) (.leaf 1 2 1))
    (.node ident ident (.leaf 2 2 1) (.leaf 3 1 0))

theorem distinct_positions : (execute base distinctProgram).state.positions.Nodup :=
  execute_nodup base distinctProgram (by decide)

end REWB.BoundaryIndex.MergeRegression
