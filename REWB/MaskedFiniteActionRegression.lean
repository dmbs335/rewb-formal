import REWB.MaskedFiniteActionRange
import REWB.MaskedFiniteActionMaps

/-! Noninjective, noncommuting lazy actions followed by a fresh point
    replacement.  This checks both tag-composition order and the rule that
    older tags affect old children, not the new replacement cell. -/
namespace REWB.MaskedFiniteAction.Regression

def base : Table 3 1 := Table.ofView (fun i _ _ => decide (i.val=0))
def fresh : Table 3 1 := Table.ofView (fun i _ _ => decide (i.val=2))
def collapse : Vector (Fin 3) 3 := #v[⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]
def swapEnds : Vector (Fin 3) 3 := #v[⟨2,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩]

def initial := Tree.build (k:=3) (m:=1) #[Table.one,base] 1 0
def first := Tree.reindex collapse initial.1
def second := Tree.reindex swapEnds first.1
def replaced := Tree.replace second.1 0 fresh
def prefixResult := Tree.queryPrefix replaced.1 1

theorem maps_noncommute :
    (Counted.compose collapse swapEnds).1.get ⟨0,by decide⟩ ≠
      (Counted.compose swapEnds collapse).1.get ⟨0,by decide⟩ := by decide

theorem execution :
    initial.2=18 ∧ first.2=7 ∧ second.2=7 ∧ replaced.2=20 ∧ prefixResult.2=5 ∧
    (Tree.cache second.1).view ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩=true ∧
    (Tree.cache replaced.1).view ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩=false ∧
    (Tree.cache replaced.1).view ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩=true ∧
    prefixResult.1.view ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩=true := by decide

theorem replaced_good : Tree.Good replaced.1 :=
  Tree.replace_good _
    (Tree.reindex_good _ _ (Tree.reindex_good _ _ (Tree.build_good _ _ _))) _ _

theorem universe_size : Maps.count 3=27 := Maps.count_eq 3

theorem source_map_decode :
    Maps.decode 3 (Maps.encode collapse)=collapse := Maps.decode_encode collapse

def matrixBase : Table 3 2 := Table.ofView (fun i p q=>
  if i.val=0 then decide (q.val=0) else decide (p=q))

def matrixFresh : Table 3 2 := Table.ofView (fun i p q=>
  if i.val=2 then decide (q.val=1) else decide (p=q))

def matrixSwap : Table 3 2 := Table.ofView (fun _ p q=>decide (p.val+q.val=1))

def matrixInitial := Tree.build (k:=3) (m:=2) #[Table.one,matrixBase,matrixSwap,Table.one] 2 0
def matrixTagged := Tree.reindex collapse matrixInitial.1
def matrixReplaced := Tree.replace matrixTagged.1 1 matrixFresh

/-- Reset then swap is constant-one; swapping the product order would
instead produce constant-zero. The fresh replacement retains its own map. -/
theorem interval_order :
    (Tree.queryRange matrixTagged.1 1 3).1.view 0 0 1=true ∧
    (Tree.queryRange matrixTagged.1 1 3).1.view 0 0 0=false ∧
    (Tree.queryRange matrixReplaced.1 1 3).1.view 0 1 0=true ∧
    (Tree.queryRange matrixReplaced.1 1 3).1.view 2 0 0=true ∧
    (Tree.queryRange matrixReplaced.1 4 2).1.view 0 0 0=true ∧
    (Tree.queryRange matrixReplaced.1 2 9).1.view 0 0 1=true ∧
    (Tree.queryRange matrixReplaced.1 9 12).1.view 0 0 0=true := by decide

theorem matrixReplaced_good : Tree.Good matrixReplaced.1 :=
  Tree.replace_good _ (Tree.reindex_good _ _ (Tree.build_good _ _ _)) _ _

end REWB.MaskedFiniteAction.Regression
