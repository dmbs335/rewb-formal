import REWB.MaskedOrderedLifecycle

namespace REWB.MaskedOrdered.Regression
open REWB.MaskedEventBudget (MergeTree leaves edges)

def first : State 4 := (add (State.empty 4) 16 4).1
def second : State 4 := (add first 16 12).1
def middle : Insertion 4 := insert second.tree 16 8

theorem middle_repairs : middle.tree.entries=[4,8,12] ∧
    middle.fresh=[(4,8),(8,12)] ∧ middle.retired=[(4,12)] ∧ middle.inserted=true := by decide

theorem duplicate_no_events :
    (insert second.tree 16 4).tree=second.tree ∧
    (insert second.tree 16 4).fresh=[] ∧
    (insert second.tree 16 4).retired=[] ∧
    (insert second.tree 16 4).inserted=false := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem old_versions : first.tree.entries=[4] ∧ second.tree.entries=[4,12] ∧
    middle.tree.entries=[4,8,12] := by decide

theorem strict_neighbors :
    (Tree.pred middle.tree 16 8).1=some 4 ∧
    (Tree.succ middle.tree 16 8).1=some 12 ∧
    (Tree.pred middle.tree 16 0).1=none ∧
    (Tree.succ middle.tree 16 100).1=none ∧
    (Tree.pred middle.tree 16 100).1=some 12 ∧
    (Tree.succ middle.tree 16 0).1=some 4 := by decide

def sample : MergeTree := .node (.node (.leaf 0) (.leaf 8)) (.node (.leaf 4) (.leaf 12))

theorem sample_bounded : Bounded 4 sample := by
  intro p hp
  simp only [sample,leaves,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (rfl|rfl)|(rfl|rfl) <;> decide

theorem sample_distinct : (leaves sample).Nodup := by decide

theorem sample_run : (run 4 sample).1.tree.entries=[0,4,8,12] ∧
    (run 4 sample).1.positions=[8,0,4,12] ∧
    (run 4 sample).2.imports=4 ∧
    (run 4 sample).2.fresh=[(4,8),(8,12),(0,4),(4,12),(0,8)] ∧
    (run 4 sample).2.retired=[(0,8),(4,12)] := by decide

def bigger : State 4 := (add (add (add (State.empty 4) 16 1).1 16 7).1 16 15).1

theorem retains_heavy : (merge 16 second bigger {}).1.positions=[4,12,15,7,1] ∧
    (merge 16 second bigger {}).2.imports=2 ∧
    bigger.positions=[15,7,1] ∧ second.positions=[12,4] := by decide

theorem old_light_retired_once :
    discardedAll second.tree 16 second.positions=[(4,12)] := by decide

theorem sparse_empty : (State.empty 100).tree.count=0 ∧
    (Tree.contains (State.empty 100).tree 0 0).2=1 ∧
    (Tree.pred (State.empty 100).tree 0 0).2=1 ∧
    (Tree.succ (State.empty 100).tree 0 0).2=1 := by decide

end REWB.MaskedOrdered.Regression
