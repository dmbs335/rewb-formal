import REWB.BoundaryTrieBuild

/-! Kernel-checked regressions exercise duplicate records, empty keys,
proper-prefix terminals, and distinct next-symbol branches. Actual large
construction is also exercised by the separate executable smoke probe. -/
namespace REWB.BoundaryTrie.Regression

def text : Array (Fin 2) := #[0,1,0,1,1]

def descriptors : List (Key text.size (Terminal 2 2)) :=
  [⟨0,2,by decide,.target 2 0 1⟩,
   ⟨2,2,by decide,.source 4⟩,
   ⟨0,1,by decide,.target 1 1 0⟩,
   ⟨1,2,by decide,.source 3⟩,
   ⟨5,0,by decide,.source 5⟩,
   ⟨1,0,by decide,.target 1 0 0⟩,
   ⟨4,1,by decide,.target 5 1 1⟩]

def built := Build.run text 0 descriptors

example : built.tree.nodes=13 := by
  have hh:=Build.run_nodes text 0 descriptors (by intro h; cases h)
  change built.tree.nodes+1=14 at hh
  omega

example : built.tree.leaves.Perm descriptors := (Build.run_correct text 0 descriptors).1

example : built.tree.Good (ArrayText.read text 0) :=
  (Build.run_correct text 0 descriptors).2.1

example : (Build.run text 0 ([] : List (Key text.size (Terminal 2 2)))).tree.nodes=0 := rfl

example : (Build.run text 0
    [(⟨5,0,by decide,.source 5⟩ : Key text.size (Terminal 2 2))]).tree.nodes=1 := by
  have hh:=Build.run_nodes text 0
    [(⟨5,0,by decide,.source 5⟩ : Key text.size (Terminal 2 2))] (by intro h; cases h)
  simp only [List.length_cons,List.length_nil] at hh
  omega

example : (commonPrefix built.prepared.ranks
    (⟨0,2,by decide,.target 2 0 1⟩ : Key text.size (Terminal 2 2))
    ⟨2,2,by decide,.source 4⟩).1=2 := by
  let a : Key text.size (Terminal 2 2):=⟨0,2,by decide,.target 2 0 1⟩
  let b : Key text.size (Terminal 2 2):=⟨2,2,by decide,.source 4⟩
  have hh:=prepare_commonPrefix text 0 descriptors a b
  apply Key.exact_unique (ArrayText.read text 0) a b _ 2 hh
  exact ⟨⟨by decide,by decide,rfl⟩,fun _ he=>he.1⟩

example : (commonPrefix built.prepared.ranks
    (⟨0,1,by decide,.target 1 1 0⟩ : Key text.size (Terminal 2 2))
    ⟨0,2,by decide,.target 2 0 1⟩).1=1 := by
  let a : Key text.size (Terminal 2 2):=⟨0,1,by decide,.target 1 1 0⟩
  let b : Key text.size (Terminal 2 2):=⟨0,2,by decide,.target 2 0 1⟩
  have hh:=prepare_commonPrefix text 0 descriptors a b
  apply Key.exact_unique (ArrayText.read text 0) a b _ 1 hh
  exact ⟨⟨by decide,by decide,rfl⟩,fun _ he=>he.1⟩

example : (∃path,built.tree.lookup path=some
    (⟨5,0,by decide,.source 5⟩ : Key text.size (Terminal 2 2))) := by
  apply (Build.run_paths text 0 descriptors _).mpr
  simp only [descriptors,List.mem_cons,List.mem_singleton,true_or,or_true]

end REWB.BoundaryTrie.Regression
