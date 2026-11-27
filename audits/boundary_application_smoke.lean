import REWB.BoundaryApplicationQuery
open REWB REWB.BoundaryApplication

def colorDFA : DFA (Fin 2) := ⟨2,0,fun _ a=>a,fun _=>true⟩
def suffixDFA : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩

def auditVersion (w : Word (Fin 2)) (g : Nat) (t : TrieFor w)
    (s : Versions.Snapshot 2 2 (height w.length)) : IO Nat := do
  let targets := t.leaves.filterMap fun a=>match a.record with
    | .source _ => none
    | .target p => some p
  let root := Versions.root s
  unless root.totalMass == t.leaves.length && root.state.cachedSize == targets.length do
    throw (IO.userError "saved source/target masses differ")
  for i in List.range (w.length+1) do
    if hi : i<w.length+1 then
      let p := position (⟨i,hi⟩ : Fin (w.length+1))
      let cell := BoundaryIndex.Merge.point root.state.tree p
      for c in (List.ofFn id : List (Fin 2)) do
        for q in (List.ofFn id : List (Fin 2)) do
          let expected := targets.any fun target=>
            target.val==i && c==color colorDFA w g target t.depth && q==suffixDFA.initial
          unless cell.active c q == expected do
            throw (IO.userError s!"saved color/position mismatch: depth={t.depth} endpoint={i}")
          let trans : Fin 2 := if i=0 then q else 1
          unless cell.trans q == trans do throw (IO.userError "static E letter changed")
  for r in List.range (w.length+1) do
    for c in (List.ofFn id : List (Fin 2)) do
      let select := fun q : Fin 2=>decide (q=c)
      let actual := (FixedEnd.query suffixDFA select s r).1
      let expected := targets.any fun target=>
        decide (target.val≤r) && select (color colorDFA w g target t.depth) &&
          suffixDFA.final (suffixDFA.run suffixDFA.initial (Spec.slice w target.val r))
      unless actual == expected do
        throw (IO.userError s!"exact E boundary query mismatch: depth={t.depth} right={r}")
  match t,s with
  | .node _ _ l r,.node _ _ a b =>
      let left ← auditVersion w g l a
      let right ← auditVersion w g r b
      pure (left+right+1)
  | .leaf _,.leaf _ => pure 1
  | _,_ => throw (IO.userError "version topology differs from constructed trie")

def auditAt (w : Word (Fin 2)) (g : Nat) (hg : g≤w.length) : IO Nat := do
  let idx := FixedEnd.build colorDFA suffixDFA w 0 g hg
  auditVersion w g idx.trie.tree idx.versions

def main : IO Unit := do
  let w : Word (Fin 2) := (List.range 32).map fun i=>⟨(i/3+i)%2,by omega⟩
  let middle ← auditAt w 12 (by simp only [w,List.length_map,List.length_range]; omega)
  let atZero ← auditAt w 0 (Nat.zero_le _)
  let terminal ← auditAt w w.length (Nat.le_refl _)
  let empty ← auditAt [] 0 (Nat.le_refl _)
  let large : Word (Fin 2) := (List.range 512).map fun i=>⟨(i/3+i)%2,by omega⟩
  let idx := FixedEnd.build colorDFA suffixDFA large 0 256
    (by simp only [large,List.length_map,List.length_range]; omega)
  let root := Versions.root idx.versions
  unless root.totalMass == 514 && root.state.cachedSize == 257 && idx.trie.tree.nodes == 1027 do
    throw (IO.userError "large fixed-end construction lost records")
  let before := (FixedEnd.query suffixDFA (fun _=>true) idx.versions 255).1
  let atGrid := (FixedEnd.query suffixDFA (fun _=>true) idx.versions 256).1
  let atEnd := (FixedEnd.query suffixDFA (fun _=>true) idx.versions 512).1
  unless !before && atGrid && atEnd do throw (IO.userError "large endpoint query mismatch")
  IO.println s!"auditedVersions={middle+atZero+terminal+empty} exactLocalQueries=true emptyAndTerminal=true totalMass={root.totalMass} targets={root.state.cachedSize} nodes={idx.trie.tree.nodes} transfers={root.transfers} work={idx.work}"
