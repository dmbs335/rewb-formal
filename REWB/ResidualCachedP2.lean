import REWB.ResidualCachedVariants

/-! Actual finite P2 one-use-cache bank. Forward all-start rows depend
only on the suffix variant; reverse rows depend only on the prefix
variant. Both are retained finite tables. Query selection uses shared
A/G/H maps and cached machines, and preserves the one-use source lower
bound. Input-row production remains explicit in `Ready`. -/
namespace REWB.ResidualCached.P2
open REWB.BoundaryRange REWB.BoundaryApplication
variable {σ : Nat}

structure Inputs (P : SevenDFA (Fin σ)) (n width : Nat) where
  forward : Table.Index fun q : Fin P.G.stateCount=>
    Table.Index fun c : TableColor.Key P.H=>OneUseRange.Cache.Inputs (suffix P q c) n width
  backward : Table.Index fun a : Fin P.A.stateCount=>
    Table.Index fun g : Fin P.G.stateCount=>
      OneUseRange.Cache.Inputs (Automata.reverse (front P a g)) n width

def Ready (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (width : Nat)
    (bits : Inputs P w.length width) : Prop :=
  ∀a g q c,OneUseRange.Cache.Ready (front P a g) P.C P.D (suffix P q c) w width
    (Table.get (Table.get bits.forward q) c) (Table.get (Table.get bits.backward a) g)

structure Cell (P : SevenDFA (Fin σ)) (w : Word (Fin σ))
    (a : Fin P.A.stateCount) (g q : Fin P.G.stateCount) (c : TableColor.Key P.H) where
  first : DFA (Fin σ)
  first_eq : first=front P a g
  last : DFA (Fin σ)
  last_eq : last=suffix P q c
  cache : OneUseRange.Cache.Index first P.C P.D last w
  work : Nat

def buildCell (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width)
    (a : Fin P.A.stateCount) (g q : Fin P.G.stateCount) (c : TableColor.Key P.H) : Cell P w a g q c :=
  let first:=front P a g
  let last:=suffix P q c
  let cache:=OneUseRange.Cache.build first P.C P.D last w fallback width hw
    (Table.get (Table.get bits.forward q) c) (Table.get (Table.get bits.backward a) g)
  ⟨first,rfl,last,rfl,cache,cache.work+8⟩

def Cell.query {P : SevenDFA (Fin σ)} {w : Word (Fin σ)}
    {a : Fin P.A.stateCount} {g q : Fin P.G.stateCount} {c : TableColor.Key P.H}
    (cell : Cell P w a g q c) (left right : Nat) : Bool×Nat :=
  OneUseRange.Cache.query cell.cache left right

structure Index (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) where
  selectors : Selectors P w
  cells : Table.Index fun a : Fin P.A.stateCount=>
    Table.Index fun g : Fin P.G.stateCount=>
      Table.Index fun q : Fin P.G.stateCount=>
        Table.Index fun c : TableColor.Key P.H=>Cell P w a g q c
  work : Nat

def build (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width) : Index P w :=
  let selectors:=prepareSelectors P w
  let cells:=Table.build fun a : Fin P.A.stateCount=>
    let block:=Table.build fun g : Fin P.G.stateCount=>
      let row:=Table.build fun q : Fin P.G.stateCount=>
        let tail:=Table.build fun c : TableColor.Key P.H=>
          let cell:=buildCell P w fallback width hw bits a g q c
          (cell,cell.work)
        (tail,tail.work)
      (row,row.work)
    (block,block.work)
  ⟨selectors,cells,selectors.work+cells.work+4⟩

@[simp] theorem build_cell (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width)
    (a : Fin P.A.stateCount) (g q : Fin P.G.stateCount) (c : TableColor.Key P.H) :
    Table.get (Table.get (Table.get (Table.get (build P w fallback width hw bits).cells a) g) q) c=
      buildCell P w fallback width hw bits a g q c := by
  simp only [build,Table.get_build]

def queryState {P : SevenDFA (Fin σ)} {w : Word (Fin σ)} (idx : Index P w)
    (choice : Choice P) (left right : Nat) (q : Fin P.G.stateCount) : Bool×Nat :=
  let g:=choice.middle.get q
  let cell:=Table.get (Table.get (Table.get (Table.get idx.cells choice.initial) g) q) choice.tailKey
  let out:=cell.query left right
  (out.1,out.2+6)

def query {P : SevenDFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index P w) (window : IndexedGrid.Strip) : Bool×Nat :=
  let choice:=select idx.selectors window.lo window.hi window.distance
  let out:=any (queryState idx choice window.lo window.hi) idx.selectors.states
  (out.1,choice.work+out.2+3)

theorem queryState_correct (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width) (ready : Ready P w width bits)
    (choice : Choice P) (left right : Nat) (q : Fin P.G.stateCount) :
    (queryState (build P w fallback width hw bits) choice left right q).1=true ↔
      Spec.oneUseRange (front P choice.initial (choice.middle.get q)) P.C P.D
        (suffix P q choice.tailKey) w left right := by
  unfold queryState
  dsimp only
  rw [build_cell]
  change (OneUseRange.Cache.query
    (OneUseRange.Cache.build (front P choice.initial (choice.middle.get q)) P.C P.D
      (suffix P q choice.tailKey) w fallback width hw
      (Table.get (Table.get bits.forward q) choice.tailKey)
      (Table.get (Table.get bits.backward choice.initial) (choice.middle.get q))) left right).1=true ↔ _
  exact OneUseRange.Cache.query_correct (front P choice.initial (choice.middle.get q)) P.C P.D
    (suffix P q choice.tailKey) w fallback width hw
    (Table.get (Table.get bits.forward q) choice.tailKey)
    (Table.get (Table.get bits.backward choice.initial) (choice.middle.get q))
    (ready _ _ _ _) left right

theorem query_correct (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width) (ready : Ready P w width bits)
    (window : IndexedGrid.Strip) :
    (query (build P w fallback width hw bits) window).1=true ↔
      ResidualDispatch.P2Query P w window := by
  unfold query
  change (any (queryState (build P w fallback width hw bits)
    (select (prepareSelectors P w) window.lo window.hi window.distance) window.lo window.hi)
    (List.finRange P.G.stateCount)).1=true ↔ _
  rw [any_correct]
  simp only [List.finRange,List.mem_ofFn,exists_eq,true_and,queryState_correct P w fallback width hw bits ready,
    select_front,select_suffix]
  rfl

def cellBudget (P : SevenDFA (Fin σ)) (n width : Nat)
    (a : Fin P.A.stateCount) (g q : Fin P.G.stateCount) (c : TableColor.Key P.H) : Nat :=
  OneUseRange.Cache.buildBudget (front P a g) P.C P.D (suffix P q c) n width+8

def tailBudget (P : SevenDFA (Fin σ)) (n width : Nat)
    (a : Fin P.A.stateCount) (g q : Fin P.G.stateCount) : Nat :=
  (List.ofFn fun c : TableColor.Key P.H=>cellBudget P n width a g q c+3).sum+1

def rowBudget (P : SevenDFA (Fin σ)) (n width : Nat) (a : Fin P.A.stateCount)
    (g : Fin P.G.stateCount) : Nat :=
  (List.ofFn fun q : Fin P.G.stateCount=>tailBudget P n width a g q+3).sum+1

def blockBudget (P : SevenDFA (Fin σ)) (n width : Nat) (a : Fin P.A.stateCount) : Nat :=
  (List.ofFn fun g : Fin P.G.stateCount=>rowBudget P n width a g+3).sum+1

def buildBudget (P : SevenDFA (Fin σ)) (n width : Nat) : Nat :=
  selectorBuildBudget P n+(List.ofFn fun a : Fin P.A.stateCount=>blockBudget P n width a+3).sum+1+4

theorem build_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width) :
    (build P w fallback width hw bits).work≤buildBudget P w.length width := by
  have hc : (build P w fallback width hw bits).cells.work≤
      (List.ofFn fun a : Fin P.A.stateCount=>blockBudget P w.length width a+3).sum+1 := by
    apply Table.build_work_mono
    intro a
    apply Table.build_work_mono
    intro g
    apply Table.build_work_mono
    intro q
    apply Table.build_work_mono
    intro c
    have hh:=OneUseRange.Cache.build_work (front P a g) P.C P.D (suffix P q c)
      w fallback width hw (Table.get (Table.get bits.forward q) c) (Table.get (Table.get bits.backward a) g)
    exact Nat.add_le_add_right hh 8
  change (prepareSelectors P w).work+(build P w fallback width hw bits).cells.work+4≤_
  rw [prepareSelectors_work]
  unfold buildBudget
  omega

def allQueryBudget (P : SevenDFA (Fin σ)) (n width : Nat) : Nat :=
  (List.ofFn fun a : Fin P.A.stateCount=>
    (List.ofFn fun g : Fin P.G.stateCount=>
      (List.ofFn fun q : Fin P.G.stateCount=>
        (List.ofFn fun c : TableColor.Key P.H=>
          OneUseRange.Cache.queryBudget (front P a g) P.C P.D (suffix P q c) n width).sum).sum).sum).sum

theorem cell_query_budget (P : SevenDFA (Fin σ)) (n width : Nat)
    (a : Fin P.A.stateCount) (g q : Fin P.G.stateCount) (c : TableColor.Key P.H) :
    OneUseRange.Cache.queryBudget (front P a g) P.C P.D (suffix P q c) n width≤
      allQueryBudget P n width := by
  let f:=fun a g q c=>OneUseRange.Cache.queryBudget (front P a g) P.C P.D (suffix P q c) n width
  have hc:=ofFn_le_sum (f a g q) c
  have hq:=ofFn_le_sum (fun q=>(List.ofFn (f a g q)).sum) q
  have hg:=ofFn_le_sum (fun g=>(List.ofFn fun q=>(List.ofFn (f a g q)).sum).sum) g
  have ha:=ofFn_le_sum (fun a=>(List.ofFn fun g=>(List.ofFn fun q=>(List.ofFn (f a g q)).sum).sum).sum) a
  exact Nat.le_trans hc (Nat.le_trans hq (Nat.le_trans hg ha))

theorem queryState_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width)
    (choice : Choice P) (left right : Nat) (q : Fin P.G.stateCount) :
    (queryState (build P w fallback width hw bits) choice left right q).2≤
      allQueryBudget P w.length width+6 := by
  have hh:=OneUseRange.Cache.query_work (front P choice.initial (choice.middle.get q)) P.C P.D
    (suffix P q choice.tailKey) w fallback width hw
    (Table.get (Table.get bits.forward q) choice.tailKey)
    (Table.get (Table.get bits.backward choice.initial) (choice.middle.get q)) left right
  have hb:=cell_query_budget P w.length width choice.initial (choice.middle.get q) q choice.tailKey
  unfold queryState
  dsimp only
  rw [build_cell]
  change (OneUseRange.Cache.query
    (OneUseRange.Cache.build (front P choice.initial (choice.middle.get q)) P.C P.D
      (suffix P q choice.tailKey) w fallback width hw
      (Table.get (Table.get bits.forward q) choice.tailKey)
      (Table.get (Table.get bits.backward choice.initial) (choice.middle.get q))) left right).2+6≤_
  omega

def queryBudget (P : SevenDFA (Fin σ)) (n width : Nat) : Nat :=
  selectorBudget P n+P.G.stateCount*(allQueryBudget P n width+9)+4

theorem query_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width)
    (window : IndexedGrid.Strip) (h : ResidualSeparated.Window w window.lo window.hi window.distance) :
    (query (build P w fallback width hw bits) window).2≤queryBudget P w.length width := by
  have hs:=select_work P w window.lo window.hi window.distance h
  have hq:=any_work (queryState (build P w fallback width hw bits)
      (select (prepareSelectors P w) window.lo window.hi window.distance) window.lo window.hi)
      (List.finRange P.G.stateCount) (allQueryBudget P w.length width+6)
      (fun q _=>queryState_work P w fallback width hw bits _ _ _ q)
  simp only [List.length_finRange,Nat.add_assoc,Nat.reduceAdd] at hq
  change (select (prepareSelectors P w) window.lo window.hi window.distance).work+
    (any (queryState (build P w fallback width hw bits)
      (select (prepareSelectors P w) window.lo window.hi window.distance) window.lo window.hi)
      (List.finRange P.G.stateCount)).2+3≤_
  unfold queryBudget
  omega

end REWB.ResidualCached.P2
