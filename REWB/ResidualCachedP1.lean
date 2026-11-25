import REWB.ResidualCachedVariants

/-! Actual finite P1 boundary-cache bank. All-start inputs are finite
vectors, shared across splice/final-subset variants with the same G
initial state. Their production is an explicit separate obligation.
Every cache and its compiled variant machines are retained in the bank;
the online path only reads them. -/
namespace REWB.ResidualCached.P1
open REWB.BoundaryRange REWB.BoundaryApplication
variable {σ : Nat}

abbrev Inputs (P : SevenDFA (Fin σ)) (n width : Nat) :=
  Vector (BoundaryRange.Cache.Inputs P.G n width) P.G.stateCount

def Ready (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (width : Nat)
    (bits : Inputs P w.length width) : Prop :=
  ∀g,BoundaryRange.Cache.Ready P.A P.B P.C (gap P g) P.D w width (bits.get g)

structure Cell (P : SevenDFA (Fin σ)) (w : Word (Fin σ))
    (g q : Fin P.G.stateCount) (c : TableColor.Key P.H) where
  middle : DFA (Fin σ)
  middle_eq : middle=gap P g
  last : DFA (Fin σ)
  last_eq : last=suffix P q c
  cache : BoundaryRange.Cache.Index P.A P.B P.C middle P.D last w
  work : Nat

def buildCell (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width)
    (g q : Fin P.G.stateCount) (c : TableColor.Key P.H) : Cell P w g q c :=
  let middle:=gap P g
  let last:=suffix P q c
  let cache:=BoundaryRange.Cache.build P.A P.B P.C middle P.D last w fallback width hw (bits.get g)
  ⟨middle,rfl,last,rfl,cache,cache.work+5⟩

def Cell.query {P : SevenDFA (Fin σ)} {w : Word (Fin σ)}
    {g q : Fin P.G.stateCount} {c : TableColor.Key P.H}
    (cell : Cell P w g q c) (left right : Nat) : Bool×Nat :=
  BoundaryRange.Cache.query cell.cache left right

structure Index (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) where
  selectors : Selectors P w
  cells : Table.Index fun g : Fin P.G.stateCount=>
    Table.Index fun q : Fin P.G.stateCount=>
      Table.Index fun c : TableColor.Key P.H=>Cell P w g q c
  work : Nat

def build (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width) : Index P w :=
  let selectors:=prepareSelectors P w
  let cells:=Table.build fun g : Fin P.G.stateCount=>
    let row:=Table.build fun q : Fin P.G.stateCount=>
      let tail:=Table.build fun c : TableColor.Key P.H=>
        let cell:=buildCell P w fallback width hw bits g q c
        (cell,cell.work)
      (tail,tail.work)
    (row,row.work)
  ⟨selectors,cells,selectors.work+cells.work+4⟩

@[simp] theorem build_cell (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width)
    (g q : Fin P.G.stateCount) (c : TableColor.Key P.H) :
    Table.get (Table.get (Table.get (build P w fallback width hw bits).cells g) q) c=
      buildCell P w fallback width hw bits g q c := by
  simp only [build,Table.get_build]

def queryState {P : SevenDFA (Fin σ)} {w : Word (Fin σ)} (idx : Index P w)
    (choice : Choice P) (left right : Nat) (q : Fin P.G.stateCount) : Bool×Nat :=
  let g:=choice.middle.get q
  let cell:=Table.get (Table.get (Table.get idx.cells g) q) choice.tailKey
  let out:=cell.query left right
  (out.1,out.2+5)

def query {P : SevenDFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index P w) (window : IndexedGrid.Strip) : Bool×Nat :=
  let choice:=select idx.selectors window.lo window.hi window.distance
  let out:=any (queryState idx choice window.lo window.hi) idx.selectors.states
  (out.1,choice.work+out.2+3)

theorem queryState_correct (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width) (ready : Ready P w width bits)
    (choice : Choice P) (left right : Nat) (q : Fin P.G.stateCount) :
    (queryState (build P w fallback width hw bits) choice left right q).1=true ↔
      Spec.boundaryRange P.A P.B P.C (gap P (choice.middle.get q)) P.D
        (suffix P q choice.tailKey) w left right := by
  unfold queryState
  dsimp only
  rw [build_cell]
  change (BoundaryRange.Cache.query
    (BoundaryRange.Cache.build P.A P.B P.C (gap P (choice.middle.get q)) P.D
      (suffix P q choice.tailKey) w fallback width hw (bits.get (choice.middle.get q))) left right).1=true ↔ _
  exact BoundaryRange.Cache.query_correct P.A P.B P.C (gap P (choice.middle.get q)) P.D
    (suffix P q choice.tailKey) w fallback width hw (bits.get (choice.middle.get q))
    (ready (choice.middle.get q)) left right

theorem query_correct (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width) (ready : Ready P w width bits)
    (window : IndexedGrid.Strip) :
    (query (build P w fallback width hw bits) window).1=true ↔
      ResidualDispatch.P1Query P w window := by
  unfold query
  change (any (queryState (build P w fallback width hw bits)
    (select (prepareSelectors P w) window.lo window.hi window.distance) window.lo window.hi)
    (List.finRange P.G.stateCount)).1=true ↔ _
  rw [any_correct]
  simp only [List.finRange,List.mem_ofFn,exists_eq,true_and,queryState_correct P w fallback width hw bits ready,
    select_gap,select_suffix]
  rfl

def cellBudget (P : SevenDFA (Fin σ)) (n width : Nat)
    (g q : Fin P.G.stateCount) (c : TableColor.Key P.H) : Nat :=
  BoundaryRange.Cache.buildBudget P.A P.B P.C (gap P g) P.D (suffix P q c) n width+5

def tailBudget (P : SevenDFA (Fin σ)) (n width : Nat) (g q : Fin P.G.stateCount) : Nat :=
  (List.ofFn fun c : TableColor.Key P.H=>cellBudget P n width g q c+3).sum+1

def rowBudget (P : SevenDFA (Fin σ)) (n width : Nat) (g : Fin P.G.stateCount) : Nat :=
  (List.ofFn fun q : Fin P.G.stateCount=>tailBudget P n width g q+3).sum+1

def buildBudget (P : SevenDFA (Fin σ)) (n width : Nat) : Nat :=
  selectorBuildBudget P n+(List.ofFn fun g : Fin P.G.stateCount=>rowBudget P n width g+3).sum+1+4

theorem build_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width) :
    (build P w fallback width hw bits).work≤buildBudget P w.length width := by
  have hc : (build P w fallback width hw bits).cells.work≤
      (List.ofFn fun g : Fin P.G.stateCount=>rowBudget P w.length width g+3).sum+1 := by
    apply Table.build_work_mono
    intro g
    apply Table.build_work_mono
    intro q
    apply Table.build_work_mono
    intro c
    have hh:=BoundaryRange.Cache.build_work P.A P.B P.C (gap P g) P.D
      (suffix P q c) w fallback width hw (bits.get g)
    exact Nat.add_le_add_right hh 5
  change (prepareSelectors P w).work+(build P w fallback width hw bits).cells.work+4≤_
  rw [prepareSelectors_work]
  unfold buildBudget
  omega

def allQueryBudget (P : SevenDFA (Fin σ)) (n width : Nat) : Nat :=
  (List.ofFn fun g : Fin P.G.stateCount=>
    (List.ofFn fun q : Fin P.G.stateCount=>
      (List.ofFn fun c : TableColor.Key P.H=>
        BoundaryRange.Cache.queryBudget P.A P.B P.C (gap P g) P.D (suffix P q c) n width).sum).sum).sum

theorem cell_query_budget (P : SevenDFA (Fin σ)) (n width : Nat)
    (g q : Fin P.G.stateCount) (c : TableColor.Key P.H) :
    BoundaryRange.Cache.queryBudget P.A P.B P.C (gap P g) P.D (suffix P q c) n width≤
      allQueryBudget P n width := by
  let f:=fun g q c=>BoundaryRange.Cache.queryBudget P.A P.B P.C (gap P g) P.D (suffix P q c) n width
  have hc:=ofFn_le_sum (f g q) c
  have hq:=ofFn_le_sum (fun q=>(List.ofFn (f g q)).sum) q
  have hg:=ofFn_le_sum (fun g=>(List.ofFn fun q=>(List.ofFn (f g q)).sum).sum) g
  exact Nat.le_trans hc (Nat.le_trans hq hg)

theorem queryState_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width)
    (choice : Choice P) (left right : Nat) (q : Fin P.G.stateCount) :
    (queryState (build P w fallback width hw bits) choice left right q).2≤
      allQueryBudget P w.length width+5 := by
  have hh:=BoundaryRange.Cache.query_work P.A P.B P.C (gap P (choice.middle.get q)) P.D
    (suffix P q choice.tailKey) w fallback width hw (bits.get (choice.middle.get q)) left right
  have hb:=cell_query_budget P w.length width (choice.middle.get q) q choice.tailKey
  unfold queryState
  dsimp only
  rw [build_cell]
  change (BoundaryRange.Cache.query
    (BoundaryRange.Cache.build P.A P.B P.C (gap P (choice.middle.get q)) P.D
      (suffix P q choice.tailKey) w fallback width hw (bits.get (choice.middle.get q))) left right).2+5≤_
  omega

def queryBudget (P : SevenDFA (Fin σ)) (n width : Nat) : Nat :=
  selectorBudget P n+P.G.stateCount*(allQueryBudget P n width+8)+4

theorem query_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs P w.length width)
    (window : IndexedGrid.Strip) (h : ResidualSeparated.Window w window.lo window.hi window.distance) :
    (query (build P w fallback width hw bits) window).2≤queryBudget P w.length width := by
  have hs:=select_work P w window.lo window.hi window.distance h
  have hq:=any_work (queryState (build P w fallback width hw bits)
      (select (prepareSelectors P w) window.lo window.hi window.distance) window.lo window.hi)
      (List.finRange P.G.stateCount) (allQueryBudget P w.length width+5)
      (fun q _=>queryState_work P w fallback width hw bits _ _ _ q)
  simp only [List.length_finRange,Nat.add_assoc,Nat.reduceAdd] at hq
  change (select (prepareSelectors P w) window.lo window.hi window.distance).work+
    (any (queryState (build P w fallback width hw bits)
      (select (prepareSelectors P w) window.lo window.hi window.distance) window.lo window.hi)
      (List.finRange P.G.stateCount)).2+3≤_
  unfold queryBudget
  omega

end REWB.ResidualCached.P1
