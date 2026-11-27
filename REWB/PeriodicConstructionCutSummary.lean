import REWB.PeriodicConstructionCutTable

/-! Concrete finite loops for strict-cut products and inclusive cut-window
transport. All tables are stored lists, and each lookup traverses the
stored list through the counted reader. No composed relation closure is
retained in the output. -/
namespace REWB.PeriodicConstruction.Cut
open REWB.FiniteRelation
variable {M : Type} [DecidableEq M] {o : RangeProducts.Ops M} {e : Enumeration M}

def summaryOne (k : Primitives o) (u : Universe e) : Result (MaskedCut.Summary e) :=
  let id:=k.unit
  let cells:=table u (fun _ _=>(false,1))
  (⟨id.1,cells.1⟩,id.2+cells.2+2)

theorem summaryOne_value (k : Primitives o) (u : Universe e) :
    (summaryOne k u).1=MaskedCut.one o e := by
  simp only [summaryOne,table_value,k.unit_value,MaskedCut.one]

def oneCost (N C : Nat) : Nat := C+tableCost N 1+2

theorem summaryOne_work (k : Primitives o) (u : Universe e) (C : Nat)
    (hc : k.unit.2≤C) : (summaryOne k u).2≤oneCost e.elems.length C := by
  have ht:=table_work u (fun _ _=>(false,1)) 1 (fun _ _=>Nat.le_refl _)
  dsimp only [summaryOne,oneCost]
  omega

def summaryAtom (k : Primitives o) (u : Universe e) (x : M) : Result (MaskedCut.Summary e) :=
  let id:=k.unit
  let cells:=table u (fun p s=>
    let a:=k.equal p id.1
    let b:=k.equal s x
    (a.1 && b.1,a.2+b.2+2))
  (⟨x,cells.1⟩,id.2+cells.2+2)

theorem summaryAtom_value (k : Primitives o) (u : Universe e) (x : M) :
    (summaryAtom k u x).1=MaskedCut.atom o e x := by
  simp only [summaryAtom,table_value,k.unit_value,k.equal_value,MaskedCut.atom,Bool.decide_and]

def atomCost (N C : Nat) : Nat := C+tableCost N (2*C+2)+2

theorem summaryAtom_work (k : Primitives o) (u : Universe e) (x : M) (C : Nat)
    (hu : k.unit.2≤C) (he : ∀a b,(k.equal a b).2≤C) :
    (summaryAtom k u x).2≤atomCost e.elems.length C := by
  have ht:=table_work u (fun p s=>
    let a:=k.equal p k.unit.1
    let b:=k.equal s x
    (a.1 && b.1,a.2+b.2+2)) (2*C+2) (by
      intro p s
      have h1:=he p k.unit.1
      have h2:=he s x
      dsimp only
      omega)
  dsimp only at ht
  dsimp only [summaryAtom,atomCost]
  omega

def leftCell (k : Primitives o) (a b : MaskedCut.Summary e) (p s t : M) : Result Bool :=
  let r:=read k a.cuts p t
  let m:=k.multiply t b.total
  let eq:=k.equal m.1 s
  (r.1 && eq.1,r.2+m.2+eq.2+3)

def rightCell (k : Primitives o) (a b : MaskedCut.Summary e) (p s t : M) : Result Bool :=
  let r:=read k b.cuts t s
  let m:=k.multiply a.total t
  let eq:=k.equal m.1 p
  (r.1 && eq.1,r.2+m.2+eq.2+3)

def summaryMul (k : Primitives o) (u : Universe e) (a b : MaskedCut.Summary e) :
    Result (MaskedCut.Summary e) :=
  let total:=k.multiply a.total b.total
  let cells:=table u (fun p s=>
    let l:=finiteAny u (leftCell k a b p s)
    let r:=finiteAny u (rightCell k a b p s)
    (l.1 || r.1,l.2+r.2+2))
  (⟨total.1,cells.1⟩,total.2+cells.2+2)

theorem summaryMul_value (k : Primitives o) (u : Universe e) (a b : MaskedCut.Summary e) :
    (summaryMul k u a b).1=MaskedCut.mul o e a b := by
  simp only [summaryMul,table_value,finiteAny_value,leftCell,rightCell,read_value,
    k.multiply_value,k.equal_value,MaskedCut.mul,MaskedCut.relation]

def sideCost (N C : Nat) : Nat := readCost N C+2*C+3
def mulCellCost (N C : Nat) : Nat := 2*(N*(sideCost N C+2)+1)+2
def mulCost (N C : Nat) : Nat := C+tableCost N (mulCellCost N C)+2

theorem leftCell_work (k : Primitives o) (a b : MaskedCut.Summary e) (p s t : M)
    (C : Nat) (hm : ∀x y,(k.multiply x y).2≤C) (he : ∀x y,(k.equal x y).2≤C) :
    (leftCell k a b p s t).2≤sideCost e.elems.length C := by
  have hr:=read_work k a.cuts p t C he
  have hmul:=hm t b.total
  have heq:=he (k.multiply t b.total).1 s
  dsimp only [leftCell,sideCost]
  omega

theorem rightCell_work (k : Primitives o) (a b : MaskedCut.Summary e) (p s t : M)
    (C : Nat) (hm : ∀x y,(k.multiply x y).2≤C) (he : ∀x y,(k.equal x y).2≤C) :
    (rightCell k a b p s t).2≤sideCost e.elems.length C := by
  have hr:=read_work k b.cuts t s C he
  have hmul:=hm a.total t
  have heq:=he (k.multiply a.total t).1 p
  dsimp only [rightCell,sideCost]
  omega

theorem summaryMul_work (k : Primitives o) (u : Universe e) (a b : MaskedCut.Summary e)
    (C : Nat) (hm : ∀x y,(k.multiply x y).2≤C) (he : ∀x y,(k.equal x y).2≤C) :
    (summaryMul k u a b).2≤mulCost e.elems.length C := by
  have ht:=table_work u (fun p s=>
    let l:=finiteAny u (leftCell k a b p s)
    let r:=finiteAny u (rightCell k a b p s)
    (l.1 || r.1,l.2+r.2+2)) (mulCellCost e.elems.length C) (by
      intro p s
      have hl:=finiteAny_work u (leftCell k a b p s) (sideCost e.elems.length C)
        (fun t=>leftCell_work k a b p s t C hm he)
      have hr:=finiteAny_work u (rightCell k a b p s) (sideCost e.elems.length C)
        (fun t=>rightCell_work k a b p s t C hm he)
      dsimp only [mulCellCost]
      omega)
  have hmul:=hm a.total b.total
  dsimp only at ht
  dsimp only [summaryMul,mulCost]
  omega

def closed (k : Primitives o) (a : MaskedCut.Summary e) (p s : M) : Result Bool :=
  let r:=read k a.cuts p s
  let id:=k.unit
  let ep:=k.equal p a.total
  let es:=k.equal s id.1
  (r.1 || (ep.1 && es.1),r.2+id.2+ep.2+es.2+4)

theorem closed_value (k : Primitives o) (a : MaskedCut.Summary e) (p s : M) :
    (closed k a p s).1=MaskedCut.closed o a p s := by
  simp only [closed,read_value,k.unit_value,k.equal_value,MaskedCut.closed,
    MaskedCut.relation,Bool.decide_and]

def closedCost (N C : Nat) : Nat := readCost N C+3*C+4

theorem closed_work (k : Primitives o) (a : MaskedCut.Summary e) (p s : M)
    (C : Nat) (hu : k.unit.2≤C) (he : ∀x y,(k.equal x y).2≤C) :
    (closed k a p s).2≤closedCost e.elems.length C := by
  have hr:=read_work k a.cuts p s C he
  have hp:=he p a.total
  have hs:=he s k.unit.1
  dsimp only [closed,closedCost]
  omega

def transport (k : Primitives o) (left middle right : MaskedCut.Summary e)
    (p s u v : M) : Result Bool :=
  let cut:=closed k middle u v
  let before:=k.multiply left.total u
  let after:=k.multiply v right.total
  let ep:=k.equal before.1 p
  let es:=k.equal after.1 s
  (cut.1 && (ep.1 && es.1),cut.2+before.2+after.2+ep.2+es.2+5)

def window (k : Primitives o) (u : Universe e) (left middle right : MaskedCut.Summary e) :
    Result (MatrixTable.Matrix e) :=
  table u (fun p s=>finiteAny u (fun a=>finiteAny u (transport k left middle right p s a)))

theorem window_value (k : Primitives o) (u : Universe e) (left middle right : MaskedCut.Summary e) :
    (window k u left middle right).1=MaskedCut.Index.window o e left middle right := by
  simp only [window,table_value,finiteAny_value,transport,closed_value,
    k.multiply_value,k.equal_value,MaskedCut.Index.window,Bool.decide_and]

def transportCost (N C : Nat) : Nat := closedCost N C+4*C+5
def windowCost (N C : Nat) : Nat := tableCost N (N*(N*(transportCost N C+2)+3)+1)

theorem transport_work (k : Primitives o) (left middle right : MaskedCut.Summary e)
    (p s u v : M) (C : Nat) (hu : k.unit.2≤C)
    (hm : ∀x y,(k.multiply x y).2≤C) (he : ∀x y,(k.equal x y).2≤C) :
    (transport k left middle right p s u v).2≤transportCost e.elems.length C := by
  have hc:=closed_work k middle u v C hu he
  have hb:=hm left.total u
  have ha:=hm v right.total
  have hp:=he (k.multiply left.total u).1 p
  have hs:=he (k.multiply v right.total).1 s
  dsimp only [transport,transportCost]
  omega

theorem window_work (k : Primitives o) (u : Universe e) (left middle right : MaskedCut.Summary e)
    (C : Nat) (hu : k.unit.2≤C)
    (hm : ∀x y,(k.multiply x y).2≤C) (he : ∀x y,(k.equal x y).2≤C) :
    (window k u left middle right).2≤windowCost e.elems.length C := by
  apply table_work
  intro p s
  apply finiteAny_work
  intro a
  exact finiteAny_work u (transport k left middle right p s a) (transportCost e.elems.length C)
    (fun v=>transport_work k left middle right p s a v C hu hm he)

end REWB.PeriodicConstruction.Cut
