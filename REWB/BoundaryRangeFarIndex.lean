import REWB.BoundaryRangeFar
import REWB.BoundaryRangeTable

/-! An eager finite family for the far-left block case. Every C/K state
variant is built once at the fixed grid boundary. An online query reads
the K state from one shared range index, then queries the cached C rows.
There is no per-query trie construction or boundary-length scan. -/
namespace REWB.BoundaryRange.FarLeft
open REWB.BoundaryApplication
variable {σ : Nat}

abbrev Row (C E : DFA (Fin σ)) (w : Word (Fin σ)) :=
  Table.Index (fun _ : Fin C.stateCount=>Separated.Index E w)

structure Index (C K E : DFA (Fin σ)) (w : Word (Fin σ)) where
  rows : Table.Index (fun _ : Fin K.stateCount=>Row C E w)
  kranges : Range.Index K
  grid : Nat
  cachedLength : Nat
  work : Nat

def buildRow (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (k : Fin K.stateCount) : Row C E w :=
  Table.build fun c=>
    let idx:=Separated.build A B (Automata.stop C c) (Automata.gap C K D c k) E w fallback g g hg
    (idx,idx.work)

def build (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) : Index C K E w :=
  let rows:=Table.build fun k=>
    let row:=buildRow A B C K D E w fallback g hg k
    (row,row.work)
  let kranges:=Range.build K w
  ⟨rows,kranges,g,w.length,
    rows.work+K.stateCount*kranges.products+kranges.letterCells+w.length+4⟩

def scan (E : DFA (Fin σ)) (rows : Row C E w) (right : Nat) : List (Fin C.stateCount)→Bool×Nat
  | [] => (false,1)
  | c::cs =>
    let cell:=Table.get rows c
    let answer:=Separated.query E cell right
    let rest:=scan E rows right cs
    (answer.1 || rest.1,answer.2+rest.2+6)

theorem scan_correct (E : DFA (Fin σ)) (rows : Row C E w) (right : Nat)
    (cs : List (Fin C.stateCount)) :
    (scan E rows right cs).1=true ↔
      ∃c,c∈cs ∧ (Separated.query E (Table.get rows c) right).1=true := by
  induction cs with
  | nil => simp [scan]
  | cons c cs ih =>
    simp only [scan,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (hc|⟨d,hd,hv⟩)
      · exact ⟨c,Or.inl rfl,hc⟩
      · exact ⟨d,Or.inr hd,hv⟩
    · rintro ⟨d,(rfl|hd),hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨d,hd,hv⟩

def query (K E : DFA (Fin σ)) (idx : Index C K E w) (left right : Nat) : Bool×Nat :=
  if left≤idx.grid ∧ right≤idx.cachedLength then
    let pre:=Range.query K idx.kranges left idx.grid
    let row:=Table.get idx.rows (pre.map.get K.initial)
    let answer:=scan E row right (List.ofFn (fun c : Fin C.stateCount=>c))
    (answer.1,pre.work+answer.2+2*C.stateCount+7)
  else (false,4)

theorem build_get (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (k : Fin K.stateCount) (c : Fin C.stateCount) :
    Table.get (Table.get (build A B C K D E w fallback g hg).rows k) c=
      Separated.build A B (Automata.stop C c) (Automata.gap C K D c k) E w fallback g g hg := by
  simp only [build,buildRow,Table.get_build]

theorem query_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (left right g0 : Nat) (hlg : left≤g) (hr : right≤w.length) :
    (query K E (build A B C K D E w fallback g hg) left right).1=true ↔
      Case A B C K D E w left right g0 g .farLeft := by
  rw [farLeft_step A B C K D E w fallback left right g0 g hlg hg hr]
  unfold query
  change ((if left≤g ∧ right≤w.length then _ else _) : Bool×Nat).1=true ↔ _
  rw [if_pos ⟨hlg,hr⟩]
  dsimp only
  rw [scan_correct]
  simp only [List.mem_ofFn,exists_eq_right,and_true,true_and,build_get]
  constructor
  · rintro ⟨c,_,hc⟩
    exact ⟨c,hc⟩
  · rintro ⟨c,hc⟩
    exact ⟨c,⟨c,rfl⟩,hc⟩

def componentBudget (A B C K D E : DFA (Fin σ)) (n : Nat) : Nat :=
  (List.ofFn fun k : Fin K.stateCount=>
    (List.ofFn fun c : Fin C.stateCount=>
      Separated.bound A B (Automata.stop C c) (Automata.gap C K D c k) E n).sum).sum

private theorem le_sum (x : Nat) (xs : List Nat) (hx : x∈xs) : x≤xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl|hx
    · omega
    · have hh:=ih hx
      omega

theorem component_le (A B C K D E : DFA (Fin σ)) (n : Nat)
    (c : Fin C.stateCount) (k : Fin K.stateCount) :
    Separated.bound A B (Automata.stop C c) (Automata.gap C K D c k) E n≤
      componentBudget A B C K D E n := by
  have hc:=le_sum _ (List.ofFn fun c : Fin C.stateCount=>
    Separated.bound A B (Automata.stop C c) (Automata.gap C K D c k) E n)
    (List.mem_ofFn.mpr ⟨c,rfl⟩)
  have hk:=le_sum _ (List.ofFn fun k : Fin K.stateCount=>
    (List.ofFn fun c : Fin C.stateCount=>
      Separated.bound A B (Automata.stop C c) (Automata.gap C K D c k) E n).sum)
    (List.mem_ofFn.mpr ⟨k,rfl⟩)
  exact Nat.le_trans hc hk

theorem buildRow_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (k : Fin K.stateCount) :
    (buildRow A B C K D E w fallback g hg k).work≤
      C.stateCount*(componentBudget A B C K D E w.length+3)+1 := by
  apply Table.build_work_le
  intro c
  have hh:=Separated.build_work A B (Automata.stop C c) (Automata.gap C K D c k) E
    w fallback g g (Nat.le_refl _) hg
  exact Nat.le_trans hh (component_le A B C K D E w.length c k)

def buildBudget (A B C K D E : DFA (Fin σ)) (n : Nat) : Nat :=
  K.stateCount*(C.stateCount*(componentBudget A B C K D E n+3)+4)+1+
    K.stateCount*((n.log2+1)*n)+n*K.stateCount+n+4

theorem build_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) :
    (build A B C K D E w fallback g hg).work≤buildBudget A B C K D E w.length := by
  have ht:=Table.build_work_le (fun k : Fin K.stateCount=>
      (buildRow A B C K D E w fallback g hg k,(buildRow A B C K D E w fallback g hg k).work))
    (C.stateCount*(componentBudget A B C K D E w.length+3)+1)
    (fun k=>buildRow_work A B C K D E w fallback g hg k)
  simp only [Nat.add_assoc,Nat.reduceAdd] at ht
  unfold build
  dsimp only
  rw [Range.build_products]
  change _+K.stateCount*((w.length.log2+1)*w.length)+w.length*K.stateCount+w.length+4≤_
  unfold buildBudget
  omega

theorem scan_work (E : DFA (Fin σ)) (rows : Row C E w) (right bound : Nat)
    (cs : List (Fin C.stateCount))
    (hb : ∀c,c∈cs→(Separated.query E (Table.get rows c) right).2≤bound) :
    (scan E rows right cs).2≤cs.length*(bound+6)+1 := by
  induction cs with
  | nil => simp [scan]
  | cons c cs ih =>
    have hc:=hb c List.mem_cons_self
    have ht:=ih (fun d hd=>hb d (List.mem_cons_of_mem c hd))
    simp only [scan,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def suffixBudget (E : DFA (Fin σ)) (n : Nat) : Nat :=
  ((n+1).log2+2)*BoundaryIndex.Tree.queryBudget 1 E.stateCount+E.stateCount+2

def queryBudget (C K E : DFA (Fin σ)) (n : Nat) : Nat :=
  K.stateCount+8*(n.log2+2)+1+C.stateCount*(suffixBudget E n+8)+8

theorem query_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (left right : Nat) :
    (query K E (build A B C K D E w fallback g hg) left right).2≤queryBudget C K E w.length := by
  unfold query
  change ((if left≤g ∧ right≤w.length then _ else _) : Bool×Nat).2≤_
  split
  · rename_i h
    let k:=(Range.query K (Range.build K w) left g).map.get K.initial
    let rows:=Table.get (build A B C K D E w fallback g hg).rows k
    have hs:=scan_work E rows right (suffixBudget E w.length) (List.ofFn (fun c : Fin C.stateCount=>c))
      (by
        intro c _
        dsimp only [rows]
        rw [build_get]
        exact Separated.query_build_work A B (Automata.stop C c) (Automata.gap C K D c k) E
          w fallback g g hg right)
    rw [List.length_ofFn] at hs
    have hp:=Range.query_work K w left g h.1 hg
    change (Range.query K (Range.build K w) left g).work+
      (scan E rows right (List.ofFn (fun c : Fin C.stateCount=>c))).2+2*C.stateCount+7≤_
    unfold queryBudget
    simp only [Nat.mul_add] at hs ⊢
    omega
  · dsimp only
    unfold queryBudget
    omega

end REWB.BoundaryRange.FarLeft
