import REWB.BoundaryIndex

/-! Instrumented materialized-table primitives for the persistent boundary
index. Counters count written scalar cells and examined Boolean candidates.
The full scans deliberately retain every color/state candidate in the
counter, including when an earlier candidate already succeeded. DFA sizes
and the number of colors are fixed pattern parameters. -/
namespace REWB.BoundaryIndex.Counted
open REWB.FiniteRelation

variable {k m : Nat}

def scan {β : Type} (p : β→Bool) : List β→Bool×Nat
  | [] => (false,0)
  | x::xs =>
    let r := scan p xs
    (p x || r.1,r.2+1)

theorem scan_value {β : Type} (p : β→Bool) (xs : List β) :
    (scan p xs).1=xs.any p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [scan,List.any_cons,ih]

theorem scan_steps {β : Type} (p : β→Bool) (xs : List β) :
    (scan p xs).2=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [scan,List.length_cons,ih]

/-- Count a materialized row: each result includes its internal probe
count, and writing its scalar value contributes one additional cell. -/
def rowWork {n : Nat} {β : Type} (v : Vector (β×Nat) n) : Nat :=
  (List.ofFn (fun i=> (v.get i).2+1)).sum

theorem sum_ofFn_const (n c : Nat) : (List.ofFn (fun _ : Fin n=>c)).sum=n*c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons]
    simp only at ih
    change c+(List.ofFn (fun _ : Fin n=>c)).sum=(n+1)*c
    rw [ih,Nat.add_mul,Nat.one_mul,Nat.add_comm]

theorem rowWork_uniform {n : Nat} {β : Type} (v : Vector (β×Nat) n) (C : Nat)
    (h : ∀ i, (v.get i).2=C) : rowWork v=n*(C+1) := by
  unfold rowWork
  simp only [h]
  exact sum_ofFn_const n (C+1)

/-- This primitive computes all m candidate predecessor states for each
color/state cell, then materializes the resulting fixed-size table. -/
def mul (a b : Table k m) : Table k m×Nat :=
  let t := Vector.ofFn (fun q=>b.view.trans (a.view.trans q))
  let cells := Vector.ofFn (fun c : Fin k=>Vector.ofFn (fun q : Fin m=>
    let r := scan (fun p : Fin m=>a.view.active c p && decide (b.view.trans p=q)) (List.ofFn id)
    (b.view.active c q || r.1,r.2)))
  let bits := Vector.ofFn (fun c=>Vector.ofFn (fun q=>(cells.get c |>.get q).1))
  (⟨t,bits⟩,m+(List.ofFn (fun c=>rowWork (cells.get c))).sum)

theorem mul_view (a b : Table k m) : (mul a b).1.view=View.mul a.view b.view := by
  apply View.ext
  · funext q; simp [mul,Table.view]
  · funext c q
    simp only [mul,Table.view,Table.get_ofFn,View.mul,scan_value,any,finEnum]

theorem mul_steps (a b : Table k m) : (mul a b).2=m+k*(m*(m+1)) := by
  unfold mul
  simp only [Table.get_ofFn]
  have h (c : Fin k) : rowWork (Vector.ofFn (fun q : Fin m=>
      (b.view.active c q || (scan (fun p : Fin m=>a.view.active c p && decide (b.view.trans p=q))
        (List.ofFn id)).1,
       (scan (fun p : Fin m=>a.view.active c p && decide (b.view.trans p=q))
        (List.ofFn id)).2)))=m*(m+1) := by
    apply rowWork_uniform
    intro q
    simp only [Table.get_ofFn,scan_steps,List.length_ofFn]
  simp only [h]
  rw [sum_ofFn_const]

/-- Relabeling coalesces old colors by scanning all k candidates for each
output cell. It never scans the represented endpoints. -/
def rename (g : Vector (Fin k) k) (a : Table k m) : Table k m×Nat :=
  let cells := Vector.ofFn (fun c : Fin k=>Vector.ofFn (fun q : Fin m=>
    scan (fun old : Fin k=>decide (g.get old=c) && a.view.active old q) (List.ofFn id)))
  let bits := Vector.ofFn (fun c=>Vector.ofFn (fun q=>(cells.get c |>.get q).1))
  (⟨a.trans,bits⟩,(List.ofFn (fun c=>rowWork (cells.get c))).sum)

theorem rename_view (g : Vector (Fin k) k) (a : Table k m) :
    (rename g a).1.view=View.rename g.get a.view := by
  apply View.ext
  · rfl
  · funext c q
    simp only [rename,Table.view,Table.get_ofFn,View.rename,scan_value,any,finEnum]

theorem rename_steps (g : Vector (Fin k) k) (a : Table k m) :
    (rename g a).2=k*(m*(k+1)) := by
  unfold rename
  simp only [Table.get_ofFn]
  have h (c : Fin k) : rowWork (Vector.ofFn (fun q : Fin m=>
      scan (fun old : Fin k=>decide (g.get old=c) && a.view.active old q)
        (List.ofFn id)))=m*(k+1) := by
    apply rowWork_uniform
    intro q
    simp only [Table.get_ofFn,scan_steps,List.length_ofFn]
  simp only [h]
  rw [sum_ofFn_const]

/-- Compose two materialized lazy maps. The new map is also materialized;
its future reads take one vector access regardless of update history. -/
def compose (g f : Vector (Fin k) k) : Vector (Fin k) k×Nat :=
  (Vector.ofFn (fun c=>g.get (f.get c)),k)

@[simp] theorem compose_get (g f : Vector (Fin k) k) (c : Fin k) :
    (compose g f).1.get c=g.get (f.get c) := by simp [compose]

@[simp] theorem compose_steps (g f : Vector (Fin k) k) : (compose g f).2=k := rfl

def identity (k : Nat) : Vector (Fin k) k := Vector.ofFn id

@[simp] theorem identity_get (c : Fin k) : (identity k).get c=c := by simp [identity]

/-- Every read in this implementation is an array-backed vector read.
The multiplier is a pattern-only bound on each table primitive. -/
def primitiveBudget (k m : Nat) : Nat :=
  1+k+m+k*(m*(m+1))+k*(m*(k+1))

theorem mul_le (a b : Table k m) : (mul a b).2≤primitiveBudget k m := by
  rw [mul_steps]; unfold primitiveBudget; omega

theorem rename_le (g : Vector (Fin k) k) (a : Table k m) :
    (rename g a).2≤primitiveBudget k m := by
  rw [rename_steps]; unfold primitiveBudget; omega

/-- A counted final color/state test over the materialized aggregate. -/
def accepted {α : Type} (d : DFA α) (select : Fin k→Bool)
    (a : Table k d.stateCount) : Bool×Nat :=
  let rows := Vector.ofFn (fun c : Fin k=>scan
    (fun q : Fin d.stateCount=>a.view.active c q && d.final q) (List.ofFn id))
  let result := scan (fun c : Fin k=>select c && (rows.get c).1) (List.ofFn id)
  (result.1,result.2+(List.ofFn (fun c=>(rows.get c).2)).sum)

theorem accepted_value {α : Type} (d : DFA α) (select : Fin k→Bool)
    (a : Table k d.stateCount) : (accepted d select a).1=BoundaryIndex.accepted d select a := by
  simp only [accepted,scan_value,Table.get_ofFn,BoundaryIndex.accepted,any,finEnum]

theorem accepted_steps {α : Type} (d : DFA α) (select : Fin k→Bool)
    (a : Table k d.stateCount) : (accepted d select a).2=k+k*d.stateCount := by
  simp only [accepted,scan_steps,List.length_ofFn,Table.get_ofFn,sum_ofFn_const]

end REWB.BoundaryIndex.Counted
