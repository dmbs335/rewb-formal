import REWB.BoundaryIndexColors

/-! Eager finite tables with dependent payloads.  Every factory call is
materialized once before costs are read.  Lookup is one array access and
an erased equality transport; no factory or key search is retained in
the table. -/
namespace REWB.BoundaryRange.Table

universe u
variable {n : Nat} {F : Fin n→Type u}

@[simp] theorem vector_get_ofFn {β : Type u} (f : Fin n→β) (i : Fin n) :
    (Vector.ofFn f).get i=f i := by
  simp [Vector.get,Vector.getElem_ofFn]

structure Cell (F : Fin n→Type u) where
  key : Fin n
  value : F key
  work : Nat

structure Index (F : Fin n→Type u) where
  cells : Vector (Cell F) n
  keyed : ∀i,(cells.get i).key=i
  work : Nat

def Cell.read (c : Cell F) (i : Fin n) (h : c.key=i) : F i := h ▸ c.value

theorem Cell.read_eq (c : Cell F) (i : Fin n) (v : F i) (work : Nat)
    (h : c=⟨i,v,work⟩) (hk : c.key=i) : c.read i hk=v := by
  cases h
  rfl

def get (idx : Index F) (i : Fin n) : F i :=
  (idx.cells.get i).read i (idx.keyed i)

def build (make : (i : Fin n)→F i×Nat) : Index F :=
  let cells : Vector (Cell F) n:=Vector.ofFn fun i=>
    let out:=make i
    ⟨i,out.1,out.2⟩
  ⟨cells,by intro i; simp only [cells,vector_get_ofFn],
    (List.ofFn fun i=>(cells.get i).work+3).sum+1⟩

@[simp] theorem get_build (make : (i : Fin n)→F i×Nat) (i : Fin n) :
    get (build make) i=(make i).1 := by
  apply Cell.read_eq _ i (make i).1 (make i).2
  exact vector_get_ofFn _ i

theorem build_work (make : (i : Fin n)→F i×Nat) :
    (build make).work=(List.ofFn fun i=>(make i).2+3).sum+1 := by
  simp only [build,vector_get_ofFn]

theorem sum_ofFn_le (bound : Nat) (f : Fin n→Nat) (hf : ∀i,f i≤bound) :
    (List.ofFn f).sum≤n*bound := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons]
    have ht:=ih (fun i=>f i.succ) (fun i=>hf i.succ)
    have hh:=hf 0
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem build_work_le (make : (i : Fin n)→F i×Nat) (bound : Nat)
    (hm : ∀i,(make i).2≤bound) :
    (build make).work≤n*(bound+3)+1 := by
  rw [build_work]
  have hh:=sum_ofFn_le (bound+3) (fun i=>(make i).2+3) (by intro i; dsimp; have h:=hm i; omega)
  omega

/-- Nonuniform factory costs can be charged without replacing them by
a maximum or evaluating the factory again. -/
theorem build_work_mono (make : (i : Fin n)→F i×Nat) (budget : Fin n→Nat)
    (hm : ∀i,(make i).2≤budget i) :
    (build make).work≤(List.ofFn fun i=>budget i+3).sum+1 := by
  rw [build_work]
  apply Nat.add_le_add_right
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.sum_cons,List.sum_cons]
    exact Nat.add_le_add (Nat.add_le_add_right (hm 0) 3)
      (ih (fun i=>make i.succ) (fun i=>budget i.succ) (fun i=>hm i.succ))

end REWB.BoundaryRange.Table
