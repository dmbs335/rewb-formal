import REWB.MaskedMutableProgressionCost
import REWB.MaskedSourceFanoutPrepared

/-! Materialized mutable-source snapshots for every actually enumerated
cubic run, together with one global singleton-source snapshot. The run
array is traversed once by an array fold; no substring or mask is copied.
Targets and complete occurrence sets are not stored or changed here. -/
namespace REWB.MaskedMutableProgression.Batch
open REWB.RunGeometry
open REWB.MaskedPeriodic.Batch (span totalSpan)
variable {σ : Nat}

def Current (source : Array Bool) (removed : List Nat) (p : Nat) : Prop :=
  MaskedProgression.readMask source p=true ∧ p∉removed

structure IndexSpec (source : Array Bool) (removed : List Nat)
    (base len step : Nat) (idx : Index) : Prop where
  good : idx.Valid
  sized : idx.LogSized
  base_eq : idx.base=base
  len_eq : idx.len=len
  step_eq : idx.step=step
  live : idx.Represents (Current source removed)

theorem built_spec (source : Array Bool) (base len step : Nat) :
    IndexSpec source [] base len step (build source base len step).index := by
  refine ⟨build_valid source base len step,build_logSized source base len step,rfl,rfl,rfl,?_⟩
  intro p
  simpa only [Current,List.not_mem_nil,not_false_eq_true,and_true,build_base,build_len] using build_live source base len step p

theorem IndexSpec.erase {source : Array Bool} {removed : List Nat} {base len step : Nat}
    {idx : Index} (hv : IndexSpec source removed base len step idx) (p : Nat) :
    IndexSpec source (p::removed) base len step (MaskedMutableProgression.erase idx p).index := by
  refine ⟨erase_valid idx hv.good p,erase_logSized idx hv.sized p,
    (erase_base idx p).trans hv.base_eq,(erase_len idx p).trans hv.len_eq,
    (erase_step idx p).trans hv.step_eq,?_⟩
  have hh:=erase_represents idx hv.good _ hv.live p
  intro x
  rw [hh x]
  simp only [Current,List.mem_cons,not_or]
  constructor
  · rintro ⟨hlo,hhi,hne,hm,hn⟩; exact ⟨hlo,hhi,hm,hne,hn⟩
  · rintro ⟨hlo,hhi,hm,hne,hn⟩; exact ⟨hlo,hhi,hne,hm,hn⟩

structure RowsBuilt where
  rows : Array Index := #[]
  work : Nat := 0
  deriving Repr

def buildOne (source : Array Bool) (K : Nat) (out : RowsBuilt) (R : Bounds) : RowsBuilt :=
  let r:=build source R.lo (span R) (K*R.period)
  ⟨out.rows.push r.index,out.work+r.work+6⟩

def buildRows (source : Array Bool) (K : Nat) (runs : Array Bounds) : RowsBuilt :=
  runs.foldl (buildOne source K) {work:=1}

/-- A proof-only sum, not a second executable traversal. -/
def rowsCost (source : Array Bool) (K : Nat) : List Bounds→Nat
  | [] => 0
  | R::Rs => (build source R.lo (span R) (K*R.period)).work+6+rowsCost source K Rs

theorem fold_rows (source : Array Bool) (K : Nat) (Rs : List Bounds) (out : RowsBuilt) :
    (Rs.foldl (buildOne source K) out).rows.toList=
      out.rows.toList++Rs.map (fun R=>(build source R.lo (span R) (K*R.period)).index) := by
  induction Rs generalizing out with
  | nil => simp
  | cons R Rs ih =>
    rw [List.foldl_cons,ih]
    simp only [buildOne,Array.push_toList,List.map_cons,List.append_assoc,List.singleton_append]

theorem fold_work (source : Array Bool) (K : Nat) (Rs : List Bounds) (out : RowsBuilt) :
    (Rs.foldl (buildOne source K) out).work=out.work+rowsCost source K Rs := by
  induction Rs generalizing out with
  | nil => simp [rowsCost]
  | cons R Rs ih => rw [List.foldl_cons,ih]; simp [buildOne,rowsCost,Nat.add_assoc]

theorem buildRows_list (source : Array Bool) (K : Nat) (runs : Array Bounds) :
    (buildRows source K runs).rows.toList=
      runs.toList.map (fun R=>(build source R.lo (span R) (K*R.period)).index) := by
  rw [buildRows,←Array.foldl_toList,fold_rows]
  rfl

theorem buildRows_get (source : Array Bool) (K : Nat) (runs : Array Bounds) (id : Nat) :
    (buildRows source K runs).rows[id]?=
      runs[id]?.map (fun R=>(build source R.lo (span R) (K*R.period)).index) := by
  have hh:=congrArg (fun xs : List Index=>xs[id]?) (buildRows_list source K runs)
  simpa only [Array.getElem?_toList,List.getElem?_map] using hh

theorem buildRows_size (source : Array Bool) (K : Nat) (runs : Array Bounds) :
    (buildRows source K runs).rows.size=runs.size := by
  have hh:=congrArg List.length (buildRows_list source K runs)
  simpa only [Array.length_toList,List.length_map] using hh

theorem buildRows_work (source : Array Bool) (K : Nat) (runs : Array Bounds) :
    (buildRows source K runs).work=1+rowsCost source K runs.toList := by
  rw [buildRows,←Array.foldl_toList,fold_work]

structure State where
  n : Nat
  modulus : Nat
  runs : Array Bounds
  indexes : Array Index
  singleton : Index
  sources : MaskedSourceFanout.Built
  enumerationWork : Nat := 0
  preparationWork : Nat := 0
  updateWork : Nat := 0
  requests : Nat := 0
  delivered : Nat := 0
  deriving Repr

/-- The reverse-address rows name precisely the not-yet-removed physical
sources. The history occurs only in this specification. -/
structure Valid (source : Array Bool) (removed : List Nat) (st : State) : Prop where
  positive : 0<st.modulus
  sourceGood : MaskedSourceFanout.Good st.sources
  sourceSize : st.sources.rows.size=st.n+1
  size : st.indexes.size=st.runs.size
  bounds : ∀(id : Nat) (R : Bounds),st.runs[id]?=some R→R.lo≤R.hi ∧ R.hi≤st.n ∧ 0<R.period
  singleton : IndexSpec source removed 0 (st.n+1) 1 st.singleton
  rows : ∀(id : Nat) (R : Bounds),st.runs[id]?=some R→∃idx,st.indexes[id]?=some idx ∧
    IndexSpec source removed R.lo (span R) (st.modulus*R.period) idx
  pending : ∀p id,id∈(MaskedSourceFanout.read st.sources.rows p).ids ↔
    p∉removed ∧ ∃R,st.runs[id]?=some R ∧ R.lo≤p ∧ p≤R.hi

/-- One concrete enumerator execution supplies both the run array and
reverse fanout. All-source singleton queries include the boundary `n`. -/
def prepare (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (K : Nat) : State :=
  let f:=MaskedSourceFanout.prepare text fallback
  let r:=buildRows source K f.runs
  let g:=build source 0 (text.size+1) 1
  { n:=text.size, modulus:=K, runs:=f.runs,indexes:=r.rows,singleton:=g.index,sources:=f.sources
    enumerationWork:=f.enumerationWork,preparationWork:=f.preparationWork+r.work+g.work+7 }

end REWB.MaskedMutableProgression.Batch
