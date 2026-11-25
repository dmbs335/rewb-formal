import REWB.MaskedRunCatalogMap
import REWB.MaskedMutableProgressionBatchCost

/-! Immutable target prefix arrays indexed by the existing source batch's
run IDs. One array fold builds target rows and a sparse binary ID map;
no run is re-enumerated and no source or target mask is copied. -/
namespace REWB.MaskedRunCatalog
open REWB.RunGeometry REWB.ExactKeys
open REWB.MaskedPeriodic.Batch (span totalSpan)
variable {σ : Nat}

structure Entry where
  run : Bounds
  counts : Array Nat
  deriving Repr

def entry (target : Array Bool) (K : Nat) (R : Bounds) : Entry :=
  ⟨R,(MaskedProgression.build target R.lo (span R) (K*R.period)).counts⟩

structure Acc where
  tree : Trie 2 := empty
  entries : Array Entry := #[]
  cells : Nat := 0
  work : Nat := 1
  deriving Repr

def step (target : Array Bool) (K width : Nat) (out : Acc) (R : Bounds) : Acc :=
  let key:=Map.key width R
  let assigned:=Map.put key.1 out.tree out.entries.size
  let counts:=MaskedProgression.build target R.lo (span R) (K*R.period)
  ⟨assigned.1,out.entries.push ⟨R,counts.counts⟩,out.cells+counts.counts.size,
    out.work+key.2+assigned.2+counts.slots+counts.arithmetic+8⟩

theorem step_entries (target : Array Bool) (K width : Nat) (out : Acc) (R : Bounds) :
    (step target K width out R).entries=out.entries.push (entry target K R) := rfl

theorem step_cells (target : Array Bool) (K width : Nat) (out : Acc) (R : Bounds) :
    (step target K width out R).cells=out.cells+span R := by
  simp only [step,MaskedProgression.build_size]

theorem step_tree (target : Array Bool) (K width : Nat) (out : Acc) (R : Bounds) :
    (step target K width out R).tree=(Map.put (RunDedup.key width R) out.tree out.entries.size).1 := by
  simp only [step,Map.key_value]

theorem step_work (target : Array Bool) (K width : Nat) (out : Acc) (R : Bounds) :
    (step target K width out R).work≤out.work+13*span R+38*width+15 := by
  have hm:=Map.put_work (Map.key width R).1 out.tree out.entries.size
  rw [Map.key_value,RunDedup.key_length] at hm
  have hc:=MaskedProgression.build_work target R.lo (span R) (K*R.period)
  simp only [step,Map.key_work,Map.key_value]
  omega

def width (n : Nat) : Nat := (n+1).log2+1

theorem width_capacity (n : Nat) : n<2^(width n) := by
  have hh:=Nat.lt_log2_self (n:=n+1)
  unfold width
  omega

structure Index where
  length : Nat
  width : Nat
  modulus : Nat
  runs : Array Bounds
  entries : Array Entry
  tree : Trie 2
  cells : Nat
  work : Nat
  deriving Repr

def build (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) : Index :=
  let h:=width n
  let out:=runs.foldl (step target K h) {}
  ⟨n,h,K,runs,out.entries,out.tree,out.cells,out.work+4⟩

/-- Reuses the existing actual enumeration and source-row IDs verbatim. -/
def ofBatch (target : Array Bool) (st : MaskedMutableProgression.Batch.State) : Index :=
  build st.n target st.modulus st.runs

def lookupId (idx : Index) (R : Bounds) : Option Nat×Nat :=
  if R.lo≤idx.length ∧ R.hi≤idx.length ∧ R.period≤idx.length then
    let key:=Map.key idx.width R
    let out:=Map.read idx.tree key.1
    (out.1,key.2+out.2+5)
  else (none,4)

structure Found where
  id : Nat
  value : Entry
  deriving Repr

def lookup (idx : Index) (R : Bounds) : Option Found×Nat :=
  let found:=lookupId idx R
  match found.1 with
  | none => (none,found.2+1)
  | some id => ((idx.entries[id]?).map (fun value=>⟨id,value⟩),found.2+3)

theorem lookupId_work (idx : Index) (R : Bounds) : (lookupId idx R).2≤26*idx.width+12 := by
  have hh:=Map.read_work idx.tree (Map.key idx.width R).1
  rw [Map.key_value,RunDedup.key_length] at hh
  simp only [lookupId]
  split
  · simp only [Map.key_work,Map.key_value]
    omega
  · dsimp only
    omega

theorem lookup_work (idx : Index) (R : Bounds) : (lookup idx R).2≤26*idx.width+15 := by
  have hh:=lookupId_work idx R
  unfold lookup
  dsimp only
  cases he : (lookupId idx R).1 <;> simp only [he] <;> omega

theorem fold_entries (target : Array Bool) (K h : Nat) (Rs : List Bounds) (out : Acc) :
    (Rs.foldl (step target K h) out).entries.toList=
      out.entries.toList++Rs.map (entry target K) := by
  induction Rs generalizing out with
  | nil => simp
  | cons R Rs ih =>
    rw [List.foldl_cons,ih,step_entries]
    simp only [Array.push_toList,List.map_cons,List.append_assoc,List.singleton_append]

theorem build_entries (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) :
    (build n target K runs).entries.toList=runs.toList.map (entry target K) := by
  unfold build
  dsimp only
  rw [←Array.foldl_toList,fold_entries]
  rfl

theorem build_get (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) (id : Nat) :
    (build n target K runs).entries[id]?=runs[id]?.map (entry target K) := by
  have hh:=congrArg (fun xs : List Entry=>xs[id]?) (build_entries n target K runs)
  simpa only [Array.getElem?_toList,List.getElem?_map] using hh

theorem build_size (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) :
    (build n target K runs).entries.size=runs.size := by
  have hh:=congrArg List.length (build_entries n target K runs)
  simpa only [Array.length_toList,List.length_map] using hh

theorem fold_cells (target : Array Bool) (K h : Nat) (Rs : List Bounds) (out : Acc) :
    (Rs.foldl (step target K h) out).cells=out.cells+totalSpan Rs := by
  induction Rs generalizing out with
  | nil => simp [totalSpan]
  | cons R Rs ih => rw [List.foldl_cons,ih,step_cells]; simp only [totalSpan,Nat.add_assoc]

theorem build_cells (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) :
    (build n target K runs).cells=totalSpan runs.toList := by
  unfold build
  dsimp only
  rw [←Array.foldl_toList,fold_cells]
  exact Nat.zero_add _

theorem fold_work (target : Array Bool) (K h : Nat) (Rs : List Bounds) (out : Acc) :
    (Rs.foldl (step target K h) out).work≤out.work+13*totalSpan Rs+(38*h+15)*Rs.length := by
  induction Rs generalizing out with
  | nil => simp [totalSpan]
  | cons R Rs ih =>
    have hh:=step_work target K h out R
    have ht:=ih (step target K h out R)
    rw [List.foldl_cons]
    simp only [totalSpan,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem build_work (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) :
    (build n target K runs).work≤13*totalSpan runs.toList+(38*width n+15)*runs.size+5 := by
  have hh:=fold_work target K (width n) runs.toList {}
  simp only [Array.length_toList] at hh
  unfold build
  dsimp only
  rw [←Array.foldl_toList]
  omega

end REWB.MaskedRunCatalog
