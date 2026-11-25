import REWB.BoundaryRangeTable

/-! Materialized subset keys for finite boundary tables. Query selection
compares cached Boolean rows using a counted scan. The input predicate
is evaluated once per examined state; callers use a range-map lookup
and a DFA final-bit lookup. There is no query-time `Colors.encode` or
construction of the subset enumeration. -/
namespace REWB.BoundaryRange.TableColor
open REWB.BoundaryIndex
variable {α : Type}

abbrev count (C : DFA α) := (Colors.colorSpace C).enumeration.elems.length
abbrev Key (C : DFA α) := Colors.Color C

structure Index (C : DFA α) where
  rows : Vector (Vector Bool C.stateCount) (count C)
  states : List (Fin C.stateCount)
  keys : List (Key C)
  fallback : Key C
  work : Nat

def build (C : DFA α) : Index C :=
  let rows:=Vector.ofFn fun c : Key C=>Vector.ofFn (Colors.decode C c)
  let states:=List.ofFn (fun q : Fin C.stateCount=>q)
  let keys:=List.ofFn (fun c : Key C=>c)
  ⟨rows,states,keys,Colors.encode C (fun _=>false),
    count C*(C.stateCount+3)+C.stateCount+count C+3⟩

@[simp] theorem build_row (C : DFA α) (c : Key C) (q : Fin C.stateCount) :
    ((build C).rows.get c).get q=Colors.decode C c q := by
  simp only [build,Table.get_ofFn]

def same {m : Nat} (row : Vector Bool m) (predicate : Fin m→Bool)
    (states : List (Fin m)) : Bool×Nat :=
  let checked:=Counted.scan (fun q=>!(row.get q==predicate q)) states
  (!checked.1,6*checked.2+1)

theorem same_correct {m : Nat} (row : Vector Bool m) (predicate : Fin m→Bool)
    (states : List (Fin m)) :
    (same row predicate states).1=true ↔ ∀q,q∈states→row.get q=predicate q := by
  simp [same,Counted.scan_value,List.any_eq_false]

theorem same_work {m : Nat} (row : Vector Bool m) (predicate : Fin m→Bool)
    (states : List (Fin m)) : (same row predicate states).2=6*states.length+1 := by
  simp only [same,Counted.scan_steps]

def search (C : DFA α) (rows : Vector (Vector Bool C.stateCount) (count C))
    (states : List (Fin C.stateCount)) (predicate : Fin C.stateCount→Bool) :
    List (Key C)→Option (Key C)×Nat
  | [] => (none,1)
  | c::cs =>
    let test:=same (rows.get c) predicate states
    if test.1 then (some c,test.2+3)
    else
      let out:=search C rows states predicate cs
      (out.1,test.2+out.2+3)

theorem search_sound (C : DFA α) (rows : Vector (Vector Bool C.stateCount) (count C))
    (states : List (Fin C.stateCount)) (predicate : Fin C.stateCount→Bool)
    (keys : List (Key C)) (c : Key C)
    (h : (search C rows states predicate keys).1=some c) :
    c∈keys ∧ ∀q,q∈states→(rows.get c).get q=predicate q := by
  induction keys with
  | nil => simp [search] at h
  | cons k keys ih =>
    simp only [search] at h
    split at h
    next ht =>
      have he : k=c := Option.some.inj h
      subst c
      exact ⟨List.mem_cons_self,(same_correct _ _ _).mp ht⟩
    next ht =>
      obtain ⟨hm,hp⟩:=ih h
      exact ⟨List.mem_cons_of_mem _ hm,hp⟩

theorem search_exists (C : DFA α) (rows : Vector (Vector Bool C.stateCount) (count C))
    (states : List (Fin C.stateCount)) (predicate : Fin C.stateCount→Bool)
    (keys : List (Key C))
    (h : ∃c,c∈keys ∧ ∀q,q∈states→(rows.get c).get q=predicate q) :
    ∃c,(search C rows states predicate keys).1=some c := by
  induction keys with
  | nil => simp at h
  | cons k keys ih =>
    simp only [search]
    split
    next ht => exact ⟨k,rfl⟩
    next ht =>
      apply ih
      obtain ⟨c,hc,hp⟩:=h
      rcases List.mem_cons.mp hc with he|hc
      · subst c
        exact False.elim (ht ((same_correct _ _ _).mpr hp))
      · exact ⟨c,hc,hp⟩

theorem search_work (C : DFA α) (rows : Vector (Vector Bool C.stateCount) (count C))
    (states : List (Fin C.stateCount)) (predicate : Fin C.stateCount→Bool)
    (keys : List (Key C)) :
    (search C rows states predicate keys).2≤keys.length*(6*states.length+4)+1 := by
  induction keys with
  | nil => simp [search]
  | cons k keys ih =>
    simp only [search]
    split <;> simp only [same_work,List.length_cons,Nat.add_mul,Nat.one_mul] <;> omega

def choose (C : DFA α) (idx : Index C) (predicate : Fin C.stateCount→Bool) : Key C×Nat :=
  let out:=search C idx.rows idx.states predicate idx.keys
  (out.1.getD idx.fallback,out.2+1)

theorem choose_correct (C : DFA α) (predicate : Fin C.stateCount→Bool) :
    Colors.decode C (choose C (build C) predicate).1=predicate := by
  have hx : ∃c,(search C (build C).rows (build C).states predicate (build C).keys).1=some c := by
    apply search_exists
    refine ⟨Colors.encode C predicate,?_,?_⟩
    · simp only [build,List.mem_ofFn]
      exact ⟨Colors.encode C predicate,rfl⟩
    · intro q hq
      rw [build_row,Colors.decode_encode]
  obtain ⟨c,hc⟩:=hx
  have hs:=search_sound C (build C).rows (build C).states predicate (build C).keys c hc
  simp only [choose,hc,Option.getD_some]
  funext q
  have hq : q∈(build C).states := by simp [build]
  simpa only [build_row] using hs.2 q hq

def budget (C : DFA α) : Nat := count C*(6*C.stateCount+4)+2

theorem choose_work (C : DFA α) (predicate : Fin C.stateCount→Bool) :
    (choose C (build C) predicate).2≤budget C := by
  have h:=search_work C (build C).rows (build C).states predicate (build C).keys
  simp only [build,List.length_ofFn] at h
  exact Nat.add_le_add_right h 1

end REWB.BoundaryRange.TableColor
