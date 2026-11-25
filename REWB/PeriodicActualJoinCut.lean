import REWB.PeriodicConstructionWindows
import REWB.IntervalDFA

/-! Actual DFA cut-vector construction for the chronological join.
State enumeration, row scans, list construction and array materialization
are executed and charged. Scalar transitions and array reads are primitive
operations in this structural ledger. -/
namespace REWB.PeriodicActual.Join.Cut
open REWB.PeriodicConstruction
variable {α : Type}

def vector (d : DFA α) (f : Fin d.stateCount→Result (Fin d.stateCount)) : Result (DFACut.Row d) :=
  let ns:=CountedProjection.range d.stateCount
  let cells:=CountedProjection.map (fun i=>f (PeriodicCache.state d i)) ns.1
  (cells.1.toArray,ns.2+cells.2+cells.1.length+2)

theorem vector_value (d : DFA α) (f : Fin d.stateCount→Result (Fin d.stateCount)) :
    (vector d f).1=DFACut.vector d (fun q=>(f q).1) := by
  simp only [vector,CountedProjection.map_value,CountedProjection.range_value,DFACut.vector]

theorem vector_work (d : DFA α) (f : Fin d.stateCount→Result (Fin d.stateCount)) (cost : Nat)
    (hc : ∀q,(f q).2≤cost) : (vector d f).2≤d.stateCount*(cost+4)+4 := by
  have hh:=map_bound (fun i=>f (PeriodicCache.state d i)) (CountedProjection.range d.stateCount).1
    cost (fun i _=>hc _)
  simp only [CountedProjection.range_value,List.length_range] at hh
  unfold vector
  simp only [CountedProjection.range_value,CountedProjection.map_value,List.length_map,List.length_range]
  rw [show (CountedProjection.range d.stateCount).2=2*d.stateCount+1 from
    CountedProjection.rangeFrom_steps 0 d.stateCount]
  simp only [Nat.mul_add,Nat.mul_comm d.stateCount 4] at hh ⊢
  omega

def suffix (d : DFA α) : Word α→Result (List (DFACut.Row d))
  | []=>let row:=vector d (fun q=>(q,1)); ([row.1],row.2+2)
  | c::cs=>
    let ⟨rest,work⟩:=suffix d cs
    let row:=vector d (fun q=>(DFACut.read d (rest.headD #[]) (d.step q c),8))
    (row.1::rest,work+row.2+6)

theorem suffix_value (d : DFA α) (w : Word α) : (suffix d w).1=DFACut.suffixRows d w := by
  induction w with
  | nil=>simp only [suffix,vector_value,DFACut.suffixRows]; rfl
  | cons c cs ih=>simp only [suffix,vector_value,ih,DFACut.suffixRows]

theorem suffix_work (d : DFA α) (w : Word α) :
    (suffix d w).2≤(20*d.stateCount+20)*(w.length+1) := by
  induction w with
  | nil=>
    have h:=vector_work d (fun q=>(q,1)) 1 (fun _=>Nat.le_refl _)
    simp only [suffix,List.length_nil,Nat.zero_add,Nat.mul_one]
    omega
  | cons c cs ih=>
    have h:=vector_work d (fun q=>(DFACut.read d ((suffix d cs).1.headD #[]) (d.step q c),8))
      8 (fun _=>Nat.le_refl _)
    simp only [suffix,List.length_cons,Nat.mul_add,Nat.mul_one]
    simp only [Nat.mul_add,Nat.mul_one] at ih
    omega

theorem prefix_length (d : DFA α) (w : Word α) (q : Fin d.stateCount) :
    (MaskScan.prefixStates d q w).length=w.length+1 := by
  induction w generalizing q with
  | nil=>rfl
  | cons c cs ih=>simp only [MaskScan.prefixStates,List.length_cons,ih]

def prefixRow (d : DFA α) (w : Word α) (q : Fin d.stateCount) : Result (DFACut.Row d) :=
  let ⟨cells,steps⟩:=IntervalDFA.countedPrefix d q w
  (cells.toArray,6*steps+cells.length+3)

theorem prefixRow_value (d : DFA α) (w : Word α) (q : Fin d.stateCount) :
    (prefixRow d w q).1=(MaskScan.prefixStates d q w).toArray := by
  simp only [prefixRow,IntervalDFA.countedPrefix_spec]

theorem prefixRow_work (d : DFA α) (w : Word α) (q : Fin d.stateCount) :
    (prefixRow d w q).2=7*w.length+4 := by
  simp only [prefixRow,IntervalDFA.countedPrefix_spec,prefix_length]
  omega

def prefixes (d : DFA α) (w : Word α) : Result (Array (DFACut.Row d)) :=
  let states:=CountedProjection.range d.stateCount
  let rows:=CountedProjection.map (fun i=>prefixRow d w (PeriodicCache.state d i)) states.1
  (rows.1.toArray,states.2+rows.2+rows.1.length+2)

theorem prefixes_value (d : DFA α) (w : Word α) :
    (prefixes d w).1=DFACut.prefixRows d w := by
  simp only [prefixes,CountedProjection.map_value,CountedProjection.range_value,prefixRow_value,
    DFACut.prefixRows]

theorem prefixes_work (d : DFA α) (w : Word α) :
    (prefixes d w).2≤d.stateCount*(7*w.length+8)+4 := by
  have h:=map_bound (fun i=>prefixRow d w (PeriodicCache.state d i))
    (CountedProjection.range d.stateCount).1 (7*w.length+4)
    (fun _ _=>Nat.le_of_eq (prefixRow_work _ _ _))
  simp only [CountedProjection.range_value,List.length_range] at h
  unfold prefixes
  simp only [CountedProjection.range_value,CountedProjection.map_value,List.length_map,List.length_range]
  rw [show (CountedProjection.range d.stateCount).2=2*d.stateCount+1 from
    CountedProjection.rangeFrom_steps 0 d.stateCount]
  simp only [Nat.mul_add,Nat.mul_comm d.stateCount 2,Nat.mul_comm d.stateCount 5,
    Nat.mul_comm d.stateCount 8] at h ⊢
  omega

def build (d : DFA α) (left right : Word α) : Result (DFACut.Index d) :=
  let ⟨back,bwork⟩:=suffix d left
  let ⟨forward,fwork⟩:=prefixes d right
  (⟨left.length,back.toArray,forward⟩,bwork+fwork+left.length+back.length+5)

theorem build_value (d : DFA α) (left right : Word α) :
    (build d left right).1=DFACut.build d left right := by
  simp only [build,suffix_value,prefixes_value,DFACut.build]

theorem suffix_length (d : DFA α) (w : Word α) : (DFACut.suffixRows d w).length=w.length+1 := by
  induction w with
  | nil=>rfl
  | cons c cs ih=>simp only [DFACut.suffixRows,List.length_cons,ih]

def coefficient (states : Nat) : Nat := 40*states+40

theorem build_work (d : DFA α) (left right : Word α) :
    (build d left right).2≤coefficient d.stateCount*(left.length+right.length+1) := by
  have hs:=suffix_work d left
  have hp:=prefixes_work d right
  unfold build coefficient
  simp only [suffix_value,suffix_length]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc] at hs hp ⊢
  rw [Nat.mul_left_comm d.stateCount 7 right.length] at hp
  omega

end REWB.PeriodicActual.Join.Cut
