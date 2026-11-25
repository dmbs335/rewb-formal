import REWB.ShortOuterRegular

/-! Concrete backwards F rows over the already built short-outer table.
Each start constructs one bounded word and one finite endpoint mask.  The
rows retain all possible F starts, so the later inner-pair loops perform
only bounded array reads.  Both empty F and empty outer copies are kept. -/
namespace REWB.ShortOuter.Ready
open REWB.Periodic
variable {σ : Nat}

def mask (band : Band.Index σ) (p : Nat) : Array Bool×Nat :=
  let ps:=CountedProjection.range (band.keys.width+1)
  let bs:=CountedProjection.map (fun len=>Band.query band p len) ps.1
  let out:=bs.1.toArray
  (out,ps.2+bs.2+out.size+2)

theorem mask_size (band : Band.Index σ) (p : Nat) :
    (mask band p).1.size=band.keys.width+1 := by
  simp only [mask,List.size_toArray,CountedProjection.map_value,
    CountedProjection.range_value,List.length_map,List.length_range]

theorem mask_get (band : Band.Index σ) (p len : Nat) (hl : len≤band.keys.width) :
    OneUseRange.FarAggregate.bit (mask band p).1 len=Band.get band p len := by
  simp only [OneUseRange.FarAggregate.bit,mask,List.getElem?_toArray,
    CountedProjection.map_value,CountedProjection.range_value,List.getElem?_map,
    List.getElem?_range,show len<band.keys.width+1 by omega,if_true,
    Option.map_some',Option.getD_some,Band.query_value]

theorem mask_work (band : Band.Index σ) (p : Nat) :
    (mask band p).2=12*band.keys.width+16 := by
  have hm:=CountedProjection.map_steps_constant (fun len=>Band.query band p len)
    (CountedProjection.range (band.keys.width+1)).1 8 (by intro _ _; rfl)
  simp only [mask]
  rw [hm]
  simp only [CountedProjection.range,CountedProjection.rangeFrom_steps,
    CountedProjection.map_value,CountedProjection.rangeFrom_value,List.size_toArray,
    List.length_map,List.length_range']
  omega

def row (F : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (band : Band.Index σ) (p : Nat) : OneUseRange.FarAggregate.Index×Nat :=
  let word:=(segment (ArrayText.read text fallback) p band.keys.width).toArray
  let bs:=mask band p
  let out:=OneUseRange.FarAggregate.build F word bs.1
  (out,bs.2+3*band.keys.width+out.work+6)

theorem row_work (F : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (band : Band.Index σ) (p : Nat) :
    (row F text fallback band p).2=
      band.keys.width*(6*F.stateCount+21)+3*F.stateCount+29 := by
  simp only [row,mask_work,OneUseRange.FarAggregate.build_work_exact,
    List.size_toArray,segment_length,Nat.mul_add]
  omega

structure Index where
  length : Nat
  width : Nat
  rows : Array OneUseRange.FarAggregate.Index
  work : Nat

def build (F : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (band : Band.Index σ) : Index :=
  let ps:=CountedProjection.range (text.size+1)
  let rs:=CountedProjection.map (fun p=>row F text fallback band p) ps.1
  let rows:=rs.1.toArray
  ⟨text.size,band.keys.width,rows,ps.2+rs.2+rows.size+2⟩

def query (idx : Index) (p off : Nat) : Bool×Nat :=
  match idx.rows[p]? with
  | none => (false,3)
  | some one => let r:=OneUseRange.FarAggregate.query one off; (r.1,r.2+3)

def get (idx : Index) (p off : Nat) : Bool := (query idx p off).1

theorem build_rows (F : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (band : Band.Index σ) (p : Nat) (hp : p≤text.size) :
    (build F text fallback band).rows[p]?=some (row F text fallback band p).1 := by
  simp only [build,List.getElem?_toArray,CountedProjection.map_value,CountedProjection.range_value,
    List.getElem?_map,List.getElem?_range,show p<text.size+1 by omega,if_true,Option.map_some']

theorem get_row (F : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (band : Band.Index σ) (p off : Nat) (hp : p≤text.size) :
    get (build F text fallback band) p off=
      (OneUseRange.FarAggregate.query (row F text fallback band p).1 off).1 := by
  simp only [get,query,build_rows F text fallback band p hp]

theorem query_work (idx : Index) (p off : Nat) : (query idx p off).2≤7 := by
  unfold query
  split
  · decide
  · have h:=OneUseRange.FarAggregate.query_work ‹_› off
    dsimp only
    omega

theorem build_work (F : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (band : Band.Index σ) :
    (build F text fallback band).work=
      (text.size+1)*(band.keys.width*(6*F.stateCount+21)+3*F.stateCount+33)+4 := by
  have hm:=CountedProjection.map_steps_constant (fun p=>row F text fallback band p)
    (CountedProjection.range (text.size+1)).1
    (band.keys.width*(6*F.stateCount+21)+3*F.stateCount+29)
    (by intro p _; exact row_work F text fallback band p)
  simp only [build]
  rw [hm]
  simp only [CountedProjection.range,CountedProjection.rangeFrom_steps,
    CountedProjection.map_value,CountedProjection.rangeFrom_value,List.size_toArray,
    List.length_map,List.length_range',Nat.mul_add,Nat.mul_one]
  omega

end REWB.ShortOuter.Ready
