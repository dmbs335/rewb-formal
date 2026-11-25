import REWB.MaskedPeriodicBatchCost

/-! Materialized reverse membership lists for cubic-run source windows.
Each physical boundary stores the IDs of all run windows containing it.
Appending a membership uses one list cons and one array update; existing
membership lists are shared. Targets and occurrence classes are untouched.
The executable construction visits only the actual run spans. -/
namespace REWB.MaskedSourceFanout
open REWB.RunGeometry REWB.MaskedPeriodic.Batch
variable {σ : Nat}

structure Cell where
  ids : List Nat := []
  count : Nat := 0
  deriving Repr

def read (rows : Array Cell) (p : Nat) : Cell := rows[p]?.getD {}

structure Built where
  rows : Array Cell
  memberships : Nat := 0
  work : Nat := 0
  deriving Repr

def push (id p : Nat) (out : Built) : Built :=
  let old:=read out.rows p
  { rows:=out.rows.setIfInBounds p ⟨id::old.ids,old.count+1⟩
    memberships:=out.memberships+1
    work:=out.work+7 }

theorem push_size (id p : Nat) (out : Built) :
    (push id p out).rows.size=out.rows.size := by
  simp [push]

theorem push_read (id p x : Nat) (out : Built) :
    read (push id p out).rows x=
      if x=p ∧ p<out.rows.size then
        ⟨id::(read out.rows x).ids,(read out.rows x).count+1⟩
      else read out.rows x := by
  by_cases hx : x=p
  · subst x
    by_cases hp : p<out.rows.size
    · simp only [push,read,Array.getElem?_setIfInBounds_self_of_lt hp,
        Option.getD_some,hp,and_self,ite_true]
    · have ha : out.rows[p]?=none := Array.getElem?_eq_none (by omega)
      have hb : (push id p out).rows[p]?=none :=
        Array.getElem?_eq_none (by rw [push_size]; omega)
      simp only [read,ha,hb,Option.getD_none,hp,and_false,ite_false]
  · simp only [push,read,Array.getElem?_setIfInBounds_ne (Ne.symm hx),hx,
      false_and,ite_false]

def fill (id : Nat) : Nat→Nat→Built→Built
  | 0,_,out => out
  | len+1,p,out => fill id len (p+1) (push id p out)

theorem fill_size (id len p : Nat) (out : Built) :
    (fill id len p out).rows.size=out.rows.size := by
  induction len generalizing p out with
  | zero => rfl
  | succ len ih => rw [fill,ih,push_size]

theorem fill_work (id len p : Nat) (out : Built) :
    (fill id len p out).work=out.work+7*len := by
  induction len generalizing p out with
  | zero => simp [fill]
  | succ len ih => rw [fill,ih]; simp [push,Nat.mul_add]; omega

theorem fill_memberships (id len p : Nat) (out : Built) :
    (fill id len p out).memberships=out.memberships+len := by
  induction len generalizing p out with
  | zero => simp [fill]
  | succ len ih => rw [fill,ih]; simp [push]; omega

theorem fill_read (id len p x : Nat) (out : Built) (hb : p+len≤out.rows.size) :
    read (fill id len p out).rows x=
      if p≤x ∧ x<p+len then
        ⟨id::(read out.rows x).ids,(read out.rows x).count+1⟩
      else read out.rows x := by
  induction len generalizing p out with
  | zero =>
    have h : ¬(p≤x ∧ x<p+0) := by omega
    simp only [fill,h,ite_false]
  | succ len ih =>
    have hp : p<out.rows.size := by omega
    have ht : p+1+len≤(push id p out).rows.size := by rw [push_size]; omega
    rw [fill,ih (p+1) (push id p out) ht,push_read]
    by_cases hx : x=p
    · subst x
      have h0 : ¬(p+1≤p ∧ p<p+1+len) := by omega
      have h1 : p≤p ∧ p<p+(len+1) := by omega
      simp only [h0,ite_false,h1,ite_true,hp,and_self]
    · have h0 : ¬(x=p ∧ p<out.rows.size) := by omega
      have he : (p+1≤x ∧ x<p+1+len) ↔ (p≤x ∧ x<p+(len+1)) := by omega
      simp only [h0,ite_false,he]

def loop : List Bounds→Nat→Built→Built
  | [],_,out => out
  | R::Rs,id,out => loop Rs (id+1)
      (fill id (span R) R.lo {out with work:=out.work+3})

theorem loop_size (Rs : List Bounds) (id : Nat) (out : Built) :
    (loop Rs id out).rows.size=out.rows.size := by
  induction Rs generalizing id out with
  | nil => rfl
  | cons R Rs ih => rw [loop,ih,fill_size]

theorem loop_memberships (Rs : List Bounds) (id : Nat) (out : Built) :
    (loop Rs id out).memberships=out.memberships+totalSpan Rs := by
  induction Rs generalizing id out with
  | nil => simp [loop,totalSpan]
  | cons R Rs ih => rw [loop,ih,fill_memberships]; simp only [totalSpan]; omega

theorem loop_work (Rs : List Bounds) (id : Nat) (out : Built) :
    (loop Rs id out).work=out.work+7*totalSpan Rs+3*Rs.length := by
  induction Rs generalizing id out with
  | nil => simp [loop,totalSpan]
  | cons R Rs ih =>
    rw [loop,ih,fill_work]
    simp only [totalSpan,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def build (n : Nat) (Rs : List Bounds) : Built :=
  loop Rs 0 { rows:=Array.replicate (n+1) {}, work:=n+1 }

theorem build_size (n : Nat) (Rs : List Bounds) : (build n Rs).rows.size=n+1 := by
  rw [build,loop_size,Array.size_replicate]

theorem build_memberships (n : Nat) (Rs : List Bounds) :
    (build n Rs).memberships=totalSpan Rs := by
  simp only [build,loop_memberships,Nat.zero_add]

theorem build_work (n : Nat) (Rs : List Bounds) :
    (build n Rs).work=n+1+7*totalSpan Rs+3*Rs.length := by
  rw [build,loop_work]

end REWB.MaskedSourceFanout
