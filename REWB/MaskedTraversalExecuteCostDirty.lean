import REWB.MaskedTraversalExecute

/-! Unconditional arithmetic for the actual sparse dirty-key collectors.
The potential pays once for every pending distinct key and is consumed
when a band repairs it. These bounds use the executed neighborhood lists,
patch logs and live event records; no cardinality oracle or full-class
enumeration is supplied. -/
namespace REWB.MaskedTraversalExecute.Cost
open REWB.MaskedTraversalDirty REWB.MaskedOrdered
variable {h : Nat}

theorem markList_work (capacity : Nat) (ps : List Nat) (out : Marked h) :
    (markList capacity ps out).work≤out.work+(28*h+22)*ps.length+1 := by
  induction ps generalizing out with
  | nil=>simp [markList]
  | cons p ps ih=>
    have ht:=ih (mark capacity p out)
    have hw:=MaskedOrdered.insert_work out.keys.tree capacity p
    change (MaskedOrdered.add out.keys capacity p).2.work≤28*h+18 at hw
    change (markList capacity ps (mark capacity p out)).work≤out.work+(28*h+22)*(ps.length+1)+1
    change _≤out.work+(MaskedOrdered.add out.keys capacity p).2.work+4+(28*h+22)*ps.length+1 at ht
    rw [Nat.mul_succ]
    omega

theorem change_measured (before after : Tree h) (capacity p : Nat) (out : Marked h) :
    (markChange before after capacity p out).keys.positions.length≤out.keys.positions.length+9 ∧
    (markChange before after capacity p out).work≤out.work+308*h+270 := by
  have hc:=markList_card capacity (prepareChange before after capacity p).keys out
  have hw:=markList_work capacity (prepareChange before after capacity p).keys out
  have hb:=prepareChange_bounds before after capacity p
  have hm:=Nat.mul_le_mul_left (28*h+22) hb.1
  simp only [markChange]
  constructor
  · omega
  · simp only [Nat.add_mul,Nat.mul_assoc] at hm hw
    omega

theorem patches_measured (capacity : Nat) (ps : List (MaskedTraversalFrontier.Patch h)) (out : Marked h) :
    (patches capacity ps out).keys.positions.length≤out.keys.positions.length+9*ps.length ∧
    (patches capacity ps out).work≤out.work+(308*h+274)*ps.length+1 := by
  induction ps generalizing out with
  | nil=>simp [patches]
  | cons p ps ih=>
    let marked:=markChange p.before.state.leaders p.update.frontier.state.leaders capacity p.position out
    have hs:=change_measured p.before.state.leaders p.update.frontier.state.leaders capacity p.position out
    have ht:=ih {marked with work:=marked.work+4}
    change _≤out.keys.positions.length+9*(ps.length+1) ∧ _≤out.work+(308*h+274)*(ps.length+1)+1
    rw [patches]
    dsimp only [marked] at ht
    simp only [Nat.mul_succ]
    constructor <;> omega

theorem live_measured (before after : Tree h) (capacity : Nat)
    (es : List MaskedClusterLeaders.Record) (out : Marked h) :
    (live before after capacity es out).keys.positions.length≤out.keys.positions.length+9*es.length ∧
    (live before after capacity es out).work≤out.work+(308*h+274)*es.length+1 := by
  induction es generalizing out with
  | nil=>simp [live]
  | cons e es ih=>
    let marked:=markChange before after capacity e.value.edge.2 out
    have hs:=change_measured before after capacity e.value.edge.2 out
    have ht:=ih {marked with work:=marked.work+4}
    change _≤out.keys.positions.length+9*(es.length+1) ∧ _≤out.work+(308*h+274)*(es.length+1)+1
    rw [live]
    dsimp only [marked] at ht
    simp only [Nat.mul_succ]
    constructor <;> omega

def markBudget (h repairUnit : Nat) : Nat := 9*repairUnit+308*h+274

theorem change_charged (before after : Tree h) (capacity p repairUnit : Nat) (out : Marked h) :
    (markChange before after capacity p out).work-out.work+
      repairUnit*(markChange before after capacity p out).keys.positions.length≤
        repairUnit*out.keys.positions.length+markBudget h repairUnit-4 := by
  have hs:=change_measured before after capacity p out
  have hm:=Nat.mul_le_mul_left repairUnit hs.1
  unfold markBudget
  simp only [Nat.mul_add,Nat.mul_comm repairUnit 9] at hm
  omega

theorem patches_charged (capacity repairUnit : Nat) (ps : List (MaskedTraversalFrontier.Patch h)) (out : Marked h) :
    (patches capacity ps out).work-out.work+repairUnit*(patches capacity ps out).keys.positions.length≤
      repairUnit*out.keys.positions.length+markBudget h repairUnit*ps.length+1 := by
  have hs:=patches_measured capacity ps out
  have hm:=Nat.mul_le_mul_left repairUnit hs.1
  unfold markBudget
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm repairUnit 9] at hs hm ⊢
  omega

theorem crossing_charged (before : MaskedClusterLeaders.State h) (after : MaskedClusterLeaders.Shortened h)
    (capacity repairUnit : Nat) (out : Marked h) :
    (crossing before after capacity out).work-out.work+repairUnit*(crossing before after capacity out).keys.positions.length≤
      repairUnit*out.keys.positions.length+markBudget h repairUnit*after.live.length+1 := by
  have hs:=live_measured before.leaders after.state.leaders capacity after.live out
  have hm:=Nat.mul_le_mul_left repairUnit hs.1
  unfold crossing markBudget
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm repairUnit 9] at hs hm ⊢
  omega

theorem crossing_fresh (before : MaskedClusterLeaders.State h) (after : MaskedClusterLeaders.Shortened h)
    (capacity repairUnit : Nat) :
    (crossing before after capacity (MaskedTraversalDirty.empty h)).work+
      repairUnit*(crossing before after capacity (MaskedTraversalDirty.empty h)).keys.positions.length≤
        markBudget h repairUnit*after.live.length+2 := by
  have hs:=live_measured before.leaders after.state.leaders capacity after.live (MaskedTraversalDirty.empty h)
  have hm:=Nat.mul_le_mul_left repairUnit hs.1
  unfold crossing markBudget
  simp only [MaskedTraversalDirty.empty,MaskedOrdered.State.empty,List.length_nil,Nat.zero_add,Nat.add_mul,
    Nat.mul_assoc,Nat.mul_left_comm repairUnit 9] at hs hm ⊢
  omega

end REWB.MaskedTraversalExecute.Cost
