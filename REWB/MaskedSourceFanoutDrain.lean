import REWB.MaskedSourceFanoutMass

/-! One-shot delivery of affected run IDs. Clearing a source's reverse
membership row prevents repeated delivery, even if the caller repeats a
position. Run indexes and cached cluster banks are updated by the caller;
this module constructs and counts their exact update-address lists. -/
namespace REWB.MaskedSourceFanout

theorem read_outside (rows : Array Cell) (p : Nat) (hp : rows.size≤p) : read rows p={} := by
  simp only [read,Array.getElem?_eq_none hp,Option.getD_none]

theorem read_clear (rows : Array Cell) (p x : Nat) :
    read (rows.setIfInBounds p {}) x=if x=p then {} else read rows x := by
  by_cases hx : x=p
  · subst x
    by_cases hp : p<rows.size
    · simp [read,Array.getElem?_setIfInBounds_self_of_lt hp]
    · rw [read_outside _ p (by rw [Array.size_setIfInBounds]; omega)]
      simp
  · simp only [read,Array.getElem?_setIfInBounds_ne (Ne.symm hx),hx,ite_false]

def take (p : Nat) (out : Built) : Cell×Built :=
  let cell:=read out.rows p
  (cell,{ rows:=out.rows.setIfInBounds p {}
          memberships:=out.memberships-cell.count
          work:=out.work+5 })

theorem take_size (p : Nat) (out : Built) : (take p out).2.rows.size=out.rows.size := by
  simp [take]

theorem take_read (p x : Nat) (out : Built) :
    read (take p out).2.rows x=if x=p then {} else read out.rows x :=
  read_clear out.rows p x

theorem take_total (p : Nat) (out : Built) :
    total (take p out).2.rows+(take p out).1.count=total out.rows := by
  have hs:=sumPrefix_change (fun x=>(read out.rows x).count)
    (fun x=>(read (take p out).2.rows x).count) out.rows.size p 0 (by
      intro x
      dsimp only
      rw [take_read]
      by_cases hx : x=p <;> simp [hx])
  unfold total
  rw [take_size]
  by_cases hp : p<out.rows.size
  · simp only [hp,ite_true,Nat.add_zero] at hs
    exact hs
  · have hz:=read_outside out.rows p (by omega)
    simp only [hp,ite_false,Nat.add_zero] at hs
    simpa only [take,hz,Nat.add_zero] using hs

theorem take_good (p : Nat) (out : Built) (hg : Good out) : Good (take p out).2 := by
  refine ⟨?_,?_⟩
  · intro x
    rw [take_read]
    split
    · rfl
    · exact hg.1 x
  · have hs:=take_total p out
    rw [hg.2] at hs
    change total (take p out).2.rows=out.memberships-(read out.rows p).count
    change total (take p out).2.rows+(read out.rows p).count=out.memberships at hs
    omega

theorem take_balance (p : Nat) (out : Built) (hg : Good out) :
    (take p out).1.count+(take p out).2.memberships=out.memberships := by
  have hs:=take_total p out
  have hn:=take_good p out hg
  rw [hg.2,hn.2] at hs
  omega

theorem take_count (p : Nat) (out : Built) (hg : Good out) :
    (take p out).1.count=(take p out).1.ids.length := hg.1 p

theorem take_again (p : Nat) (out : Built) : (take p (take p out).2).1={} := by
  change read (take p out).2.rows p={}
  rw [take_read,if_pos rfl]

structure Delivery where
  source : Nat
  affected : Cell
  deriving Repr

structure Drained where
  remaining : Built
  deliveries : List Delivery
  calls : Nat
  visits : Nat
  work : Nat
  deriving Repr

/-- Batches are returned in reverse request order; their internal run-ID
lists are shared with the original index, without flattening or copying. -/
def drainLoop : List Nat→Built→List Delivery→Nat→Nat→Nat→Drained
  | [],out,acc,calls,visits,work => ⟨out,acc,calls,visits,work⟩
  | p::ps,out,acc,calls,visits,work =>
    let r:=take p out
    drainLoop ps r.2 (⟨p,r.1⟩::acc) (calls+1) (visits+r.1.count) (work+8)

theorem drainLoop_good (ps : List Nat) (out : Built) (acc : List Delivery)
    (calls visits work : Nat) (hg : Good out) :
    Good (drainLoop ps out acc calls visits work).remaining := by
  induction ps generalizing out acc calls visits work with
  | nil => exact hg
  | cons p ps ih => rw [drainLoop]; exact ih _ _ _ _ _ (take_good p out hg)

theorem drainLoop_balance (ps : List Nat) (out : Built) (acc : List Delivery)
    (calls visits work : Nat) (hg : Good out) :
    (drainLoop ps out acc calls visits work).visits+
      (drainLoop ps out acc calls visits work).remaining.memberships=
        visits+out.memberships := by
  induction ps generalizing out acc calls visits work with
  | nil => rfl
  | cons p ps ih =>
    rw [drainLoop,ih _ _ _ _ _ (take_good p out hg)]
    have hb:=take_balance p out hg
    omega

theorem drainLoop_counters (ps : List Nat) (out : Built) (acc : List Delivery)
    (calls visits work : Nat) :
    (drainLoop ps out acc calls visits work).calls=calls+ps.length ∧
    (drainLoop ps out acc calls visits work).work=work+8*ps.length ∧
    (drainLoop ps out acc calls visits work).remaining.work=out.work+5*ps.length := by
  induction ps generalizing out acc calls visits work with
  | nil => simp [drainLoop]
  | cons p ps ih =>
    rw [drainLoop]
    have hh:=ih (take p out).2 (⟨p,(take p out).1⟩::acc)
      (calls+1) (visits+(take p out).1.count) (work+8)
    simp only [take,List.length_cons,Nat.mul_add,Nat.mul_one] at hh ⊢
    exact ⟨by omega,by omega,by omega⟩

def drain (ps : List Nat) (out : Built) : Drained := drainLoop ps out [] 0 0 0

theorem drain_visits (ps : List Nat) (out : Built) (hg : Good out) :
    (drain ps out).visits≤out.memberships := by
  have hh:=drainLoop_balance ps out [] 0 0 0 hg
  unfold drain
  omega

theorem drainLoop_read (ps : List Nat) (out : Built) (acc : List Delivery)
    (calls visits work x : Nat) :
    read (drainLoop ps out acc calls visits work).remaining.rows x=
      if x∈ps then {} else read out.rows x := by
  induction ps generalizing out acc calls visits work with
  | nil => simp [drainLoop]
  | cons p ps ih =>
    rw [drainLoop,ih,take_read]
    by_cases ht : x∈ps <;> by_cases he : x=p <;> simp [ht,he]

def deliverySize : List Delivery→Nat
  | [] => 0
  | d::ds => d.affected.ids.length+deliverySize ds

theorem drainLoop_deliverySize (ps : List Nat) (out : Built) (acc : List Delivery)
    (calls visits work : Nat) (hg : Good out) :
    deliverySize (drainLoop ps out acc calls visits work).deliveries+visits=
      deliverySize acc+(drainLoop ps out acc calls visits work).visits := by
  induction ps generalizing out acc calls visits work with
  | nil => simp [drainLoop]
  | cons p ps ih =>
    have hh:=ih (take p out).2 (⟨p,(take p out).1⟩::acc)
      (calls+1) (visits+(take p out).1.count) (work+8) (take_good p out hg)
    simp only [deliverySize] at hh
    have hc:=take_count p out hg
    simp only [drainLoop]
    omega

theorem drain_deliverySize (ps : List Nat) (out : Built) (hg : Good out) :
    deliverySize (drain ps out).deliveries=(drain ps out).visits := by
  have hh:=drainLoop_deliverySize ps out [] 0 0 0 hg
  simpa only [drain,deliverySize,Nat.add_zero,Nat.zero_add] using hh

theorem drain_size_bound (ps : List Nat) (out : Built) (hg : Good out) :
    deliverySize (drain ps out).deliveries≤out.memberships := by
  rw [drain_deliverySize ps out hg]
  exact drain_visits ps out hg

def HasDelivery (ds : List Delivery) (source run : Nat) : Prop :=
  ∃ d,d∈ds ∧ d.source=source ∧ run∈d.affected.ids

theorem hasDelivery_cons (d : Delivery) (ds : List Delivery) (source run : Nat) :
    HasDelivery (d::ds) source run ↔
      (d.source=source ∧ run∈d.affected.ids) ∨ HasDelivery ds source run := by
  simp [HasDelivery]

theorem drainLoop_has (ps : List Nat) (out : Built) (acc : List Delivery)
    (calls visits work source run : Nat) :
    HasDelivery (drainLoop ps out acc calls visits work).deliveries source run ↔
      HasDelivery acc source run ∨
        (source∈ps ∧ run∈(read out.rows source).ids) := by
  induction ps generalizing out acc calls visits work with
  | nil => simp [drainLoop]
  | cons p ps ih =>
    rw [drainLoop,ih,hasDelivery_cons,take_read]
    by_cases hs : source=p
    · subst source
      simp [take,or_comm]
    · simp [take,hs,Ne.symm hs]

theorem drain_has (ps : List Nat) (out : Built) (source run : Nat) :
    HasDelivery (drain ps out).deliveries source run ↔
      source∈ps ∧ run∈(read out.rows source).ids := by
  simpa [drain,HasDelivery] using drainLoop_has ps out [] 0 0 0 source run

end REWB.MaskedSourceFanout
