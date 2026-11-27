import REWB.MaskedSourceFanoutDrain

/-! Construct every source-to-run address from the actual complete cubic
run enumerator. Aggregate delivery is bounded by cubic-run mass, including
repeated source-removal requests. No run list is supplied to `prepare`. -/
namespace REWB.MaskedSourceFanout
open REWB.RunGeometry REWB.MaskedPeriodic.Batch
variable {σ : Nat}

theorem length_le_span (Rs : List Bounds) : Rs.length≤totalSpan Rs := by
  induction Rs with
  | nil => simp [totalSpan]
  | cons R Rs ih => simp only [List.length_cons,totalSpan,span]; omega

structure Prepared where
  runs : Array Bounds
  sources : Built
  enumerationWork : Nat
  preparationWork : Nat
  deriving Repr

def prepare (text : Array (Fin σ)) (fallback : Fin σ) : Prepared :=
  let rs:=MaskedOrdered.Owner.enumerateAuto text fallback
  let out:=build text.size rs.runs
  ⟨rs.runs.toArray,out,rs.work,out.work+rs.runs.length+2⟩

theorem enumerated_bounds (text : Array (Fin σ)) (fallback : Fin σ) :
    ∀ R,R∈(MaskedOrdered.Owner.enumerateAuto text fallback).runs → R.lo≤R.hi ∧ R.hi≤text.size := by
  intro R hR
  have h:=(MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mp hR
  exact ⟨Nat.le_of_lt h.1.1,h.1.2.1⟩

theorem prepare_mem (text : Array (Fin σ)) (fallback : Fin σ) (p k : Nat) :
    k∈(read (prepare text fallback).sources.rows p).ids ↔
      ∃ R,(prepare text fallback).runs[k]?=some R ∧ R.lo≤p ∧ p≤R.hi := by
  simpa only [prepare,List.getElem?_toArray] using
    build_mem text.size p k _ (enumerated_bounds text fallback)

theorem prepare_good (text : Array (Fin σ)) (fallback : Fin σ) :
    Good (prepare text fallback).sources :=
  build_good text.size _ (enumerated_bounds text fallback)

theorem prepare_nodup (text : Array (Fin σ)) (fallback : Fin σ) (p : Nat) :
    (read (prepare text fallback).sources.rows p).ids.Nodup :=
  build_nodup text.size p _ (enumerated_bounds text fallback)

theorem prepare_memberships (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).sources.memberships≤6*text.size*(text.size.log2+1) := by
  change (build text.size _).memberships≤_
  rw [build_memberships]
  exact enumerated_span text fallback

theorem prepare_work (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).preparationWork≤
      text.size+3+66*text.size*(text.size.log2+1) ∧
    (prepare text fallback).enumerationWork≤
      MaskedRunEnumerationCost.coefficient σ*(text.size+1)*((text.size+1).log2+1)^2 := by
  refine ⟨?_,MaskedRunEnumerationCost.enumerate_work text fallback⟩
  have hs:=enumerated_span text fallback
  have hl:=length_le_span (MaskedOrdered.Owner.enumerateAuto text fallback).runs
  have hm:=Nat.mul_le_mul_left 11 hs
  change (build text.size _).work+_+2≤_
  rw [build_work]
  have he : 11*(6*text.size*(text.size.log2+1))=66*text.size*(text.size.log2+1) := by
    simp only [←Nat.mul_assoc]
  rw [he] at hm
  omega

theorem prepare_delivery_bound (text : Array (Fin σ)) (fallback : Fin σ) (ps : List Nat) :
    deliverySize (drain ps (prepare text fallback).sources).deliveries≤
      6*text.size*(text.size.log2+1) :=
  Nat.le_trans (drain_size_bound ps _ (prepare_good text fallback))
    (prepare_memberships text fallback)

theorem prepare_delivery_exact (text : Array (Fin σ)) (fallback : Fin σ)
    (ps : List Nat) (source run : Nat) :
    HasDelivery (drain ps (prepare text fallback).sources).deliveries source run ↔
      source∈ps ∧ ∃ R,(prepare text fallback).runs[run]?=some R ∧
        R.lo≤source ∧ source≤R.hi := by
  rw [drain_has,prepare_mem]

end REWB.MaskedSourceFanout
