import REWB.PeriodicConstructionRuns

/-! Complete construction envelope for the actual small-period run
enumerator. The coefficient is a numeric constant; the dependence on
the period threshold is exactly the existing comparison envelope. -/
namespace REWB.PeriodicConstruction.Runs
open REWB.Periodic REWB.RunGeometry REWB.RunExtension
variable {α : Type} [DecidableEq α]

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def squareEnvelope (p : Nat) : Nat:=2*p*(p+1)+1

theorem squareEnvelope_pos (p : Nat) : 1≤squareEnvelope p := by
  unfold squareEnvelope
  omega

def periodEnvelope (n p : Nat) : Nat:=n+(n+1)*squareEnvelope p

theorem periodEnvelope_ge (n p : Nat) : n+1≤periodEnvelope n p := by
  have h:=Nat.mul_le_mul_left (n+1) (squareEnvelope_pos p)
  simp only [Nat.mul_one] at h
  unfold periodEnvelope
  omega

theorem periodEnvelope_mono (n p Q : Nat) (hp : p≤Q) :
    periodEnvelope n p≤periodEnvelope n Q := by
  unfold periodEnvelope squareEnvelope
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp) (Nat.add_le_add_right hp 1)

theorem period_work (f : Nat→α) (i L p : Nat) :
    (period f i L p).2≤16*L+8 := by
  have ht:=allCounted_work (fun j=>((decide (f (i+j)=f (i+j+p)),1),6))
    (CountedProjection.range (L-p)).1 6 (by intro _ _; exact Nat.le_refl _)
  have hr : (CountedProjection.range (L-p)).2=2*(L-p)+1 :=
    CountedProjection.rangeFrom_steps 0 (L-p)
  simp only [period,hr]
  simp only [CountedProjection.range_value,List.length_range] at ht ⊢
  omega

theorem shorter_work (f : Nat→α) (i p q : Nat) :
    (shorter f i p q).2≤32*p+11 := by
  have hp:=period_work f i (2*p) q
  unfold shorter
  split <;> dsimp only <;> omega

theorem square_work (f : Nat→α) (n i p : Nat) :
    (square f n i p).2≤64*squareEnvelope p := by
  have ha:=period_work f i (2*p) p
  have hb:=allCounted_work (shorter f i p) (CountedProjection.range p).1
    (32*p+11) (fun q _=>shorter_work f i p q)
  have hr : (CountedProjection.range p).2=2*p+1:=CountedProjection.rangeFrom_steps 0 p
  simp only [square,hr]
  simp only [CountedProjection.range_value,List.length_range] at hb ⊢
  simp only [squareEnvelope,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_one,Nat.one_mul] at ha hb ⊢
  rw [Nat.mul_left_comm p 32 p] at hb
  omega

theorem candidate_work (f : Nat→α) (n p : Nat) (T : Array Nat) (i : Nat) :
    (candidate f n p T i).2≤84*squareEnvelope p := by
  have hs:=square_work f n i p
  have hp:=squareEnvelope_pos p
  simp only [candidate,isLeft,endAt]
  split <;> (try split) <;> dsimp only <;> omega

theorem collect_work (f : Nat→α) (n p : Nat) (T : Array Nat) (xs : List Nat) :
    (collect f n p T xs).2≤88*xs.length*squareEnvelope p+1 := by
  induction xs with
  | nil=>simp [collect]
  | cons i is ih=>
    have hh:=candidate_work f n p T i
    have hp:=squareEnvelope_pos p
    simp only [Nat.mul_assoc] at ih
    simp only [collect,List.length_cons,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc]
    omega

theorem forPeriod_work (f : Nat→α) (n p : Nat) :
    (forPeriod f n p).2≤128*(periodEnvelope n p+1) := by
  have hc:=collect_work f n p (materialize (ends f p 0 (n-p)).1.1).1
    (CountedProjection.range (n+1)).1
  have hr : (CountedProjection.range (n+1)).2=2*(n+1)+1:=
    CountedProjection.rangeFrom_steps 0 (n+1)
  simp only [forPeriod,ends_work,materialize_work,ends_length,hr]
  simp only [CountedProjection.range_value,List.length_range] at hc ⊢
  simp only [periodEnvelope,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at hc ⊢
  omega

theorem enumerate_work (f : Nat→α) (n Q : Nat) :
    (enumerate f n Q).2≤136*Q*(periodEnvelope n Q+1)+1 := by
  induction Q with
  | zero=>simp [enumerate]
  | succ Q ih=>
    have here:=forPeriod_work f n (Q+1)
    have hm:=periodEnvelope_mono n Q (Q+1) (by omega)
    have prior:=Nat.le_trans ih (Nat.add_le_add_right
      (Nat.mul_le_mul_left (136*Q) (Nat.add_le_add_right hm 1)) 1)
    have hl:=forPeriod_length f n (Q+1)
    have hn:=periodEnvelope_ge n (Q+1)
    simp only [enumerate,CountedProjection.append_steps]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at here prior ⊢
    omega

/-- The complete original pair is produced with this actual work bound. -/
theorem enumerate_work_closed (f : Nat→α) (n Q : Nat) :
    (enumerate f n Q).2≤
      160*(Q*(n+(n+1)*(2*Q*(Q+1)+1))+n+Q+1) := by
  have h:=enumerate_work f n Q
  simp only [periodEnvelope,squareEnvelope,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at h ⊢
  omega

/-- Includes the final counted cubic filter. No unfiltered enumeration
is repeated to recover the original comparison ledger. -/
theorem cubic_work (f : Nat→α) (n Q : Nat) :
    (cubic f n Q).2≤
      160*(Q*(n+(n+1)*(2*Q*(Q+1)+1))+n+Q+1) := by
  have he:=enumerate_work f n Q
  have hl:=enumerate_length f n Q
  have hm:=Nat.mul_le_mul_left Q (periodEnvelope_ge n Q)
  have hlength:=Nat.le_trans hl hm
  simp only [cubic,cubicFilter_work]
  simp only [periodEnvelope,squareEnvelope,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at he hlength ⊢
  omega

end REWB.PeriodicConstruction.Runs
