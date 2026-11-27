import REWB.RankIndexSchedule
import REWB.IndexedGridAccounting

/-! The actual six returned counters of the duplicate-free sampled-run
generator satisfy the rounded exponent target. This theorem covers the
index/run-construction counters only; it does not establish a cost bound
for the complete REWB matcher or a compiled-machine memory semantics. -/
namespace REWB.RankIndexScheduleAccounting
open REWB.IndexedGridAccounting
variable {σ : Nat}

def measured (f : Nat→Fin σ) (n : Nat) : Nat :=
  let r:=RankIndexSchedule.generate f n (ThresholdBudget.block n)
  r.preparation+r.divisorWork+r.queryWork+r.periodWork+r.probes+r.dedupWork

def coefficient (σ : Nat) : Nat := 2*(16*(σ+2)+5)+240

theorem measured_bound (f : Nat→Fin σ) (n : Nat) :
    measured f n≤coefficient σ*ThresholdBudget.ledger n*(height n)^2 := by
  let r:=RankIndexSchedule.generate f n (ThresholdBudget.block n)
  let H:=height n
  let L:=ThresholdBudget.ledger n
  let A:=n/ThresholdBudget.block n+1
  have hc:=RankIndexSchedule.generate_counts f n (ThresholdBudget.block n)
  have hprobes : A*(n+1)≤3*L:=rounded_probes n
  have hl : n+1≤L:=(ledger_lowers n).1
  have hn : n≤L:=by omega
  have hh : 1≤H:=height_pos n
  have hdepth : n.log2+1≤H:=depth_le n
  have hh2 : 1≤H^2:=Nat.pow_pos (by omega)
  have hH : H≤H^2:=by
    simpa only [Nat.pow_two,Nat.mul_one] using Nat.mul_le_mul_left H hh
  have ha : A*n≤3*L:=Nat.le_trans (Nat.mul_le_mul_left A (by omega : n≤n+1)) hprobes
  have hprep : r.preparation≤(2*(16*(σ+2)+5))*(L*H^2) := by
    have hm:=Nat.mul_le_mul_left 2 (Nat.mul_le_mul hl (preparation_factor σ n))
    have he : 2*(L*((16*(σ+2)+5)*H^2))=(2*(16*(σ+2)+5))*(L*H^2) := by ac_rfl
    rw [he] at hm
    exact Nat.le_trans hc.2.2.2.1 hm
  have hquery : r.queryWork≤84*(L*H^2) := by
    have hq : 26*(n.log2+1)+2≤28*H := by omega
    have hm:=Nat.mul_le_mul hq hprobes
    have he : (28*H)*(3*L)=84*(L*H) := by
      calc
        _ = (28*3)*(L*H) := by ac_rfl
        _ = _ := rfl
    rw [he] at hm
    have hq' : r.queryWork≤84*(L*H) := by
      have he' : A*((26*(n.log2+1)+2)*(n+1))=
          (26*(n.log2+1)+2)*(A*(n+1)) := by ac_rfl
      have hactual : r.queryWork≤A*((26*(n.log2+1)+2)*(n+1)):=hc.2.1
      rw [he'] at hactual
      exact Nat.le_trans hactual hm
    exact Nat.le_trans hq' (Nat.mul_le_mul_left 84 (Nat.mul_le_mul_left L hH))
  have hdivisor : r.divisorWork≤3*(L*H^2) := by
    have hm:=Nat.le_trans (Nat.mul_le_mul hn hdepth) (Nat.mul_le_mul_left L hH)
    exact Nat.le_trans hc.2.2.2.2.1 (Nat.mul_le_mul_left 3 hm)
  have hprobe : r.probes≤3*(L*H^2) := by
    have hp : r.probes≤3*L:=by rw [hc.1]; exact hprobes
    have hm:=Nat.mul_le_mul_left L hh2
    simp only [Nat.mul_one] at hm
    exact Nat.le_trans hp (Nat.mul_le_mul_left 3 hm)
  have hperiod : r.periodWork≤57*(L*H^2) := by
    have hp : 13*(n.log2+1)+6≤19*H:=by omega
    have hm:=Nat.mul_le_mul hdepth hp
    have he : H*(19*H)=19*H^2:=by simp only [Nat.pow_two]; ac_rfl
    rw [he] at hm
    have hall:=Nat.mul_le_mul ha hm
    have he' : (3*L)*(19*H^2)=57*(L*H^2) := by
      calc
        _ = (3*19)*(L*H^2) := by ac_rfl
        _ = _ := rfl
    rw [he'] at hall
    have hactual : r.periodWork≤A*((n*(n.log2+1))*(13*(n.log2+1)+6)):=hc.2.2.1
    have he'' : A*((n*(n.log2+1))*(13*(n.log2+1)+6))=
        (A*n)*((n.log2+1)*(13*(n.log2+1)+6)) := by ac_rfl
    rw [he''] at hactual
    exact Nat.le_trans hactual hall
  have hdedup : r.dedupWork≤93*(L*H^2) := by
    have hd : (n+1).log2+1≤H:=
      Nat.add_le_add_right (CountedJoin.log2_mono (by omega : n+1≤n+2)) 1
    have hq : 26*((n+1).log2+1)+5≤31*H:=by omega
    have hm:=Nat.mul_le_mul hq hprobes
    have he : (31*H)*(3*L)=93*(L*H) := by
      calc
        _ = (31*3)*(L*H) := by ac_rfl
        _ = _ := rfl
    rw [he] at hm
    have hactual : r.dedupWork≤93*(L*H):=Nat.le_trans hc.2.2.2.2.2 hm
    exact Nat.le_trans hactual (Nat.mul_le_mul_left 93 (Nat.mul_le_mul_left L hH))
  change r.preparation+r.divisorWork+r.queryWork+r.periodWork+r.probes+r.dedupWork≤_
  change _≤coefficient σ*L*H^2
  rw [Nat.mul_assoc]
  unfold coefficient
  rw [Nat.add_mul]
  omega

def targetConstant (σ : Nat) : Nat := (coefficient σ)^13*ThresholdBudget.constant

set_option exponentiation.threshold 1024 in
theorem measured_power (f : Nat→Fin σ) (n : Nat) :
    (measured f n)^13≤targetConstant σ*(n+2)^25*(height n)^26 := by
  have h:=Nat.pow_le_pow_left (measured_bound f n) 13
  rw [Nat.mul_pow,Nat.mul_pow,← Nat.pow_mul] at h
  have hl:=ThresholdBudget.ledger_power n
  have hm:=Nat.mul_le_mul_right ((height n)^26)
    (Nat.mul_le_mul_left ((coefficient σ)^13) hl)
  exact Nat.le_trans h (by simpa only [targetConstant,Nat.mul_assoc] using hm)

theorem measured_target (texts : Nat→Nat→Fin σ) :
    Spec.Target25Over13 (fun n=>measured (texts n) n) := by
  refine ⟨targetConstant σ,26,?_,?_⟩
  · apply Nat.mul_pos
    · apply Nat.pow_pos
      unfold coefficient
      omega
    · exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (Nat.pow_pos (by decide)))
  · intro n
    exact measured_power (texts n) n

end REWB.RankIndexScheduleAccounting
