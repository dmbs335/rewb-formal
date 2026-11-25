import REWB.IndexedGrid
import REWB.ThresholdBudget
import REWB.CountedJoin

/-! The actual returned rank-preparation, LCE-query and probe counters of
the grid generator fit the rounded target. This does not count the full
matcher or supply a runtime allocation/bit-operation semantics. -/
namespace REWB.IndexedGridAccounting
open REWB.IndexedGrid
variable {σ : Nat}

def height (n : Nat) : Nat := (n+2).log2+1

theorem height_pos (n : Nat) : 1≤height n := by unfold height; omega

theorem depth_le (n : Nat) : n.log2+1≤height n :=
  Nat.add_le_add_right (CountedJoin.log2_mono (by omega : n≤n+2)) 1

theorem width_le (σ n : Nat) : RankIndex.width σ n≤(σ+2)*height n := by
  have hh:=height_pos n
  unfold RankIndex.width RankIndex.bound
  by_cases hn : σ+1≤n+1
  · rw [Nat.max_eq_left hn]
    have hd:=Nat.add_le_add_right (CountedJoin.log2_mono (by omega : n+1≤n+2)) 1
    have hm:=Nat.mul_le_mul_right (height n) (by omega : 1≤σ+2)
    simp only [Nat.one_mul] at hm
    exact Nat.le_trans hd hm
  · rw [Nat.max_eq_right (by omega)]
    have hd:=Nat.log2_le_self (σ+1)
    have hm:=Nat.mul_le_mul_left (σ+2) hh
    simp only [Nat.mul_one] at hm
    omega

theorem probes_bound (n s : Nat) (hs : 0<s) :
    (n/s+1)*(n+1)≤n^2/s+2*n+1 := by
  have hp : (n/s*n)*s≤n*n := by
    calc
      _ = (n/s*s)*n := by simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      _ ≤ n*n := Nat.mul_le_mul_right n (Nat.div_mul_le_self n s)
  have hq := (Nat.le_div_iff_mul_le hs).mpr hp
  have hd:=Nat.div_le_self n s
  simp only [Nat.pow_two,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
  omega

theorem ledger_lowers (n : Nat) :
    n+1≤ThresholdBudget.ledger n ∧
    n^2/ThresholdBudget.block n+1≤ThresholdBudget.ledger n := by
  have ht:=ThresholdBudget.base_pos n
  have hp : 1≤((ThresholdBudget.base n)^13)^2 := Nat.pow_pos (Nat.pow_pos ht)
  have hn:=Nat.mul_le_mul_left n hp
  simp only [Nat.mul_one] at hn
  have initial_le (a b c d e f g h : Nat) : a+b≤a+b+c+d+e+f+g+h := by omega
  have hfirst : 1≤n^2/(ThresholdBudget.base n)^3+1 :=
    Nat.le_add_left 1 (n^2/(ThresholdBudget.base n)^3)
  have hsum:=Nat.add_le_add hfirst hn
  have hprefix:=initial_le (n^2/(ThresholdBudget.base n)^3+1)
    (n*((ThresholdBudget.base n)^13)^2)
    (n^2*((ThresholdBudget.base n)^3)^2/(ThresholdBudget.base n)^13+1)
    (n^2*((ThresholdBudget.base n)^3)^2/(ThresholdBudget.base n)^13+1)
    (n^2*((ThresholdBudget.base n)^3)^2/(ThresholdBudget.base n)^9+1)
    (n*(ThresholdBudget.base n)^13*((ThresholdBudget.base n)^3)^2)
    (n*((ThresholdBudget.base n)^3)^2) (n*((ThresholdBudget.base n)^9)^4)
  unfold ThresholdBudget.ledger ThresholdBudget.ledgerAt ThresholdBudget.block
  exact ⟨Nat.le_trans (by simpa only [Nat.add_comm 1 n] using hsum) hprefix,
    Nat.le_trans (Nat.le_add_right _ _) hprefix⟩

theorem rounded_probes (n : Nat) :
    (n/ThresholdBudget.block n+1)*(n+1)≤3*ThresholdBudget.ledger n := by
  have hs : 0<ThresholdBudget.block n := Nat.pow_pos (ThresholdBudget.base_pos n)
  have hp:=probes_bound n (ThresholdBudget.block n) hs
  have hl:=ledger_lowers n
  omega

theorem preparation_factor (σ n : Nat) :
    (n.log2+1)*(16*RankIndex.width σ n+4)+1≤
      (16*(σ+2)+5)*(height n)^2 := by
  have hh:=height_pos n
  have hd:=depth_le n
  have hw:=width_le σ n
  have hi : 16*RankIndex.width σ n+4≤(16*(σ+2)+4)*height n := by
    have hm:=Nat.mul_le_mul_left 16 hw
    simp only [Nat.add_mul,Nat.mul_assoc] at hm ⊢
    omega
  have hm:=Nat.mul_le_mul hd hi
  have hp : 1≤(height n)^2 := Nat.pow_pos (by omega)
  have he : height n*((16*(σ+2)+4)*height n)=
      (16*(σ+2)+4)*(height n)^2 := by
    simp only [Nat.pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  rw [he] at hm
  have he' : (16*(σ+2)+5)*(height n)^2=
      (16*(σ+2)+4)*(height n)^2+(height n)^2 := by
    rw [show 16*(σ+2)+5=(16*(σ+2)+4)+1 by omega,Nat.add_mul,Nat.one_mul]
  rw [he']
  omega

def measured (f : Nat→Fin σ) (n : Nat) : Nat :=
  let r:=generate f n (ThresholdBudget.block n)
  r.preparation+r.queryWork+r.probes

def coefficient (σ : Nat) : Nat := 2*(16*(σ+2)+5)+87

theorem measured_bound (f : Nat→Fin σ) (n : Nat) :
    measured f n≤coefficient σ*ThresholdBudget.ledger n*(height n)^2 := by
  let r:=generate f n (ThresholdBudget.block n)
  let H:=height n
  let L:=ThresholdBudget.ledger n
  have hc:=generate_counts f n (ThresholdBudget.block n)
  have hp:=rounded_probes n
  have hl: n+1≤L := (ledger_lowers n).1
  have hh:1≤H:=height_pos n
  have hh2:1≤H^2:=Nat.pow_pos (by omega)
  have hH:H≤H^2:=by simpa only [Nat.pow_two,Nat.mul_one] using Nat.mul_le_mul_left H hh
  have ha : r.preparation≤(2*(16*(σ+2)+5))*(L*H^2) := by
    have hm:=Nat.mul_le_mul hl (preparation_factor σ n)
    have hm2:=Nat.mul_le_mul_left 2 hm
    have he : 2*(L*((16*(σ+2)+5)*H^2))=(2*(16*(σ+2)+5))*(L*H^2) := by
      simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [he] at hm2
    exact Nat.le_trans hc.2.2.2 hm2
  have hb : r.queryWork≤84*(L*H^2) := by
    have hd:=depth_le n
    have hq : 26*(n.log2+1)+2≤28*H := by change n.log2+1≤H at hd; omega
    have hm:=Nat.mul_le_mul hq hp
    have hm':r.queryWork≤84*(L*H) := by
      have he : (28*H)*(3*L)=84*(L*H) := by
        calc
          _ = (28*3)*(L*H) := by ac_rfl
          _ = _ := rfl
      rw [he] at hm
      exact Nat.le_trans hc.2.2.1 hm
    exact Nat.le_trans hm' (Nat.mul_le_mul_left 84 (Nat.mul_le_mul_left L hH))
  have hc' : r.probes≤3*(L*H^2) := by
    have hr:r.probes≤3*L := by rw [hc.1]; exact hp
    have hm:=Nat.mul_le_mul_left L hh2
    simp only [Nat.mul_one] at hm
    exact Nat.le_trans hr (Nat.mul_le_mul_left 3 hm)
  change r.preparation+r.queryWork+r.probes≤_
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

end REWB.IndexedGridAccounting
