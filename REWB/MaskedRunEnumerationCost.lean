import REWB.MaskedOrderedOwnerEnumeration

/-! A closed fixed-alphabet bound for the complete cubic-run enumerator's
returned work. This includes suffix/rank preparation, persistent owner
execution, validation and exact deduplication in their stated slot model.
It is not a cost theorem for the full REWB matcher. -/
namespace REWB.MaskedRunEnumerationCost
set_option maxRecDepth 4096
open REWB.MaskedOrdered.Owner
variable {σ : Nat}

def height (n : Nat) : Nat := (n+1).log2+1
def volume (n : Nat) : Nat := (n+1)*(height n)^2
def coefficient (σ : Nat) : Nat := 32*(σ+2)+800

theorem height_pos (n : Nat) : 1≤height n := by unfold height; omega

theorem depth_le (n : Nat) : n.log2+1≤height n :=
  Nat.add_le_add_right (CountedJoin.log2_mono (by omega : n≤n+1)) 1

theorem width_le (σ n : Nat) : RankIndex.width σ n≤(σ+2)*height n := by
  have hh:=height_pos n
  unfold RankIndex.width RankIndex.bound
  by_cases hn : σ+1≤n+1
  · rw [Nat.max_eq_left hn]
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (height n) (by omega : 1≤σ+2)
  · rw [Nat.max_eq_right (by omega)]
    have hd:=Nat.log2_le_self (σ+1)
    have hm:=Nat.mul_le_mul_left (σ+2) hh
    simp only [Nat.mul_one] at hm
    omega

theorem square_bounds (n : Nat) :
    1≤volume n ∧ n+1≤volume n ∧ height n≤volume n ∧ (n+1)*height n≤volume n := by
  have hh:=height_pos n
  have hs : 1≤(height n)^2 := Nat.pow_pos (by omega)
  have hsq : height n≤(height n)^2 := by
    simpa only [Nat.pow_two,Nat.mul_one] using Nat.mul_le_mul_left (height n) hh
  have hn:=Nat.mul_le_mul_left (n+1) hs
  have hnh:=Nat.mul_le_mul_left (n+1) hsq
  have hN:=Nat.mul_le_mul_right (height n) (by omega : 1≤n+1)
  simp only [Nat.mul_one,Nat.one_mul] at hn hN
  change _≤volume n at hn hnh
  exact ⟨by omega,hn,Nat.le_trans hN hnh,hnh⟩

theorem preparation_factor (σ n : Nat) :
    (n.log2+1)*(16*RankIndex.width σ n+4)+1≤(16*(σ+2)+5)*(height n)^2 := by
  have hh:=height_pos n
  have hd:=depth_le n
  have hw:=width_le σ n
  have hi : 16*RankIndex.width σ n+4≤(16*(σ+2)+4)*height n := by
    have hm:=Nat.mul_le_mul_left 16 hw
    simp only [Nat.add_mul,Nat.mul_assoc] at hm ⊢
    omega
  have hm:=Nat.mul_le_mul hd hi
  have hs : 1≤(height n)^2 := Nat.pow_pos (by omega)
  have he : height n*((16*(σ+2)+4)*height n)=(16*(σ+2)+4)*(height n)^2 := by
    simp only [Nat.pow_two]
    ac_rfl
  rw [he] at hm
  have he' : (16*(σ+2)+5)*(height n)^2=(16*(σ+2)+4)*(height n)^2+(height n)^2 := by
    rw [show 16*(σ+2)+5=(16*(σ+2)+4)+1 by omega,Nat.add_mul,Nat.one_mul]
  rw [he']
  omega

theorem preparation_bound (σ n : Nat) :
    preparationBudget σ n≤(2*(16*(σ+2)+5)+324)*volume n := by
  have hh:=height_pos n
  have hd:=depth_le n
  have hv:=square_bounds n
  have hprep : 2*((n+1)*((n.log2+1)*(16*RankIndex.width σ n+4)+1))≤
      (2*(16*(σ+2)+5))*volume n := by
    have hm:=Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (n+1) (preparation_factor σ n))
    have he : 2*((n+1)*((16*(σ+2)+5)*(height n)^2))=
        (2*(16*(σ+2)+5))*volume n := by unfold volume; ac_rfl
    rwa [he] at hm
  have hsort : (13*(n.log2+1)+12)*(8*(n+1)*((n+1).log2+1))≤200*volume n := by
    have hcoef : 13*(n.log2+1)+12≤25*height n := by omega
    have hm:=Nat.mul_le_mul_right (8*(n+1)*height n) hcoef
    have he : (25*height n)*(8*(n+1)*height n)=200*volume n := by
      unfold volume
      rw [Nat.pow_two]
      calc
        _ = (25*8)*((n+1)*(height n*height n)) := by ac_rfl
        _ = _ := rfl
    rw [he] at hm
    exact hm
  have hscalar : 5*(n+1)+3≤8*volume n := by omega
  have htrie : 2*(n+1)*BoundaryTrie.Build.budget n (n+1)≤116*volume n := by
    have hb : BoundaryTrie.Build.budget n (n+1)≤58*height n := by
      unfold BoundaryTrie.Build.budget
      change 13*(n.log2+1)+15*height n+30≤_
      omega
    have hm:=Nat.mul_le_mul_left (2*(n+1)) hb
    have he : 2*(n+1)*(58*height n)=116*((n+1)*height n) := by
      calc
        _ = (2*58)*((n+1)*height n) := by ac_rfl
        _ = _ := rfl
    rw [he] at hm
    exact Nat.le_trans hm (Nat.mul_le_mul_left 116 hv.2.2.2)
  unfold preparationBudget
  rw [Nat.add_mul (2*(16*(σ+2)+5)) 324 (volume n)]
  omega

theorem execution_bound (n : Nat) : executionBudget (height n) n≤416*volume n := by
  have hh:=height_pos n
  have hd:=depth_le n
  have hv:=square_bounds n
  have hlog : (n+1).log2≤height n := by unfold height; omega
  have hprod:=Nat.mul_le_mul_left (n+1) hlog
  have hnode : 2*(n+1)*(28*height n+32)≤120*volume n := by
    have hb : 28*height n+32≤60*height n := by omega
    have hm:=Nat.mul_le_mul_left (2*(n+1)) hb
    have he : 2*(n+1)*(60*height n)=120*((n+1)*height n) := by
      calc
        _ = (2*60)*((n+1)*height n) := by ac_rfl
        _ = _ := rfl
    rw [he] at hm
    exact Nat.le_trans hm (Nat.mul_le_mul_left 120 hv.2.2.2)
  have hlight : ((n+1)*(n+1).log2)*(35*height n+46)≤81*volume n := by
    have hb : 35*height n+46≤81*height n := by omega
    have hm:=Nat.mul_le_mul hprod hb
    have he : ((n+1)*height n)*(81*height n)=81*volume n := by
      unfold volume
      rw [Nat.pow_two]
      ac_rfl
    rwa [he] at hm
  have hevents : (2*((n+1)*(n+1).log2))*(probeBudget (height n) n+26*((n+1).log2+1)+10)≤
      200*volume n := by
    have hb : probeBudget (height n) n+26*((n+1).log2+1)+10≤100*height n := by
      unfold probeBudget
      change 11*height n+26*(n.log2+1)+27+26*height n+10≤_
      omega
    have hm:=Nat.mul_le_mul (Nat.mul_le_mul_left 2 hprod) hb
    have he : (2*((n+1)*height n))*(100*height n)=200*volume n := by
      unfold volume
      rw [Nat.pow_two]
      calc
        _ = (2*100)*((n+1)*(height n*height n)) := by ac_rfl
        _ = _ := rfl
    rwa [he] at hm
  have hscalar : height n+14≤15*volume n := by omega
  unfold executionBudget
  omega

/-- Complete cubic-run enumeration, including preparation, in a closed
near-linear fixed-alphabet bound for the returned operation ledger. -/
theorem enumerate_work (text : Array (Fin σ)) (fallback : Fin σ) :
    (enumerateAuto text fallback).work≤coefficient σ*(text.size+1)*((text.size+1).log2+1)^2 := by
  have he:=enumerateAuto_work text fallback
  have hp:=preparation_bound σ text.size
  have hx:=execution_bound text.size
  have hv:=square_bounds text.size
  have ha : height text.size+2≤3*volume text.size := by omega
  rw [Nat.mul_assoc (coefficient σ) (text.size+1) (((text.size+1).log2+1)^2)]
  change (enumerateAuto text fallback).work≤coefficient σ*volume text.size
  change (enumerateAuto text fallback).work≤preparationBudget σ text.size+
    executionBudget (height text.size) text.size+height text.size+2 at he
  have hc : coefficient σ=2*(16*(σ+2)+5)+324+416+50 := by unfold coefficient; omega
  rw [hc,Nat.add_mul (2*(16*(σ+2)+5)+324+416) 50 (volume text.size),
    Nat.add_mul (2*(16*(σ+2)+5)+324) 416 (volume text.size),
    Nat.add_mul (2*(16*(σ+2)+5)) 324 (volume text.size)]
  rw [Nat.add_mul (2*(16*(σ+2)+5)) 324 (volume text.size)] at hp
  omega

end REWB.MaskedRunEnumerationCost
