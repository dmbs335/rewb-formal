import REWB.MaskedPeriodic

/-! Exact arithmetic connection to two disjoint copies of length
    L=a*q+rho at source block 0 and target block k. The containing run
    ends at N*q+eta, with rho,eta<q. This proves the three compiler cases
    exhaust the physical disjointness/end constraints; it does not prove
    the text is periodic or discover its runs.
-/
namespace REWB.MaskedPeriodic

def Physical (q eta rho N a k : Nat) : Prop :=
  2≤a ∧ a*q+rho≤k*q ∧ k*q+a*q+rho≤N*q+eta

theorem block_bound (q eta rho N u : Nat) (hr : rho<q) (he : eta<q) :
    u*q+rho≤N*q+eta ↔ u<N ∨ (u=N ∧ rho≤eta) := by
  constructor
  · intro h
    by_cases hu : u<N
    · exact Or.inl hu
    · have hle : u≤N := by
        by_cases hh : u≤N
        · exact hh
        · have hm := Nat.mul_le_mul_right q (show N+1≤u by omega)
          rw [Nat.add_mul,Nat.one_mul] at hm
          omega
      have huN : u=N := by omega
      subst u
      exact Or.inr ⟨rfl,by omega⟩
  · rintro (hu|⟨rfl,hre⟩)
    · have hm := Nat.mul_le_mul_right q (show u+1≤N by omega)
      rw [Nat.add_mul,Nat.one_mul] at hm
      omega
    · omega

theorem disjoint_positive (q rho a k : Nat) (hr0 : 0<rho) (hr : rho<q) :
    a*q+rho≤k*q ↔ a+1≤k := by
  constructor
  · intro h
    by_cases hh : a+1≤k
    · exact hh
    · have hm := Nat.mul_le_mul_right q (show k≤a by omega)
      omega
  · intro h
    have hm := Nat.mul_le_mul_right q h
    rw [Nat.add_mul,Nat.one_mul] at hm
    omega

theorem physical_zero (q eta N a k : Nat) (hq : 0<q) (he : eta<q) :
    Physical q eta 0 N a k ↔ Geometry .zero N a k := by
  have hd : a*q+0≤k*q ↔ a≤k := by
    simp only [Nat.add_zero]
    exact ⟨fun h=>Nat.le_of_mul_le_mul_right h hq,fun h=>Nat.mul_le_mul_right q h⟩
  have hb := block_bound q eta 0 N (k+a) hq he
  rw [Nat.add_mul] at hb
  unfold Physical Geometry
  rw [hd,hb]
  simp only [Branch.carry,Branch.endOK,Nat.add_zero]
  omega

theorem physical_positive (q eta rho N a k : Nat) (hr0 : 0<rho)
    (hr : rho<q) (he : eta<q) :
    Physical q eta rho N a k ↔
      Geometry .interior N a k ∨ (Geometry .ending N a k ∧ rho≤eta) := by
  have hb := block_bound q eta rho N (k+a) hr he
  rw [Nat.add_mul] at hb
  unfold Physical
  rw [disjoint_positive q rho a k hr0 hr,hb]
  simp only [Geometry,Branch.carry,Branch.endOK]
  omega

theorem physical_long (q eta rho N a k : Nat) (h : Physical q eta rho N a k) :
    2*q≤a*q+rho := by
  have hh := Nat.mul_le_mul_right q h.1
  omega

end REWB.MaskedPeriodic
