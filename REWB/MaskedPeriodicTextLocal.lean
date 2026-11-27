import REWB.MaskedPeriodicTextFactors

/-! Eliminate the word-family abstraction on a genuinely periodic text
    accessor. Quotient/remainder decomposition ranges over every long
    capture length, and the three branches preserve one actual rho.
-/
namespace REWB.MaskedPeriodic.Text
open REWB.Periodic
open REWB.P2Periodic (factor)
variable {α : Type}

def Factors (b c e : DFA α) (f : Nat→α) (n q : Nat) (tail : Word α) (L k : Nat) : Prop :=
  b.accepts (factor f 0 L) ∧ c.accepts (factor f L (k*q)) ∧
    e.accepts (factor f (k*q+L) n++tail)

def localFamily (b c e : DFA α) (f : Nat→α) (tail : Word α) (q N eta : Nat)
    (branch : Branch) (rho a k : Nat) : Prop :=
  match branch with
  | .zero => WordFamily b c e (segment f 0 q) [] [] [] (segment f 0 eta++tail) .zero N a k
  | .interior => WordFamily b c e (segment f 0 q) (segment f 0 rho)
      (factor f rho q) (factor f rho q) (segment f 0 eta++tail) .interior N a k
  | .ending => WordFamily b c e (segment f 0 q) (segment f 0 rho)
      (factor f rho q) (factor f rho eta) tail .ending N a k

theorem local_zero (b c e : DFA α) (f : Nat→α) (tail : Word α) (q N eta a k : Nat)
    (hq : 0<q) (he : eta<q) (hp : Period f (N*q+eta) q) :
    localFamily b c e f tail q N eta .zero 0 a k ↔
      Geometry .zero N a k ∧ Factors b c e f (N*q+eta) q tail (a*q) k := by
  by_cases hg : Geometry .zero N a k
  · have hphys := (physical_zero q eta N a k hq he).mpr hg
    have ha : a≤k := by have hh := hg.2.1; simpa only [Branch.carry,Nat.add_zero] using hh
    have hn : k+a≤N := hg.2.2
    have hcap := capture f (N*q+eta) q a 0 hp (by have hh := hphys.2.2; omega)
    simp only [Nat.add_zero,segment,List.append_nil] at hcap
    have hgap := zero_gap f (N*q+eta) q a k hp ha (by have hh := hphys.2.2; omega)
    have hsuf := zero_suffix f (N*q+eta) q (k+a) N eta hp hn (Nat.le_refl _)
    simp only [Nat.add_mul,Nat.sub_add_eq] at hsuf
    simp only [localFamily,WordFamily,Factors,hg,true_and,hcap,hgap,hsuf,
      Branch.carry,tailCount,Nat.sub_zero,List.nil_append,List.append_nil,List.append_assoc]
  · simp only [localFamily,WordFamily,hg,false_and]

theorem local_interior (b c e : DFA α) (f : Nat→α) (tail : Word α) (q N eta rho a k : Nat)
    (hr0 : 0<rho) (hr : rho<q) (he : eta<q) (hp : Period f (N*q+eta) q) :
    localFamily b c e f tail q N eta .interior rho a k ↔
      Geometry .interior N a k ∧ Factors b c e f (N*q+eta) q tail (a*q+rho) k := by
  by_cases hg : Geometry .interior N a k
  · have hphys := (physical_positive q eta rho N a k hr0 hr he).mpr (Or.inl hg)
    have ha : a+1≤k := hg.2.1
    have hn : k+a+1≤N := hg.2.2
    have hcap := capture f (N*q+eta) q a rho hp (by have hh := hphys.2.2; omega)
    have hgap := positive_gap f (N*q+eta) q a k rho hp (Nat.le_of_lt hr) ha
      (by have hh := hphys.2.2; omega)
    have hsuf := interior_suffix f (N*q+eta) q (k+a) rho N eta hp (Nat.le_of_lt hr) hn
      (Nat.le_refl _)
    simp only [Nat.add_mul,Nat.sub_add_eq,Nat.add_assoc] at hsuf
    simp only [localFamily,WordFamily,Factors,hg,true_and,hcap,hgap,hsuf,
      Branch.carry,tailCount,List.append_assoc]
  · simp only [localFamily,WordFamily,hg,false_and]

theorem local_ending (b c e : DFA α) (f : Nat→α) (tail : Word α) (q N eta rho a k : Nat)
    (hr0 : 0<rho) (hr : rho≤eta) (he : eta<q) (hp : Period f (N*q+eta) q) :
    localFamily b c e f tail q N eta .ending rho a k ↔
      Geometry .ending N a k ∧ Factors b c e f (N*q+eta) q tail (a*q+rho) k := by
  by_cases hg : Geometry .ending N a k
  · have hphys := (physical_positive q eta rho N a k hr0 (by omega) he).mpr (Or.inr ⟨hg,hr⟩)
    have ha : a+1≤k := hg.2.1
    have hn : k+a=N := hg.2.2
    have hcap := capture f (N*q+eta) q a rho hp (by have hh := hphys.2.2; omega)
    have hgap := positive_gap f (N*q+eta) q a k rho hp (by omega) ha
      (by have hh := hphys.2.2; omega)
    have hpos : k*q+(a*q+rho)=N*q+rho := by rw [←Nat.add_assoc,←Nat.add_mul,hn]
    have hsuf : factor f (k*q+(a*q+rho)) (N*q+eta)=factor f rho eta := by
      rw [hpos]
      exact ending_suffix f (N*q+eta) q rho N eta hp hr (Nat.le_refl _)
    simp only [localFamily,WordFamily,Factors,hg,true_and,hcap,hgap,hsuf,
      Branch.carry,tailCount,repeatWord,List.append_nil]
  · simp only [localFamily,WordFamily,hg,false_and]

def FamilyWitness (b c e : DFA α) (f : Nat→α) (tail : Word α) (q N eta : Nat)
    (mask : Array Bool) (base len s : Nat) : Prop :=
  (∃ a k,localFamily b c e f tail q N eta .zero 0 a k ∧ Marked mask base len q s k) ∨
  (∃ rho a k,0<rho ∧ rho<q ∧ localFamily b c e f tail q N eta .interior rho a k ∧
    Marked mask base len q s k) ∨
  (∃ rho a k,0<rho ∧ rho≤eta ∧ localFamily b c e f tail q N eta .ending rho a k ∧
    Marked mask base len q s k)

def LocalWitness (b c e : DFA α) (f : Nat→α) (tail : Word α) (q n : Nat)
    (mask : Array Bool) (base len s : Nat) : Prop :=
  ∃ L k,2*q≤L ∧ L≤k*q ∧ k*q+L≤n ∧ Factors b c e f n q tail L k ∧
    Marked mask base len q s k

theorem families_iff (b c e : DFA α) (f : Nat→α) (tail : Word α) (q N eta : Nat)
    (mask : Array Bool) (base len s : Nat) (hq : 0<q) (he : eta<q)
    (hp : Period f (N*q+eta) q) :
    FamilyWitness b c e f tail q N eta mask base len s ↔
      LocalWitness b c e f tail q (N*q+eta) mask base len s := by
  constructor
  · rintro (⟨a,k,hf,hm⟩|⟨rho,a,k,hr0,hr,hf,hm⟩|⟨rho,a,k,hr0,hr,hf,hm⟩)
    · obtain ⟨hg,hf⟩ := (local_zero b c e f tail q N eta a k hq he hp).mp hf
      have hphys := (physical_zero q eta N a k hq he).mpr hg
      have hl := physical_long q eta 0 N a k hphys
      exact ⟨a*q,k,by simpa only [Nat.add_zero] using hl,
        by simpa only [Nat.add_zero] using hphys.2.1,
        by simpa only [Nat.add_zero] using hphys.2.2,hf,hm⟩
    · obtain ⟨hg,hf⟩ := (local_interior b c e f tail q N eta rho a k hr0 hr he hp).mp hf
      have hphys := (physical_positive q eta rho N a k hr0 hr he).mpr (Or.inl hg)
      exact ⟨a*q+rho,k,physical_long q eta rho N a k hphys,hphys.2.1,
        by simpa only [Nat.add_assoc] using hphys.2.2,hf,hm⟩
    · obtain ⟨hg,hf⟩ := (local_ending b c e f tail q N eta rho a k hr0 hr he hp).mp hf
      have hphys := (physical_positive q eta rho N a k hr0 (by omega) he).mpr (Or.inr ⟨hg,hr⟩)
      exact ⟨a*q+rho,k,physical_long q eta rho N a k hphys,hphys.2.1,
        by simpa only [Nat.add_assoc] using hphys.2.2,hf,hm⟩
  · rintro ⟨L,k,hl,hd,hbound,hf,hm⟩
    let a := L/q
    let rho := L%q
    have ha : 2≤a := (long_quotient q L hq).mp hl
    have hr : rho<q := Nat.mod_lt L hq
    have hL : a*q+rho=L := quotient_length q L
    have hphys : Physical q eta rho N a k := by
      refine ⟨ha,?_,?_⟩
      · rwa [hL]
      · rw [Nat.add_assoc,hL]
        exact hbound
    by_cases hz : rho=0
    · have hzL : a*q=L := by omega
      have hg : Geometry .zero N a k :=
        (physical_zero q eta N a k hq he).mp (by simpa only [hz] using hphys)
      exact Or.inl ⟨a,k,(local_zero b c e f tail q N eta a k hq he hp).mpr
        ⟨hg,by simpa only [hzL] using hf⟩,hm⟩
    · have hr0 : 0<rho := by omega
      rcases (physical_positive q eta rho N a k hr0 hr he).mp hphys with hg|⟨hg,hre⟩
      · exact Or.inr (Or.inl ⟨rho,a,k,hr0,hr,
          (local_interior b c e f tail q N eta rho a k hr0 hr he hp).mpr
            ⟨hg,by simpa only [hL] using hf⟩,hm⟩)
      · exact Or.inr (Or.inr ⟨rho,a,k,hr0,hre,
          (local_ending b c e f tail q N eta rho a k hr0 hre he hp).mpr
            ⟨hg,by simpa only [hL] using hf⟩,hm⟩)

end REWB.MaskedPeriodic.Text
