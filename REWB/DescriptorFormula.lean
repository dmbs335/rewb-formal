import REWB.ProjectionSolver

/-! Bridge from finite-orbit descriptors to affine DNF. In a fixed-phase
    periodic problem the exponent is an affine difference of block
    coordinates. The finite initial exceptions become equalities; each
    periodic tail becomes a lower bound plus divisibility. -/
namespace REWB.AffineProjection
open REWB.FiniteOrbit

def exactCount (t : Aff) (v : Nat) : Conj :=
  [.le (t.sub (.lit (v:Int))),.le ((Aff.lit (v:Int)).sub t)]

theorem exactCount_correct (t : Aff) (v : Nat) (env : List Int) :
    Holds (exactCount t v) env ↔ t.eval env=(v:Int) := by
  constructor
  · intro h
    have ha := h (.le (t.sub (.lit (v:Int)))) (by simp [exactCount])
    have hb := h (.le ((Aff.lit (v:Int)).sub t)) (by simp [exactCount])
    change (t.sub (.lit (v:Int))).eval env≤0 at ha
    change ((Aff.lit (v:Int)).sub t).eval env≤0 at hb
    rw [Aff.eval_sub,Aff.eval] at ha hb
    omega
  · intro h a ha
    simp only [exactCount,List.mem_cons] at ha
    rcases ha with h1|h1|h1
    · subst a
      simp [Atom.holds,Aff.eval_sub,Aff.eval,h]
    · subst a
      simp [Atom.holds,Aff.eval_sub,Aff.eval,h]
    · simp at h1

def progression (t : Aff) (start period : Nat) : Conj :=
  [.le ((Aff.lit (start:Int)).sub t),
    .dvd period (t.sub (.lit (start:Int)))]

theorem progression_correct (t : Aff) (start period k : Nat)
    (env : List Int) (ht : t.eval env=(k:Int)) :
    Holds (progression t start period) env ↔
      ∃ m : Nat,k=start+m*period := by
  have he : (t.sub (.lit (start:Int))).eval env=(k:Int)-(start:Int) := by
    rw [Aff.eval_sub,ht,Aff.eval]
  have hrev : ((Aff.lit (start:Int)).sub t).eval env=(start:Int)-(k:Int) := by
    rw [Aff.eval_sub,ht,Aff.eval]
  constructor
  · intro h
    have ha := h (.le ((Aff.lit (start:Int)).sub t)) (by simp [progression])
    have hd := h (.dvd period (t.sub (.lit (start:Int)))) (by simp [progression])
    change ((Aff.lit (start:Int)).sub t).eval env≤0 at ha
    change (period:Int)∣(t.sub (.lit (start:Int))).eval env at hd
    rw [hrev] at ha
    rw [he] at hd
    have hle : start≤k := by omega
    have hsub : ((k-start:Nat):Int)=(k:Int)-(start:Int) := by omega
    rw [← hsub] at hd
    have hnat : period∣k-start := by
      simpa using (Int.ofNat_dvd_right.mp hd)
    obtain ⟨m,hm⟩ := hnat
    refine ⟨m,?_⟩
    rw [Nat.mul_comm m period]
    omega
  · rintro ⟨m,hm⟩ a ha
    simp only [progression,List.mem_cons] at ha
    rcases ha with h1|h1|h1
    · subst a
      change ((Aff.lit (start:Int)).sub t).eval env≤0
      rw [hrev]
      omega
    · subst a
      change (period:Int)∣(t.sub (.lit (start:Int))).eval env
      rw [he]
      refine ⟨(m:Int),?_⟩
      rw [hm,Int.ofNat_add,Int.ofNat_mul,Int.mul_comm (m:Int) (period:Int)]
      omega
    · simp at h1

def descriptorFormula (D : Descriptor) (t : Aff) : Formula :=
  ((D.initialCounts.filter (fun k=>decide (k<D.threshold))).map (exactCount t))++
    (D.residues.map (fun r=>progression t (D.threshold+r) D.period))

theorem descriptorFormula_good (D : Descriptor) (t : Aff) (hp : 0<D.period) :
    FormulaGood (descriptorFormula D t) := by
  intro C hC
  rcases List.mem_append.mp hC with h|h
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    intro a ha
    simp only [exactCount,List.mem_cons] at ha
    rcases ha with h1|h1|h1
    · subst a; trivial
    · subst a; trivial
    · simp at h1
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
    intro a ha
    simp only [progression,List.mem_cons] at ha
    rcases ha with h1|h1|h1
    · subst a; trivial
    · subst a; exact hp
    · simp at h1

theorem descriptorFormula_correct (D : Descriptor) (t : Aff) (env : List Int)
    (k : Nat) (ht : t.eval env=(k:Int)) (hp : 0<D.period)
    (hr : ∀ r,r∈D.residues→r<D.period) :
    Satisfies (descriptorFormula D t) env ↔ D.test k=true := by
  rw [descriptor_ap D hp hr k]
  constructor
  · rintro ⟨C,hC,h⟩
    rcases List.mem_append.mp hC with h1|h1
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h1
      have he := (exactCount_correct t v env).mp h
      have hkv : k=v := by rw [ht] at he; omega
      subst v
      have hh := List.mem_filter.mp hv
      exact Or.inl ⟨of_decide_eq_true hh.2,hh.1⟩
    · obtain ⟨r,hm,rfl⟩ := List.mem_map.mp h1
      obtain ⟨m,he⟩ := (progression_correct t (D.threshold+r) D.period k env ht).mp h
      exact Or.inr ⟨r,hm,m,he⟩
  · rintro (⟨hk,hm⟩|⟨r,hm,m,he⟩)
    · refine ⟨exactCount t k,List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨k,List.mem_filter.mpr ⟨hm,by simp [hk]⟩,rfl⟩)),?_⟩
      exact (exactCount_correct t k env).mpr ht
    · refine ⟨progression t (D.threshold+r) D.period,
        List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨r,hm,rfl⟩)),?_⟩
      exact (progression_correct t (D.threshold+r) D.period k env ht).mpr ⟨m,he⟩

end REWB.AffineProjection
