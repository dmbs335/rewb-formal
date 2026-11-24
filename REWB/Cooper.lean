import REWB.AffineProjection

/-! Cooper-style elimination for affine conjunctions. Scale the eliminated
    variable to a common multiple of its coefficients, add the divisibility
    guard that restores integrality, and invoke symbolic residue elimination.
    Positive moduli are required; equalities can be written as two inequalities.
    All scaling factors and candidate counts are independent of RHS magnitudes. -/
namespace REWB.AffineProjection

def Atom.good : Atom→Prop
  | .le _ => True
  | .dvd m _ => 0<m

def Good (C : Conj) : Prop := ∀ a,a∈C→a.good

def Atom.factor : Atom→Nat
  | .le a => max 1 a.split.1.natAbs
  | .dvd _ _ => 1

theorem Atom.factor_pos (a : Atom) : 0<a.factor := by
  cases a with
  | le t => exact Nat.lt_of_lt_of_le (by decide : 0<1) (Nat.le_max_left _ _)
  | dvd m t => simp [Atom.factor]

def multiplier : Conj→Nat
  | [] => 1
  | a::as => a.factor*multiplier as

theorem multiplier_pos (C : Conj) : 0<multiplier C := by
  induction C with
  | nil => decide
  | cons a as ih => exact Nat.mul_pos a.factor_pos ih

theorem factor_dvd (C : Conj) (a : Atom) (ha : a∈C) : a.factor∣multiplier C := by
  induction C with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with h|h
    · subst b
      exact ⟨multiplier bs,rfl⟩
    · obtain ⟨k,hk⟩ := ih h
      refine ⟨b.factor*k,?_⟩
      change b.factor*multiplier bs=a.factor*(b.factor*k)
      rw [hk]
      simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]

theorem abs_factor (a : Aff) (ha : a.split.1≠0) :
    (Atom.le a).factor=a.split.1.natAbs := by
  have h : 1≤a.split.1.natAbs := by omega
  exact Nat.max_eq_right h

theorem abs_dvd (C : Conj) (a : Aff) (ha : Atom.le a∈C)
    (hne : a.split.1≠0) : a.split.1.natAbs∣multiplier C := by
  have h := factor_dvd C (.le a) ha
  rwa [abs_factor a hne] at h

def Norm.empty : Norm := ⟨[],[],[],[]⟩

def Norm.merge (N M : Norm) : Norm :=
  ⟨N.lower++M.lower,N.upper++M.upper,N.free++M.free,N.guards++M.guards⟩

theorem Norm.empty_holds (env : List Int) (y : Int) : Norm.empty.holds env y := by
  simp [Norm.empty,Norm.holds,Norm.bounds,Norm.guardHolds,Holds,IntegerProjection.Above,IntegerProjection.Below]

theorem Norm.merge_holds (N M : Norm) (env : List Int) (y : Int) :
    (N.merge M).holds env y ↔ N.holds env y ∧ M.holds env y := by
  simp only [Norm.merge,Norm.holds,Norm.bounds,Norm.guardHolds,
    holds_append,List.map_append,IntegerProjection.Above,IntegerProjection.Below]
  constructor
  · rintro ⟨⟨hf,hf'⟩,⟨hl,hu⟩,hg⟩
    refine ⟨⟨hf,⟨?_,?_⟩,?_⟩,⟨hf',⟨?_,?_⟩,?_⟩⟩
    · exact fun a ha=>hl a (List.mem_append.mpr (Or.inl ha))
    · exact fun a ha=>hu a (List.mem_append.mpr (Or.inl ha))
    · exact fun a ha=>hg a (List.mem_append.mpr (Or.inl ha))
    · exact fun a ha=>hl a (List.mem_append.mpr (Or.inr ha))
    · exact fun a ha=>hu a (List.mem_append.mpr (Or.inr ha))
    · exact fun a ha=>hg a (List.mem_append.mpr (Or.inr ha))
  · rintro ⟨⟨hf,⟨hl,hu⟩,hg⟩,⟨hf',⟨hl',hu'⟩,hg'⟩⟩
    refine ⟨⟨hf,hf'⟩,⟨?_,?_⟩,?_⟩
    · intro a ha
      exact (List.mem_append.mp ha).elim (hl a) (hl' a)
    · intro a ha
      exact (List.mem_append.mp ha).elim (hu a) (hu' a)
    · intro a ha
      exact (List.mem_append.mp ha).elim (hg a) (hg' a)

def normalizeAtom (D : Nat) : Atom→Norm
  | .le a =>
    let c := a.split.1
    let r := a.split.2
    if c=0 then ⟨[],[],[.le r],[]⟩
    else
      let s : Int := Int.ofNat (D/c.natAbs)
      if 0<c then ⟨[],[.scale (-s) r],[],[]⟩
      else ⟨[.scale s r],[],[],[]⟩
  | .dvd m a =>
    ⟨[],[],[],[⟨D*m,a.split.1,.scale (Int.ofNat D) a.split.2⟩]⟩

private theorem scale_positive (D : Nat) (c : Int)
    (hD : 0<D) (hc : c≠0) (hd : c.natAbs∣D) :
    0<(Int.ofNat (D/c.natAbs)) ∧
      Int.ofNat (D/c.natAbs) * (Int.ofNat c.natAbs)=Int.ofNat D := by
  have he : (D/c.natAbs)*c.natAbs=D := Nat.div_mul_cancel hd
  have hs : 0<D/c.natAbs := by
    by_cases h : D/c.natAbs=0
    · rw [h,Nat.zero_mul] at he
      omega
    · omega
  refine ⟨by omega,?_⟩
  exact (by simpa only [Int.ofNat_mul] using congrArg Int.ofNat he)

private theorem scale_le_zero (s v : Int) (hs : 0<s) :
    s*v≤0 ↔ v≤0 := by
  constructor
  · intro h
    apply Int.le_of_mul_le_mul_left (a:=s) _ hs
    simpa using h
  · intro h
    have he := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hs)
    simpa using he

theorem normalizeAtom_correct (D : Nat) (A : Atom) (env : List Int) (x : Int)
    (hD : 0<D) (hc : match A with
      | .le a => a.split.1≠0→a.split.1.natAbs∣D
      | .dvd _ _ => True) :
    (normalizeAtom D A).holds env ((D:Int)*x) ↔ A.holds (x::env) := by
  cases A with
  | le a =>
    let c := a.split.1
    let r := a.split.2
    have hspl : a.eval (x::env)=c*x+r.eval env := a.split_eval env x
    change _ ↔ a.eval (x::env)≤0
    rw [hspl]
    change (if c=0 then (⟨[],[],[Atom.le r],[]⟩ : Norm)
      else if 0<c then ⟨[],[Aff.scale (-Int.ofNat (D/c.natAbs)) r],[],[]⟩
      else ⟨[Aff.scale (Int.ofNat (D/c.natAbs)) r],[],[],[]⟩).holds env ((D:Int)*x) ↔ _
    by_cases he : c=0
    · rw [if_pos he,he]
      simp [Norm.holds,Norm.bounds,Norm.guardHolds,Holds,IntegerProjection.Above,
        IntegerProjection.Below,Atom.holds]
    · rw [if_neg he]
      let s := Int.ofNat (D/c.natAbs)
      have hscale := scale_positive D c hD he (hc he)
      have hs : 0<s := hscale.1
      have hm : s*(Int.ofNat c.natAbs)=(D:Int) := hscale.2
      have hmul : s*(c*x+r.eval env)=(s*c)*x+s*r.eval env := by
        rw [Int.mul_add,Int.mul_assoc]
      by_cases hp : 0<c
      · rw [if_pos hp]
        have habs : (Int.ofNat c.natAbs)=c := Int.natAbs_of_nonneg (by omega)
        rw [habs] at hm
        rw [hm] at hmul
        simp [Norm.holds,Norm.bounds,Norm.guardHolds,Holds,
          IntegerProjection.Above,IntegerProjection.Below,Aff.eval]
        change (D:Int)*x≤(-s)*r.eval env ↔ c*x+r.eval env≤0
        rw [← scale_le_zero s _ hs,hmul,Int.neg_mul]
        omega
      · rw [if_neg hp]
        have habs : (Int.ofNat c.natAbs) = -c := by
          have h := Int.natAbs_of_nonneg (a:= -c) (by omega)
          simpa only [Int.natAbs_neg] using h
        rw [habs,Int.mul_neg] at hm
        have hm' : s*c=-(D:Int) := by omega
        rw [hm'] at hmul
        simp [Norm.holds,Norm.bounds,Norm.guardHolds,Holds,
          IntegerProjection.Above,IntegerProjection.Below,Aff.eval]
        change s*r.eval env≤(D:Int)*x ↔ c*x+r.eval env≤0
        rw [← scale_le_zero s _ hs,hmul,Int.neg_mul]
        omega
  | dvd m a =>
    have hd : (D:Int)≠0 := by omega
    change _ ↔ (m:Int)∣a.eval (x::env)
    rw [a.split_eval env x]
    simp [normalizeAtom,Norm.holds,Norm.bounds,Norm.guardHolds,Holds,
      IntegerProjection.Above,IntegerProjection.Below,Guard.holds,Aff.eval,Int.ofNat_mul]
    change ((D:Int)*(m:Int))∣a.split.1*((D:Int)*x)+(D:Int)*a.split.2.eval env ↔ _
    have he : a.split.1*((D:Int)*x)+(D:Int)*a.split.2.eval env =
        (D:Int)*(a.split.1*x+a.split.2.eval env) := by
      rw [Int.mul_add]
      simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
    rw [he,Int.mul_dvd_mul_iff_left hd]

def normalizeRows (D : Nat) : Conj→Norm
  | [] => Norm.empty
  | a::as => (normalizeAtom D a).merge (normalizeRows D as)

theorem normalizeRows_correct (D : Nat) (C : Conj) (env : List Int) (x : Int)
    (hD : 0<D) (hc : ∀ a,Atom.le a∈C→a.split.1≠0→a.split.1.natAbs∣D) :
    (normalizeRows D C).holds env ((D:Int)*x) ↔ Holds C (x::env) := by
  induction C with
  | nil =>
    constructor
    · intro _ a ha
      simp at ha
    · intro _
      exact Norm.empty_holds _ _
  | cons a as ih =>
    change ((normalizeAtom D a).merge (normalizeRows D as)).holds env ((D:Int)*x) ↔ _
    rw [Norm.merge_holds,normalizeAtom_correct D a env x hD,
      ih (fun t ht=>hc t (by simp [ht]))]
    · constructor
      · rintro ⟨ha,hs⟩ b hb
        rcases List.mem_cons.mp hb with h|h
        · subst b
          exact ha
        · exact hs b h
      · intro h
        exact ⟨h a (by simp),fun b hb=>h b (by simp [hb])⟩
    · cases a with
      | le a => exact hc a (by simp)
      | dvd m a => trivial

def integrality (D : Nat) : Norm :=
  ⟨[],[],[],[⟨D,1,.lit 0⟩]⟩

theorem integrality_holds (D : Nat) (env : List Int) (y : Int) :
    (integrality D).holds env y ↔ (D:Int)∣y := by
  simp [integrality,Norm.holds,Norm.bounds,Norm.guardHolds,Holds,
    IntegerProjection.Above,IntegerProjection.Below,Guard.holds,Aff.eval]

def normalize (C : Conj) : Norm :=
  let D := multiplier C
  (normalizeRows D C).merge (integrality D)

theorem normalize_correct (C : Conj) (env : List Int) :
    (∃ x,Holds C (x::env)) ↔ ∃ y,(normalize C).holds env y := by
  let D := multiplier C
  have hD := multiplier_pos C
  have hn := fun x=>normalizeRows_correct D C env x hD (fun a ha hne=>abs_dvd C a ha hne)
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨(D:Int)*x,?_⟩
    change ((normalizeRows D C).merge (integrality D)).holds env ((D:Int)*x)
    rw [Norm.merge_holds,integrality_holds]
    exact ⟨(hn x).mpr hx,⟨x,rfl⟩⟩
  · rintro ⟨y,hy⟩
    change ((normalizeRows D C).merge (integrality D)).holds env y at hy
    rw [Norm.merge_holds,integrality_holds] at hy
    obtain ⟨h,⟨x,rfl⟩⟩ := hy
    exact ⟨x,(hn x).mp h⟩

theorem normalizeAtom_moduli (D : Nat) (A : Atom)
    (hD : 0<D) (ha : A.good) :
    ∀ g,g∈(normalizeAtom D A).guards→0<g.modulus := by
  intro g hg
  cases A with
  | le a =>
    unfold normalizeAtom at hg
    dsimp only at hg
    split at hg
    · simp at hg
    · split at hg <;> simp at hg
  | dvd m a =>
    change g∈[⟨D*m,a.split.1,.scale (Int.ofNat D) a.split.2⟩] at hg
    simp only [List.mem_cons,List.mem_nil,false_or] at hg
    subst g
    exact Nat.mul_pos hD ha

theorem normalizeRows_moduli (D : Nat) (C : Conj) (hD : 0<D)
    (hC : Good C) :
    ∀ g,g∈(normalizeRows D C).guards→0<g.modulus := by
  induction C with
  | nil => intro g hg; simp [normalizeRows,Norm.empty] at hg
  | cons a as ih =>
    intro g hg
    change g∈(normalizeAtom D a).guards++(normalizeRows D as).guards at hg
    rcases List.mem_append.mp hg with h|h
    · exact normalizeAtom_moduli D a hD (hC a (by simp)) g h
    · exact ih (fun b hb=>hC b (by simp [hb])) g h

theorem normalize_moduli (C : Conj) (hC : Good C) :
    ∀ g,g∈(normalize C).guards→0<g.modulus := by
  intro g hg
  let D := multiplier C
  have hD := multiplier_pos C
  change g∈(normalizeRows D C).guards++(integrality D).guards at hg
  rcases List.mem_append.mp hg with h|h
  · exact normalizeRows_moduli D C hD hC g h
  · change g∈[⟨D,1,.lit 0⟩] at h
    simp only [List.mem_cons,List.mem_nil,false_or] at h
    subst g
    exact hD

def commonPeriod : List Guard→Nat
  | [] => 1
  | g::gs => g.modulus*commonPeriod gs

theorem commonPeriod_pos (gs : List Guard) (h : ∀ g,g∈gs→0<g.modulus) :
    0<commonPeriod gs := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    exact Nat.mul_pos (h g (by simp)) (ih (fun a ha=>h a (by simp [ha])))

theorem commonPeriod_dvd (gs : List Guard) (g : Guard) (hg : g∈gs) :
    g.modulus∣commonPeriod gs := by
  induction gs with
  | nil => simp at hg
  | cons a as ih =>
    rcases List.mem_cons.mp hg with h|h
    · subst a
      exact ⟨commonPeriod as,rfl⟩
    · obtain ⟨k,hk⟩ := ih h
      refine ⟨a.modulus*k,?_⟩
      change a.modulus*commonPeriod as=g.modulus*(a.modulus*k)
      rw [hk]
      simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]

def eliminateConj (C : Conj) : Formula :=
  let N := normalize C
  N.eliminate (commonPeriod N.guards)

theorem eliminateConj_correct (C : Conj) (env : List Int) (hC : Good C) :
    Satisfies (eliminateConj C) env ↔ ∃ x,Holds C (x::env) := by
  rw [normalize_correct]
  exact (Norm.eliminate_correct (normalize C) _ env
    (commonPeriod_pos _ (normalize_moduli C hC))
    (commonPeriod_dvd _)).symm

end REWB.AffineProjection
