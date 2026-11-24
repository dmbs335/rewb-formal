import REWB.DescriptorFormula

/-! Compile fixed-phase periodic intervals into affine DNF. No coefficient
    in a generated length or ordering atom is the run period: division
    by the period is used only to compute constant bounds and residues.
    All constraints share the same environment of integer block numbers. -/
namespace REWB.PhaseSolver
open REWB.Periodic
open REWB.AffineProjection
variable {α : Type}

def both (F G : Formula) : Formula :=
  F.flatMap (fun A=>G.map (fun B=>A++B))

theorem both_correct (F G : Formula) (env : List Int) :
    Satisfies (both F G) env ↔ Satisfies F env ∧ Satisfies G env := by
  constructor
  · rintro ⟨C,hC,h⟩
    obtain ⟨A,hA,hC⟩ := List.mem_flatMap.mp hC
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hC
    obtain ⟨ha,hb⟩ := (holds_append A B env).mp h
    exact ⟨⟨A,hA,ha⟩,⟨B,hB,hb⟩⟩
  · rintro ⟨⟨A,hA,ha⟩,⟨B,hB,hb⟩⟩
    exact ⟨A++B,List.mem_flatMap.mpr ⟨A,hA,List.mem_map.mpr ⟨B,hB,rfl⟩⟩,
      (holds_append A B env).mpr ⟨ha,hb⟩⟩

theorem both_good (F G : Formula) (hF : FormulaGood F) (hG : FormulaGood G) :
    FormulaGood (both F G) := by
  intro C hC
  obtain ⟨A,hA,hC⟩ := List.mem_flatMap.mp hC
  obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hC
  exact (Good_append A B).mpr ⟨hF A hA,hG B hB⟩

def unit (a : Atom) : Formula := [[a]]

theorem unit_correct (a : Atom) (env : List Int) :
    Satisfies (unit a) env ↔ a.holds env := by
  simp [unit,Satisfies,Holds]

theorem unit_good (a : Atom) (h : a.good) : FormulaGood (unit a) := by
  simp [unit,FormulaGood,Good,h]

def le (a b : Aff) : Formula := unit (.le (a.sub b))

theorem le_correct (a b : Aff) (env : List Int) :
    Satisfies (le a b) env ↔ a.eval env≤b.eval env := by
  rw [le,unit_correct]
  change (a.sub b).eval env≤0 ↔ _
  rw [Aff.eval_sub]
  omega

theorem le_good (a b : Aff) : FormulaGood (le a b) := unit_good _ trivial

def eq (a b : Aff) : Formula := both (le a b) (le b a)

theorem eq_correct (a b : Aff) (env : List Int) :
    Satisfies (eq a b) env ↔ a.eval env=b.eval env := by
  rw [eq,both_correct,le_correct,le_correct]
  omega

theorem eq_good (a b : Aff) : FormulaGood (eq a b) :=
  both_good _ _ (le_good _ _) (le_good _ _)

abbrev Endpoint := Aff × Nat

namespace Endpoint

def number (a : Endpoint) (env : List Int) : Int := a.1.eval env
def phase (a : Endpoint) : Nat := a.2

def coordinate (a : Endpoint) (env : List Int) : Coord :=
  ⟨(a.number env).toNat,a.phase⟩

def pos (a : Endpoint) (p : Nat) (env : List Int) : Nat :=
  (a.coordinate env).pos p

def valid (a : Endpoint) (p n : Nat) (env : List Int) : Prop :=
  0≤a.number env ∧ a.phase<p ∧ a.pos p env≤n

theorem cast_block (a : Endpoint) (env : List Int) (h : 0≤a.number env) :
    ((a.coordinate env).block:Int)=a.number env := by
  change ((a.number env).toNat:Int)=a.number env
  rw [Int.ofNat_toNat]
  omega

def bound (a : Endpoint) (p n : Nat) : Formula :=
  if a.phase<p ∧ a.phase≤n then
    both (le (.lit 0) a.1) (le a.1 (.lit (Int.ofNat ((n-a.phase)/p))))
  else []

theorem bound_correct (a : Endpoint) (p n : Nat) (env : List Int) (hp : 0<p) :
    Satisfies (a.bound p n) env ↔ a.valid p n env := by
  unfold bound
  by_cases h : a.phase<p ∧ a.phase≤n
  · rw [if_pos h,both_correct,le_correct,le_correct]
    change (0≤a.number env ∧ a.number env≤Int.ofNat ((n-a.phase)/p)) ↔ _
    constructor
    · rintro ⟨h0,hle⟩
      have hb := a.cast_block env h0
      rw [← hb] at hle
      have ht : (a.coordinate env).block≤(n-a.phase)/p := Int.ofNat_le.mp hle
      have hm := (Nat.le_div_iff_mul_le hp).mp ht
      refine ⟨h0,h.1,?_⟩
      change (a.coordinate env).block*p+a.phase≤n
      omega
    · rintro ⟨h0,hphase,hpos⟩
      have hb := a.cast_block env h0
      change (a.coordinate env).block*p+a.phase≤n at hpos
      have ht := (Nat.le_div_iff_mul_le hp).mpr (show (a.coordinate env).block*p≤n-a.phase by omega)
      exact ⟨h0,by rw [← hb]; exact Int.ofNat_le.mpr ht⟩
  · rw [if_neg h]
    constructor
    · rintro ⟨C,hC,_⟩
      simp at hC
    · rintro ⟨_,hphase,hpos⟩
      change (a.coordinate env).block*p+a.phase≤n at hpos
      exact False.elim (h ⟨hphase,by omega⟩)

theorem bound_good (a : Endpoint) (p n : Nat) : FormulaGood (a.bound p n) := by
  unfold bound
  split
  · exact both_good _ _ (le_good _ _) (le_good _ _)
  · intro C hC
    simp at hC

end Endpoint

def phaseCoord (a : Endpoint) : Coord := ⟨0,a.phase⟩

def carry (a b : Endpoint) : Nat := borrow (phaseCoord a) (phaseCoord b)
def tailLen (p : Nat) (a b : Endpoint) : Nat := residual p (phaseCoord a) (phaseCoord b)

def countExpr (a b : Endpoint) : Aff :=
  (b.1.sub a.1).sub (.lit (Int.ofNat (carry a b)))

theorem count_eval (a b : Endpoint) (env : List Int) :
    (countExpr a b).eval env=b.number env-a.number env-(carry a b:Int) := by
  simp only [countExpr,Aff.eval_sub,Aff.eval,Endpoint.number]
  rfl

theorem carry_eq (a b : Endpoint) (env : List Int) :
    borrow (a.coordinate env) (b.coordinate env)=carry a b := rfl

theorem tail_eq (p : Nat) (a b : Endpoint) (env : List Int) :
    residual p (a.coordinate env) (b.coordinate env)=tailLen p a b := rfl

theorem order_iff (a b : Endpoint) (p n : Nat) (env : List Int)
    (ha : a.valid p n env) (hb : b.valid p n env) :
    0≤(countExpr a b).eval env ↔ a.pos p env≤b.pos p env := by
  have hA := a.cast_block env ha.1
  have hB := b.cast_block env hb.1
  have hc := carry_eq a b env
  rw [count_eval]
  constructor
  · intro h
    have ho : (a.coordinate env).block+carry a b≤(b.coordinate env).block := by omega
    have hm := Nat.mul_le_mul_right p ho
    rw [Nat.add_mul] at hm
    change (a.coordinate env).block*p+a.phase≤(b.coordinate env).block*p+b.phase
    by_cases he : a.phase≤b.phase
    · unfold carry phaseCoord borrow at hm
      simp only [he,if_true,Nat.zero_mul,Nat.add_zero] at hm
      omega
    · unfold carry phaseCoord borrow at hm
      simp only [he,if_false,Nat.one_mul] at hm
      have hap := ha.2.1
      omega
  · intro ho
    have hh := borrow_order p (a.coordinate env) (b.coordinate env) hb.2.1 ho
    rw [hc] at hh
    omega

theorem count_natural (a b : Endpoint) (p n : Nat) (env : List Int)
    (ha : a.valid p n env) (hb : b.valid p n env) (ho : a.pos p env≤b.pos p env) :
    (countExpr a b).eval env=(copies (a.coordinate env) (b.coordinate env):Int) := by
  have hA := a.cast_block env ha.1
  have hB := b.cast_block env hb.1
  have hh := borrow_order p (a.coordinate env) (b.coordinate env) hb.2.1 ho
  rw [carry_eq] at hh
  rw [count_eval,← hA,← hB]
  unfold copies
  rw [carry_eq]
  omega

def orderFormula (p n : Nat) (a b : Endpoint) : Formula :=
  both (both (a.bound p n) (b.bound p n)) (le (.lit 0) (countExpr a b))

theorem orderFormula_correct (p n : Nat) (a b : Endpoint) (env : List Int) (hp : 0<p) :
    Satisfies (orderFormula p n a b) env ↔
      a.valid p n env ∧ b.valid p n env ∧ a.pos p env≤b.pos p env := by
  rw [orderFormula,both_correct,both_correct,Endpoint.bound_correct _ _ _ _ hp,
    Endpoint.bound_correct _ _ _ _ hp,le_correct]
  change (a.valid p n env ∧ b.valid p n env) ∧ 0≤(countExpr a b).eval env ↔ _
  constructor
  · rintro ⟨⟨ha,hb⟩,ho⟩
    exact ⟨ha,hb,(order_iff a b p n env ha hb).mp ho⟩
  · rintro ⟨ha,hb,ho⟩
    exact ⟨⟨ha,hb⟩,(order_iff a b p n env ha hb).mpr ho⟩

theorem orderFormula_good (p n : Nat) (a b : Endpoint) :
    FormulaGood (orderFormula p n a b) :=
  both_good _ _ (both_good _ _ (a.bound_good p n) (b.bound_good p n)) (le_good _ _)

def interval (a b : Endpoint) (env : List Int) : Interval :=
  ⟨a.coordinate env,b.coordinate env⟩

def regularFormula (p n : Nat) (f : Nat→α) (d : DFA α) (a b : Endpoint) : Formula :=
  both (orderFormula p n a b)
    (match factorDescriptor d f a.phase p (tailLen p a b) with
      | none => []
      | some D => descriptorFormula D (countExpr a b))

/-- No enumeration of the quotient length; descriptor depends only on
    the chosen phases and automaton. -/
theorem regularFormula_correct (p n : Nat) (f : Nat→α) (d : DFA α)
    (a b : Endpoint) (env : List Int) (hp : 0<p) (h : Period f n p) :
    Satisfies (regularFormula p n f d a b) env ↔
      a.valid p n env ∧ b.valid p n env ∧ a.pos p env≤b.pos p env ∧
        d.accepts ((interval a b env).value p f) := by
  obtain ⟨D,hD,hpD,_,hr,hcorrect⟩ := factorDescriptor_spec d f n a.phase p (tailLen p a b) h
  rw [regularFormula,both_correct,orderFormula_correct p n a b env hp,hD]
  constructor
  · rintro ⟨⟨ha,hb,ho⟩,hacc⟩
    have he := count_natural a b p n env ha hb ho
    have ht := (descriptorFormula_correct D (countExpr a b) env _ he hpD hr).mp hacc
    have hi : (interval a b env).Good p n := ⟨ha.2.1,hb.2.1,ho,hb.2.2⟩
    refine ⟨ha,hb,ho,(regularCode_iff _ p n f d hp h hi).mp ?_⟩
    exact ⟨D,hD,ht⟩
  · rintro ⟨ha,hb,ho,hacc⟩
    have hi : (interval a b env).Good p n := ⟨ha.2.1,hb.2.1,ho,hb.2.2⟩
    obtain ⟨E,hE,hacc⟩ := (regularCode_iff _ p n f d hp h hi).mpr hacc
    change factorDescriptor d f a.phase p (tailLen p a b)=some E at hE
    rw [hD] at hE
    simp only [Option.some.injEq] at hE
    subst E
    exact ⟨⟨ha,hb,ho⟩,(descriptorFormula_correct D _ env _
      (count_natural a b p n env ha hb ho) hpD hr).mpr hacc⟩

theorem regularFormula_good (p n : Nat) (f : Nat→α) (d : DFA α) (a b : Endpoint)
    (h : Period f n p) : FormulaGood (regularFormula p n f d a b) := by
  obtain ⟨D,hD,hp,_,_,_⟩ := factorDescriptor_spec d f n a.phase p (tailLen p a b) h
  rw [regularFormula,hD]
  exact both_good _ _ (orderFormula_good _ _ _ _) (descriptorFormula_good _ _ hp)

theorem length_unique (p a b r s : Nat) (hr : r<p) (hs : s<p) :
    a*p+r=b*p+s ↔ a=b ∧ r=s := by
  constructor
  · intro h
    have ha : a≤b := by
      by_cases ht : a≤b
      · exact ht
      · have hm := Nat.mul_le_mul_right p (show b+1≤a by omega)
        rw [Nat.add_mul,Nat.one_mul] at hm
        omega
    have hb : b≤a := by
      by_cases ht : b≤a
      · exact ht
      · have hm := Nat.mul_le_mul_right p (show a+1≤b by omega)
        rw [Nat.add_mul,Nat.one_mul] at hm
        omega
    have he : a=b := by omega
    exact ⟨he,by rw [he] at h; omega⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem phase_mod (a : Endpoint) (env : List Int) (p : Nat) (ha : a.phase<p) :
    (a.pos p env)%p=a.phase := by
  change ((a.coordinate env).block*p+a.phase)%p=a.phase
  rw [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,Nat.zero_add,
    Nat.mod_mod,Nat.mod_eq_of_lt ha]

theorem divisible_phase (a b : Endpoint) (env : List Int) (p : Nat)
    (ha : a.phase<p) (hb : b.phase<p) (ho : a.pos p env≤b.pos p env)
    (hd : p∣b.pos p env-a.pos p env) : a.phase=b.phase := by
  obtain ⟨k,hk⟩ := hd
  have he : b.pos p env=a.pos p env+p*k := by omega
  have hm := congrArg (fun x : Nat=>x%p) he
  change (b.pos p env)%p=(a.pos p env+p*k)%p at hm
  rw [phase_mod b env p hb,Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,
    Nat.add_zero,Nat.mod_mod,phase_mod a env p ha] at hm
  exact hm.symm

/-- Equal lengths force the quotient and remainder separately to agree.
    For unequal starting phases, an equal factor cannot contain a full
    period; only the single fixed residual is compared. -/
def equalityCore [DecidableEq α] (p : Nat) (f : Nat→α)
    (a b c d : Endpoint) : Formula :=
  if tailLen p a b=tailLen p c d then
    if a.phase=c.phase then eq (countExpr a b) (countExpr c d)
    else if segment f a.phase (tailLen p a b)=segment f c.phase (tailLen p c d) then
      both (eq (countExpr a b) (.lit 0)) (eq (countExpr c d) (.lit 0))
    else []
  else []

theorem equalityCore_good [DecidableEq α] (p : Nat) (f : Nat→α) (a b c d : Endpoint) :
    FormulaGood (equalityCore p f a b c d) := by
  unfold equalityCore
  split
  · split
    · exact eq_good _ _
    · split
      · exact both_good _ _ (eq_good _ _) (eq_good _ _)
      · intro C hC; simp at hC
  · intro C hC; simp at hC

theorem equalityCore_correct [DecidableEq α] (p n : Nat) (f : Nat→α)
    (h : LeastPeriod f n p) (a b c d : Endpoint) (env : List Int)
    (ha : a.valid p n env) (hb : b.valid p n env)
    (hc : c.valid p n env) (hd : d.valid p n env)
    (hab : a.pos p env≤b.pos p env) (hcd : c.pos p env≤d.pos p env)
    (hac : a.pos p env≤c.pos p env) :
    Satisfies (equalityCore p f a b c d) env ↔
      (interval a b env).value p f=(interval c d env).value p f := by
  let m := copies (a.coordinate env) (b.coordinate env)
  let k := copies (c.coordinate env) (d.coordinate env)
  let r := tailLen p a b
  let s := tailLen p c d
  have hA : (countExpr a b).eval env=(m:Int) := count_natural a b p n env ha hb hab
  have hC : (countExpr c d).eval env=(k:Int) := count_natural c d p n env hc hd hcd
  have hla := coordinate_length p (a.coordinate env) (b.coordinate env) h.1 ha.2.1 hb.2.1 hab
  have hlc := coordinate_length p (c.coordinate env) (d.coordinate env) h.1 hc.2.1 hd.2.1 hcd
  rw [tail_eq] at hla hlc
  have hr : r<p := hla.2.1
  have hs : s<p := hlc.2.1
  have hl : (interval a b env).len p=m*p+r := hla.2.2
  have hl' : (interval c d env).len p=k*p+s := hlc.2.2
  have hword : (interval a b env).value p f=segment f a.phase (m*p+r) :=
    coordinate_factor h.2.1 _ _ h.1 ha.2.1 hb.2.1 hab hb.2.2
  have hword' : (interval c d env).value p f=segment f c.phase (k*p+s) :=
    coordinate_factor h.2.1 _ _ h.1 hc.2.1 hd.2.1 hcd hd.2.2
  have lengths : (interval a b env).value p f=(interval c d env).value p f →
      m=k ∧ r=s := by
    intro he
    have hh := congrArg List.length he
    rw [hword,hword',segment_length,segment_length] at hh
    exact (length_unique p m k r s hr hs).mp hh
  have short : (interval a b env).value p f=(interval c d env).value p f →
      a.phase≠c.phase → m=0 := by
    intro he hdiff
    by_cases hm : m=0
    · exact hm
    · have hmul : p≤m*p := by
        have hh := Nat.mul_le_mul_right p (show 1≤m by omega)
        simpa only [Nat.one_mul] using hh
      have hlen := (lengths he)
      have hlen' : (interval a b env).len p=(interval c d env).len p := by
        rw [hl,hl',hlen.1,hlen.2]
      have hbound : c.pos p env+(interval c d env).len p≤n := by
        have h1 := hd.2.2
        change d.pos p env≤n at h1
        change c.pos p env+(d.pos p env-c.pos p env)≤n
        omega
      have hh : segment f (a.pos p env) ((interval c d env).len p) =
          segment f (c.pos p env) ((interval c d env).len p) := by
        change segment f (a.pos p env) ((interval a b env).len p) =
          segment f (c.pos p env) ((interval c d env).len p) at he
        rwa [hlen'] at he
      have hlong : p≤(interval c d env).len p := by rw [← hlen',hl]; omega
      have hdiv := equal_long_factor_same_phase h hac hbound hlong
        ((segment_eq_points _ _ _ _).mp hh)
      exact False.elim (hdiff (divisible_phase a c env p ha.2.1 hc.2.1 hac hdiv))
  unfold equalityCore
  change Satisfies (if r=s then if a.phase=c.phase then eq (countExpr a b) (countExpr c d)
      else if segment f a.phase r=segment f c.phase s then
        both (eq (countExpr a b) (.lit 0)) (eq (countExpr c d) (.lit 0)) else []
      else []) env ↔ _
  by_cases hrs : r=s
  · rw [if_pos hrs]
    by_cases hphase : a.phase=c.phase
    · rw [if_pos hphase,eq_correct,hA,hC]
      constructor
      · intro he
        have hm : m=k := by omega
        rw [hword,hword',hm,hrs,hphase]
      · intro he
        have hh := (lengths he).1
        omega
    · rw [if_neg hphase]
      by_cases ht : segment f a.phase r=segment f c.phase s
      · rw [if_pos ht,both_correct,eq_correct,eq_correct,hA,hC]
        constructor
        · rintro ⟨hm,hk⟩
          change (m:Int)=0 at hm
          change (k:Int)=0 at hk
          have hm' : m=0 := by omega
          have hk' : k=0 := by omega
          simp only [hword,hword',hm',hk',Nat.zero_mul,Nat.zero_add]
          exact ht
        · intro he
          have hm := short he hphase
          have hk := (lengths he).1
          change (m:Int)=0 ∧ (k:Int)=0
          exact ⟨by omega,by omega⟩
      · rw [if_neg ht]
        constructor
        · rintro ⟨C,hC,_⟩
          simp at hC
        · intro he
          have hm := short he hphase
          have hk : k=0 := by have hh := (lengths he).1; omega
          simp only [hword,hword',hm,hk,Nat.zero_mul,Nat.zero_add] at he
          exact False.elim (ht he)
  · rw [if_neg hrs]
    constructor
    · rintro ⟨C,hC,_⟩
      simp at hC
    · intro he
      exact False.elim (hrs (lengths he).2)

end REWB.PhaseSolver
