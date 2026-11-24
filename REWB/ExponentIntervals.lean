import REWB.P1Join

/-! A one-variable affine DNF can be decomposed into bounded integer
    intervals, one for each conjunction and each residue of a common
    positive modulus. The endpoints are computed by signed floor/ceiling
    division, not by enumerating possible exponents.

    The modulus K is supplied by the caller and must be a multiple of
    each modulus in the formulas. A global fixed-pattern modulus bound
    still has to be established separately. -/
namespace REWB.ExponentIntervals
open REWB.AffineProjection
open REWB.IntegerProjection

structure Window where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

def Window.has (I : Window) (x : Int) : Prop := I.lo ≤ x ∧ x ≤ I.hi

def empty : Window := ⟨1,0⟩

theorem empty_has (x : Int) : ¬empty.has x := by
  change ¬((1:Int)≤x ∧ x≤0)
  omega

def Window.meet (I J : Window) : Window :=
  ⟨max I.lo J.lo,min I.hi J.hi⟩

theorem Window.meet_has (I J : Window) (x : Int) :
    (I.meet J).has x ↔ I.has x ∧ J.has x := by
  change max I.lo J.lo≤x ∧ x≤min I.hi J.hi ↔ _
  simp only [Int.max_le,Int.le_min,Window.has]
  constructor
  · rintro ⟨⟨a,b⟩,c,d⟩
    exact ⟨⟨a,c⟩,b,d⟩
  · rintro ⟨⟨a,c⟩,b,d⟩
    exact ⟨⟨a,b⟩,c,d⟩

/-- Intersect a window with c*x+d <= 0, using integer division with a
    positive divisor in both the lower- and upper-bound cases. -/
def clip (I : Window) (c d : Int) : Window :=
  if 0<c then ⟨I.lo,min I.hi ((-d)/c)⟩
  else if c<0 then ⟨max I.lo (-((-d)/(-c))),I.hi⟩
  else if d≤0 then I else empty

theorem clip_correct (I : Window) (c d x : Int) :
    (clip I c d).has x ↔ I.has x ∧ c*x+d≤0 := by
  unfold clip
  by_cases hc : 0<c
  · rw [if_pos hc]
    have hm : x≤(-d)/c ↔ c*x+d≤0 := by
      rw [Int.le_ediv_iff_mul_le hc,Int.mul_comm x c]
      omega
    change I.lo≤x ∧ x≤min I.hi ((-d)/c) ↔ _
    rw [Int.le_min,hm]
    simp only [Window.has, and_assoc]
  · rw [if_neg hc]
    by_cases hn : c<0
    · rw [if_pos hn]
      have hp : 0< -c := by omega
      have hm : -((-d)/(-c))≤x ↔ c*x+d≤0 := by
        have h : -((-d)/(-c))≤x ↔ -x≤(-d)/(-c) := by omega
        rw [h,Int.le_ediv_iff_mul_le hp,Int.neg_mul,Int.mul_neg,Int.neg_neg,Int.mul_comm x c]
        omega
      change max I.lo (-((-d)/(-c)))≤x ∧ x≤I.hi ↔ _
      rw [Int.max_le,hm]
      simp only [Window.has]
      constructor
      · rintro ⟨⟨a,b⟩,c⟩
        exact ⟨⟨a,c⟩,b⟩
      · rintro ⟨⟨a,c⟩,b⟩
        exact ⟨⟨a,b⟩,c⟩
    · rw [if_neg hn]
      have he : c=0 := by omega
      subst c
      by_cases hd : d≤0
      · simp [hd,Window.has]
      · simp [hd,empty_has]

def ResidueOK (K : Nat) : Atom→Prop
  | .le _ => True
  | .dvd m _ => m∣K

def Compatible (K : Nat) (F : Formula) : Prop :=
  ∀ C,C∈F→∀ a,a∈C→ResidueOK K a

/-- Restrict one inequality or divisibility atom to the progression
    m=r+K*z. Divisibility is a constant guard on this progression. -/
def applyAtom (K r : Nat) (I : Window) : Atom→Window
  | .le a => clip I (a.split.1*(K:Int)) (a.eval [(r:Int)])
  | .dvd m a =>
    if a.eval [(r:Int)]%(m:Int)=0 then I else empty

theorem affine_residue (a : Aff) (K r : Nat) (z : Int) :
    a.eval [(r:Int)+(K:Int)*z]=(a.split.1*(K:Int))*z+a.eval [(r:Int)] := by
  have h := a.split_eval [] ((r:Int)+(K:Int)*z)
  have h' := a.split_eval [] (r:Int)
  change a.eval [(r:Int)+(K:Int)*z]=_ at h
  change a.eval [(r:Int)]=_ at h'
  rw [h,h',Int.mul_add,Int.mul_assoc]
  omega

theorem applyAtom_correct (K r : Nat) (I : Window) (a : Atom) (z : Int)
    (h : ResidueOK K a) :
    (applyAtom K r I a).has z ↔ I.has z ∧ a.holds [(r:Int)+(K:Int)*z] := by
  cases a with
  | le a =>
    change (clip I (a.split.1*(K:Int)) (a.eval [(r:Int)])).has z ↔ _
    rw [clip_correct]
    change (_ ∧ _) ↔ I.has z ∧ a.eval [(r:Int)+(K:Int)*z]≤0
    rw [affine_residue]
  | dvd m a =>
    have hd : (m:Int)∣(K:Int) := by
      obtain ⟨k,hk⟩ := h
      exact ⟨(k:Int),by rw [hk,Int.ofNat_mul]⟩
    have hp := dvd_guard (K:Int) (m:Int) a.split.1 (a.split.2.eval []) hd (r:Int) z
    have he : ((m:Int)∣a.eval [(r:Int)+(K:Int)*z]) ↔ (m:Int)∣a.eval [(r:Int)] := by
      rw [a.split_eval [] ((r:Int)+(K:Int)*z),a.split_eval [] (r:Int)]
      exact hp
    change (if a.eval [(r:Int)]%(m:Int)=0 then I else empty).has z ↔
      I.has z ∧ ((m:Int)∣a.eval [(r:Int)+(K:Int)*z])
    rw [he,Int.dvd_iff_emod_eq_zero]
    by_cases hh : a.eval [(r:Int)]%(m:Int)=0
    · simp [hh]
    · simp [hh,empty_has]

def clipConj (K r : Nat) (I : Window) : Conj→Window
  | [] => I
  | a::as => clipConj K r (applyAtom K r I a) as

theorem clipConj_correct (K r : Nat) (I : Window) (C : Conj) (z : Int)
    (h : ∀ a,a∈C→ResidueOK K a) :
    (clipConj K r I C).has z ↔ I.has z ∧ Holds C [(r:Int)+(K:Int)*z] := by
  induction C generalizing I with
  | nil => simp [clipConj,Holds]
  | cons a as ih =>
    change (clipConj K r (applyAtom K r I a) as).has z ↔ _
    rw [ih _ (fun b hb=>h b (by simp [hb])),applyAtom_correct K r I a z (h a (by simp))]
    constructor
    · rintro ⟨⟨hi,ha⟩,hs⟩
      refine ⟨hi,?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with he|hm
      · subst b
        exact ha
      · exact hs b hm
    · rintro ⟨hi,hc⟩
      exact ⟨⟨hi,hc a (by simp)⟩,fun b hb=>hc b (by simp [hb])⟩

/-- Bounded exponent m in [0,N], represented by its quotient z.
    The case r>N correctly creates an empty interval. -/
def baseWindow (K r N : Nat) : Window :=
  ⟨0,((N:Int)-(r:Int))/(K:Int)⟩

theorem base_correct (K r N : Nat) (z : Int) (hK : 0<K) (hr : r<K) :
    (baseWindow K r N).has z ↔ 0≤(r:Int)+(K:Int)*z ∧ (r:Int)+(K:Int)*z≤(N:Int) := by
  have hp : 0<(K:Int) := by omega
  change (0≤z ∧ z≤((N:Int)-(r:Int))/(K:Int)) ↔ _
  rw [Int.le_ediv_iff_mul_le hp,Int.mul_comm z (K:Int)]
  constructor
  · rintro ⟨hz,hb⟩
    have hmul := Int.mul_nonneg (Int.le_of_lt hp) hz
    omega
  · rintro ⟨h0,hb⟩
    refine ⟨?_,by omega⟩
    by_cases hz : 0≤z
    · exact hz
    · have he := Int.mul_le_mul_of_nonneg_left (show z≤ -1 by omega) (Int.le_of_lt hp)
      rw [Int.mul_neg,Int.mul_one] at he
      omega

def windows (K r N : Nat) (F : Formula) : List Window :=
  F.map (clipConj K r (baseWindow K r N))

theorem windows_length (K r N : Nat) (F : Formula) :
    (windows K r N F).length=F.length := by simp [windows]

theorem windows_correct (K r N : Nat) (F : Formula) (z : Int)
    (hK : 0<K) (hr : r<K) (hF : Compatible K F) :
    (∃ I,I∈windows K r N F ∧ I.has z) ↔
      (0≤(r:Int)+(K:Int)*z ∧ (r:Int)+(K:Int)*z≤(N:Int)) ∧
        Satisfies F [(r:Int)+(K:Int)*z] := by
  constructor
  · rintro ⟨I,hI,hz⟩
    obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hI
    obtain ⟨hb,hc⟩ := (clipConj_correct K r _ C z (hF C hC)).mp hz
    exact ⟨(base_correct K r N z hK hr).mp hb,⟨C,hC,hc⟩⟩
  · rintro ⟨hb,⟨C,hC,hc⟩⟩
    exact ⟨_,List.mem_map.mpr ⟨C,hC,rfl⟩,
      (clipConj_correct K r _ C z (hF C hC)).mpr ⟨(base_correct K r N z hK hr).mpr hb,hc⟩⟩

/-- At most K times the number of DNF branches; no length-dependent
    splitting into singleton counts occurs. -/
def allWindows (K N : Nat) (F : Formula) : List (Nat×Window) :=
  (List.range K).flatMap (fun r=>(windows K r N F).map (fun I=>(r,I)))

theorem allWindows_length (K N : Nat) (F : Formula) :
    (allWindows K N F).length=K*F.length := by
  have aux : ∀ rs : List Nat,
      (rs.flatMap (fun r=>(windows K r N F).map (fun I=>(r,I)))).length=rs.length*F.length := by
    intro rs
    induction rs with
    | nil => simp
    | cons r rs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_map,windows_length,
        ih,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  unfold allWindows
  rw [aux,List.length_range]

end REWB.ExponentIntervals
