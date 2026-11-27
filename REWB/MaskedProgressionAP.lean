import REWB.MaskedProgressionQuery

/-! Exact clipped arithmetic-progression mask queries.

    The requested physical positions are j=s+k*q with lo<=k<=hi and
    k mod K=r. The prefix array has step K*q and covers [base,base+len).
    Lower-window clipping is done before residue alignment. Upper-window
    clipping is delegated to the two-read grid query. No residue classes
    or query positions are enumerated. Positive q,K are the correctness
    hypotheses; malformed zero parameters and residues are rejected.
-/
namespace REWB.MaskedProgression

def ceilDiv (a d : Nat) : Nat := (a+d-1)/d

theorem ceilDiv_le (a d k : Nat) (hd : 0<d) :
    ceilDiv a d≤k ↔ a≤k*d := by
  unfold ceilDiv
  rw [Nat.div_le_iff_le_mul hd]
  omega

theorem ceilDiv_cover (a d : Nat) (hd : 0<d) : a≤ceilDiv a d*d :=
  (ceilDiv_le a d (ceilDiv a d) hd).mp (Nat.le_refl _)

def aligned (lower K r : Nat) : Nat := r+ceilDiv (lower-r) K*K

theorem aligned_lower (lower K r : Nat) (hK : 0<K) : lower≤aligned lower K r := by
  have hh := ceilDiv_cover (lower-r) K hK
  unfold aligned
  omega

theorem aligned_mod (lower K r : Nat) (hr : r<K) : aligned lower K r%K=r := by
  unfold aligned
  rw [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hr]

theorem aligned_minimal (lower K r k : Nat) (hK : 0<K)
    (hl : lower≤k) (hk : k%K=r) : aligned lower K r≤k := by
  have he := Nat.mod_add_div k K
  rw [hk,Nat.mul_comm K (k/K)] at he
  have hc : ceilDiv (lower-r) K≤k/K := (ceilDiv_le _ _ _ hK).mpr (by omega)
  have hm := Nat.mul_le_mul_right K hc
  unfold aligned
  omega

/-- Alignment enumerates exactly the requested residue class, starting
    with its first element at or above lower. -/
theorem aligned_progression (lower K r k : Nat) (hK : 0<K) (hr : r<K) :
    (lower≤k ∧ k%K=r) ↔ ∃ t, k=aligned lower K r+t*K := by
  constructor
  · rintro ⟨hl,hk⟩
    have he := Nat.mod_add_div k K
    rw [hk,Nat.mul_comm K (k/K)] at he
    have hc : ceilDiv (lower-r) K≤k/K := (ceilDiv_le _ _ _ hK).mpr (by omega)
    refine ⟨k/K-ceilDiv (lower-r) K,?_⟩
    have hs : ceilDiv (lower-r) K+(k/K-ceilDiv (lower-r) K)=k/K :=
      Nat.add_sub_of_le hc
    calc
      k = r+(k/K)*K := he.symm
      _ = r+(ceilDiv (lower-r) K+(k/K-ceilDiv (lower-r) K))*K := by rw [hs]
      _ = aligned lower K r+(k/K-ceilDiv (lower-r) K)*K := by
        simp only [aligned,Nat.add_mul,Nat.add_assoc]
  · rintro ⟨t,rfl⟩
    refine ⟨Nat.le_trans (aligned_lower lower K r hK) (Nat.le_add_right _ _),?_⟩
    rw [Nat.add_mul_mod_self_right,aligned_mod lower K r hr]

def lowerIndex (base s q lo : Nat) : Nat := max lo (ceilDiv (base-s) q)

theorem lowerIndex_le (base s q lo k : Nat) (hq : 0<q) :
    lowerIndex base s q lo≤k ↔ lo≤k ∧ base≤s+k*q := by
  have hh := ceilDiv_le (base-s) q k hq
  unfold lowerIndex
  omega

def ap (counts : Array Nat) (base q K s lo hi r : Nat) : Answer :=
  if q=0 ∨ K=0 then ⟨false,0,2⟩
  else if K≤r then ⟨false,0,3⟩
  else
    let lower := lowerIndex base s q lo
    let first := aligned lower K r
    if hi<first then ⟨false,0,17⟩
    else
      let start := s+first*q-base
      let wanted := (hi-first)/K+1
      let result := grid counts (K*q) start wanted
      ⟨result.answer,result.slots,result.arithmetic+24⟩

theorem ap_slots (counts : Array Nat) (base q K s lo hi r : Nat) :
    (ap counts base q K s lo hi r).slots≤2 := by
  unfold ap
  split
  · decide
  · split
    · decide
    · dsimp only
      split
      · decide
      · exact grid_slots _ _ _ _

/-- The fixed charge covers clipping/alignment arithmetic and branches,
    in addition to the grid query's independently bounded arithmetic. -/
theorem ap_arithmetic (counts : Array Nat) (base q K s lo hi r : Nat) :
    (ap counts base q K s lo hi r).arithmetic≤37 := by
  unfold ap
  split
  · decide
  · split
    · decide
    · dsimp only
      split
      · decide
      · have hh := grid_arithmetic counts (K*q)
          (s+aligned (lowerIndex base s q lo) K r*q-base)
          ((hi-aligned (lowerIndex base s q lo) K r)/K+1)
        dsimp only
        omega

theorem ap_work (counts : Array Nat) (base q K s lo hi r : Nat) :
    (ap counts base q K s lo hi r).slots+
      (ap counts base q K s lo hi r).arithmetic≤39 := by
  have hs := ap_slots counts base q K s lo hi r
  have ha := ap_arithmetic counts base q K s lo hi r
  omega

theorem ap_build_correct (mask : Array Bool) (base len q K s lo hi r : Nat)
    (hq : 0<q) (hK : 0<K) :
    (ap (build mask base len (K*q)).counts base q K s lo hi r).answer=true ↔
      ∃ k, lo≤k ∧ k≤hi ∧ k%K=r ∧ base≤s+k*q ∧ s+k*q<base+len ∧
        readMask mask (s+k*q)=true := by
  have hbad : ¬(q=0 ∨ K=0) := by omega
  by_cases hrbad : K≤r
  · simp only [ap,hbad,if_false,hrbad,if_true,Bool.false_eq_true,false_iff]
    rintro ⟨k,_,_,hmod,_⟩
    have hh := Nat.mod_lt k hK
    omega
  · have hr : r<K := by omega
    let lower := lowerIndex base s q lo
    let first := aligned lower K r
    have hflo : lower≤first := aligned_lower lower K r hK
    have hfbase : base≤s+first*q := (lowerIndex_le base s q lo first hq).mp hflo |>.2
    by_cases hempty : hi<first
    · simp only [ap,hbad,if_false,hrbad]
      change (if hi<first then (⟨false,0,17⟩ : Answer) else _).answer=true ↔ _
      rw [if_pos hempty]
      simp only [Bool.false_eq_true,false_iff]
      rintro ⟨k,hlo,hhi,hmod,hbase,_⟩
      have hl : lower≤k := (lowerIndex_le base s q lo k hq).mpr ⟨hlo,hbase⟩
      have hf := aligned_minimal lower K r k hK hl hmod
      change first≤k at hf
      omega
    · let start := s+first*q-base
      let wanted := (hi-first)/K+1
      have hphys (t : Nat) : base+(start+t*(K*q))=s+(first+t*K)*q := by
        have hb : base+start=s+first*q := by dsimp [start]; omega
        calc
          base+(start+t*(K*q)) = (base+start)+t*(K*q) := (Nat.add_assoc _ _ _).symm
          _ = (s+first*q)+t*(K*q) := by rw [hb]
          _ = s+(first+t*K)*q := by rw [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]
      have hslots (t : Nat) : t<wanted ↔ first+t*K≤hi := by
        have hh := capacity_correct (hi+1) K first t hK (by omega)
        simp only [Nat.add_sub_cancel] at hh
        change t<wanted ↔ _ at hh
        omega
      simp only [ap,hbad,if_false,hrbad]
      change (if hi<first then (⟨false,0,17⟩ : Answer) else
        let out := grid (build mask base len (K*q)).counts (K*q) start wanted
        ⟨out.answer,out.slots,out.arithmetic+24⟩).answer=true ↔ _
      rw [if_neg hempty]
      change (grid (build mask base len (K*q)).counts (K*q) start wanted).answer=true ↔ _
      rw [grid_build_correct mask base len (K*q) (Nat.mul_pos hK hq)]
      constructor
      · rintro ⟨t,ht,hbound,hm⟩
        have hindex := (aligned_progression lower K r (first+t*K) hK hr).mpr ⟨t,rfl⟩
        obtain ⟨hlo,hbase⟩ := (lowerIndex_le base s q lo (first+t*K) hq).mp hindex.1
        refine ⟨first+t*K,hlo,(hslots t).mp ht,hindex.2,hbase,?_,?_⟩
        · have hp := hphys t
          omega
        · rwa [hphys t] at hm
      · rintro ⟨k,hlo,hhi,hmod,hbase,hbound,hm⟩
        have hl : lower≤k := (lowerIndex_le base s q lo k hq).mpr ⟨hlo,hbase⟩
        obtain ⟨t,he⟩ := (aligned_progression lower K r k hK hr).mp ⟨hl,hmod⟩
        subst k
        refine ⟨t,(hslots t).mpr hhi,?_,?_⟩
        · change s+(first+t*K)*q<base+len at hbound
          rw [←hphys t] at hbound
          exact Nat.lt_of_add_lt_add_left hbound
        · rwa [hphys t]

end REWB.MaskedProgression
