import REWB.MaskedMutableProgressionQuery

/-! The existing `(q,K,s,lo,hi,r)` progression contract for a dynamic
source index. Requests mean `s+k*q`, `lo≤k≤hi`, `k%K=r`. The index step
must be `K*q`; malformed or incompatible requests are rejected. Alignment
and clipping are scalar, followed by one sparse-tree grid query. -/
namespace REWB.MaskedMutableProgression
open MaskedProgression

def ap (idx : Index) (q K s lo hi r : Nat) : Answer :=
  if q=0 ∨ K=0 ∨ idx.step≠K*q then ⟨none,5⟩
  else if K≤r then ⟨none,6⟩
  else
    let lower:=lowerIndex idx.base s q lo
    let first:=aligned lower K r
    if hi<first then ⟨none,20⟩
    else
      let start:=s+first*q-idx.base
      let wanted:=(hi-first)/K+1
      let result:=grid idx start wanted
      ⟨result.value,result.work+30⟩

theorem ap_work (idx : Index) (q K s lo hi r : Nat) :
    (ap idx q K s lo hi r).work≤7*idx.levels+65 := by
  unfold ap
  split
  · dsimp only; omega
  · split
    · dsimp only; omega
    · dsimp only
      split
      · dsimp only; omega
      · have hh:=grid_work idx (s+aligned (lowerIndex idx.base s q lo) K r*q-idx.base)
          ((hi-aligned (lowerIndex idx.base s q lo) K r)/K+1)
        dsimp only
        omega

theorem ap_correct (idx : Index) (hv : idx.Valid) (q K s lo hi r : Nat)
    (hq : 0<q) (hK : 0<K) (hstep : idx.step=K*q) :
    (ap idx q K s lo hi r).answer=true ↔
      ∃k,lo≤k ∧ k≤hi ∧ k%K=r ∧ idx.base≤s+k*q ∧ s+k*q<idx.base+idx.len ∧
        idx.Live (s+k*q) := by
  have hbad : ¬(q=0 ∨ K=0 ∨ idx.step≠K*q) := by omega
  have hs : 0<idx.step := by rw [hstep]; exact Nat.mul_pos hK hq
  by_cases hrbad : K≤r
  · simp only [ap,hbad,if_false,hrbad,if_true,Answer.answer,
      Option.isSome_none,Bool.false_eq_true,false_iff]
    rintro ⟨k,_,_,hmod,_⟩
    have hh:=Nat.mod_lt k hK
    omega
  · have hr : r<K := by omega
    let lower:=lowerIndex idx.base s q lo
    let first:=aligned lower K r
    have hflo : lower≤first:=aligned_lower lower K r hK
    have hfbase : idx.base≤s+first*q := (lowerIndex_le idx.base s q lo first hq).mp hflo |>.2
    by_cases hempty : hi<first
    · simp only [ap,hbad,if_false,hrbad]
      change (if hi<first then (⟨none,20⟩ : Answer) else _).answer=true ↔ _
      rw [if_pos hempty]
      simp only [Answer.answer,Option.isSome_none,Bool.false_eq_true,false_iff]
      rintro ⟨k,hlo,hhi,hmod,hbase,_⟩
      have hl : lower≤k:=(lowerIndex_le idx.base s q lo k hq).mpr ⟨hlo,hbase⟩
      have hf:=aligned_minimal lower K r k hK hl hmod
      change first≤k at hf
      omega
    · let start:=s+first*q-idx.base
      let wanted:=(hi-first)/K+1
      have hphys (t : Nat) : idx.base+(start+t*(K*q))=s+(first+t*K)*q := by
        have hb : idx.base+start=s+first*q := by dsimp [start]; omega
        calc
          idx.base+(start+t*(K*q)) = (idx.base+start)+t*(K*q) := (Nat.add_assoc _ _ _).symm
          _ = (s+first*q)+t*(K*q) := by rw [hb]
          _ = s+(first+t*K)*q := by rw [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]
      have hslots (t : Nat) : t<wanted ↔ first+t*K≤hi := by
        have hh:=capacity_correct (hi+1) K first t hK (by omega)
        simp only [Nat.add_sub_cancel] at hh
        change t<wanted ↔ _ at hh
        omega
      simp only [ap,hbad,if_false,hrbad]
      change (if hi<first then (⟨none,20⟩ : Answer) else
        let out:=grid idx start wanted
        ⟨out.value,out.work+30⟩).answer=true ↔ _
      rw [if_neg hempty]
      change (grid idx start wanted).answer=true ↔ _
      rw [grid_correct idx hv hs,hstep]
      constructor
      · rintro ⟨t,ht,hbound,hm⟩
        have hindex:=(aligned_progression lower K r (first+t*K) hK hr).mpr ⟨t,rfl⟩
        obtain ⟨hlo,hbase⟩:=(lowerIndex_le idx.base s q lo (first+t*K) hq).mp hindex.1
        refine ⟨first+t*K,hlo,(hslots t).mp ht,hindex.2,hbase,?_,?_⟩
        · have hp:=hphys t; omega
        · rwa [hphys t] at hm
      · rintro ⟨k,hlo,hhi,hmod,hbase,hbound,hm⟩
        have hl : lower≤k:=(lowerIndex_le idx.base s q lo k hq).mpr ⟨hlo,hbase⟩
        obtain ⟨t,he⟩:=(aligned_progression lower K r k hK hr).mp ⟨hl,hmod⟩
        subst k
        refine ⟨t,(hslots t).mpr hhi,?_,?_⟩
        · change s+(first+t*K)*q<idx.base+idx.len at hbound
          rw [←hphys t] at hbound
          exact Nat.lt_of_add_lt_add_left hbound
        · rwa [hphys t]

/-- Every returned physical source satisfies the requested AP and is live
in this exact version. Runtime guards suffice to infer all step conditions. -/
theorem ap_some (idx : Index) (hv : idx.Valid) (q K s lo hi r p : Nat)
    (hp : (ap idx q K s lo hi r).value=some p) :
    ∃k,lo≤k ∧ k≤hi ∧ k%K=r ∧ p=s+k*q ∧ idx.Live p := by
  unfold ap at hp
  split at hp
  next hbad => contradiction
  next hgood =>
    have hq : 0<q := by omega
    have hK : 0<K := by omega
    have hstep : idx.step=K*q := by omega
    have hs : 0<idx.step := by rw [hstep]; exact Nat.mul_pos hK hq
    split at hp
    next hrbad => contradiction
    next hr =>
      let lower:=lowerIndex idx.base s q lo
      let first:=aligned lower K r
      have hflo : lower≤first:=aligned_lower lower K r hK
      have hfbase : idx.base≤s+first*q := (lowerIndex_le idx.base s q lo first hq).mp hflo |>.2
      change (if hi<first then (⟨none,20⟩ : Answer) else
        let result:=grid idx (s+first*q-idx.base) ((hi-first)/K+1)
        ⟨result.value,result.work+30⟩).value=some p at hp
      split at hp
      next hempty => contradiction
      next hnonempty =>
        change (grid idx (s+first*q-idx.base) ((hi-first)/K+1)).value=some p at hp
        obtain ⟨t,ht,_,he,hlive⟩:=grid_some idx hv hs _ _ p hp
        rw [hstep] at he
        have hphys : idx.base+(s+first*q-idx.base+t*(K*q))=s+(first+t*K)*q := by
          rw [←Nat.add_assoc,Nat.add_sub_of_le hfbase]
          rw [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]
        have hindex:=(aligned_progression lower K r (first+t*K) hK (by omega)).mpr ⟨t,rfl⟩
        have hlo:=(lowerIndex_le idx.base s q lo (first+t*K) hq).mp hindex.1 |>.1
        have hslots:=capacity_correct (hi+1) K first t hK (by omega)
        simp only [Nat.add_sub_cancel] at hslots
        refine ⟨first+t*K,hlo,by have hh:=hslots.mp ht; omega,hindex.2,he.trans hphys,hlive⟩

theorem ap_represents (idx : Index) (hv : idx.Valid) (live : Nat→Prop) (hr : idx.Represents live)
    (q K s lo hi r : Nat) (hq : 0<q) (hK : 0<K) (hstep : idx.step=K*q) :
    (ap idx q K s lo hi r).answer=true ↔
      ∃k,lo≤k ∧ k≤hi ∧ k%K=r ∧ idx.base≤s+k*q ∧ s+k*q<idx.base+idx.len ∧ live (s+k*q) := by
  rw [ap_correct idx hv q K s lo hi r hq hK hstep]
  constructor
  · rintro ⟨k,hlo,hhi,hmod,hbase,hbound,hm⟩
    exact ⟨k,hlo,hhi,hmod,hbase,hbound,(hr _).mp hm |>.2.2⟩
  · rintro ⟨k,hlo,hhi,hmod,hbase,hbound,hm⟩
    exact ⟨k,hlo,hhi,hmod,hbase,hbound,(hr _).mpr ⟨hbase,hbound,hm⟩⟩

theorem ap_build_correct (mask : Array Bool) (base len q K s lo hi r : Nat)
    (hq : 0<q) (hK : 0<K) :
    (ap (build mask base len (K*q)).index q K s lo hi r).answer=true ↔
      ∃k,lo≤k ∧ k≤hi ∧ k%K=r ∧ base≤s+k*q ∧ s+k*q<base+len ∧
        MaskedProgression.readMask mask (s+k*q)=true :=
  ap_represents _ (build_valid mask base len (K*q)) _ (build_represents mask base len (K*q))
    q K s lo hi r hq hK rfl

end REWB.MaskedMutableProgression
