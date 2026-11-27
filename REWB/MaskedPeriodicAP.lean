import REWB.MaskedPeriodicBounds
import REWB.MaskedProgressionAP

/-! Connect projected integer windows to the actual immutable-mask array.
    A window contains quotient z and represents target block k=r+K*z.
    Signed endpoints are clipped before conversion to natural AP bounds;
    a negative upper endpoint is rejected. No exponent or marked target
    is enumerated. The list traversal below visits only projected windows.
-/
namespace REWB.MaskedPeriodic
open REWB.AffineProjection REWB.ExponentIntervals

def windowQuery (counts : Array Nat) (base q K s r : Nat) (I : Window) :
    MaskedProgression.Answer :=
  if I.hi<0 then ⟨false,0,1⟩
  else
    let result := MaskedProgression.ap counts base q K s
      (r+I.lo.toNat*K) (r+I.hi.toNat*K) r
    ⟨result.answer,result.slots,result.arithmetic+7⟩

theorem windowQuery_slots (counts : Array Nat) (base q K s r : Nat) (I : Window) :
    (windowQuery counts base q K s r I).slots≤2 := by
  unfold windowQuery
  split
  · decide
  · exact MaskedProgression.ap_slots _ _ _ _ _ _ _ _

theorem windowQuery_arithmetic (counts : Array Nat) (base q K s r : Nat) (I : Window) :
    (windowQuery counts base q K s r I).arithmetic≤44 := by
  unfold windowQuery
  split
  · decide
  · have hh := MaskedProgression.ap_arithmetic counts base q K s
      (r+I.lo.toNat*K) (r+I.hi.toNat*K) r
    dsimp only
    omega

theorem residue_decomposition (K r k : Nat) (hr : k%K=r) : r+(k/K)*K=k := by
  have hh := Nat.mod_add_div k K
  rw [hr,Nat.mul_comm K (k/K)] at hh
  exact hh

theorem window_bounds (K r k : Nat) (I : Window) (hK : 0<K)
    (hr : k%K=r) (hi : 0≤I.hi) :
    (r+I.lo.toNat*K≤k ∧ k≤r+I.hi.toNat*K) ↔ I.has ((k/K:Nat):Int) := by
  have he := residue_decomposition K r k hr
  have hlo : I.lo.toNat≤k/K ↔ I.lo≤((k/K:Nat):Int) := Int.toNat_le
  have hhi : k/K≤I.hi.toNat ↔ ((k/K:Nat):Int)≤I.hi := by omega
  constructor
  · rintro ⟨hl,hu⟩
    have hL : I.lo.toNat*K≤(k/K)*K := by omega
    have hH : (k/K)*K≤I.hi.toNat*K := by omega
    exact ⟨hlo.mp (Nat.le_of_mul_le_mul_right hL hK),
      hhi.mp (Nat.le_of_mul_le_mul_right hH hK)⟩
  · rintro ⟨hl,hu⟩
    have hL := Nat.mul_le_mul_right K (hlo.mpr hl)
    have hH := Nat.mul_le_mul_right K (hhi.mpr hu)
    omega

theorem windowQuery_correct (mask : Array Bool) (base len q K s r : Nat) (I : Window)
    (hq : 0<q) (hK : 0<K) :
    (windowQuery (MaskedProgression.build mask base len (K*q)).counts base q K s r I).answer=true ↔
      ∃ k,k%K=r ∧ I.has ((k/K:Nat):Int) ∧ base≤s+k*q ∧ s+k*q<base+len ∧
        MaskedProgression.readMask mask (s+k*q)=true := by
  by_cases hi : I.hi<0
  · simp only [windowQuery,hi,if_true,Bool.false_eq_true,false_iff]
    rintro ⟨k,_,hwin,_⟩
    have hh := hwin.2
    have hn : 0≤((k/K:Nat):Int) := Int.ofNat_nonneg _
    omega
  · have hnonneg : 0≤I.hi := by omega
    simp only [windowQuery,hi,if_false]
    rw [MaskedProgression.ap_build_correct mask base len q K s _ _ r hq hK]
    constructor
    · rintro ⟨k,hlo,hhi,hr,hbase,hbound,hm⟩
      exact ⟨k,hr,(window_bounds K r k I hK hr hnonneg).mp ⟨hlo,hhi⟩,hbase,hbound,hm⟩
    · rintro ⟨k,hr,hwin,hbase,hbound,hm⟩
      obtain ⟨hlo,hhi⟩ := (window_bounds K r k I hK hr hnonneg).mpr hwin
      exact ⟨k,hlo,hhi,hr,hbase,hbound,hm⟩

def queryWindows (counts : Array Nat) (base q K s : Nat) :
    List (Nat×Window) → MaskedProgression.Answer
  | [] => ⟨false,0,1⟩
  | (r,I)::rest =>
    let head := windowQuery counts base q K s r I
    let tail := queryWindows counts base q K s rest
    ⟨head.answer || tail.answer,head.slots+tail.slots,head.arithmetic+tail.arithmetic+1⟩

theorem queryWindows_work (counts : Array Nat) (base q K s : Nat) (ws : List (Nat×Window)) :
    (queryWindows counts base q K s ws).slots+
      (queryWindows counts base q K s ws).arithmetic≤47*ws.length+1 := by
  induction ws with
  | nil => simp [queryWindows]
  | cons w ws ih =>
    obtain ⟨r,I⟩ := w
    have hs := windowQuery_slots counts base q K s r I
    have ha := windowQuery_arithmetic counts base q K s r I
    simp only [queryWindows,List.length_cons]
    omega

theorem queryWindows_correct (mask : Array Bool) (base len q K s : Nat)
    (ws : List (Nat×Window)) (hq : 0<q) (hK : 0<K) :
    (queryWindows (MaskedProgression.build mask base len (K*q)).counts base q K s ws).answer=true ↔
      ∃ k,(∃ r I,(r,I)∈ws ∧ k%K=r ∧ I.has ((k/K:Nat):Int)) ∧
        base≤s+k*q ∧ s+k*q<base+len ∧ MaskedProgression.readMask mask (s+k*q)=true := by
  induction ws with
  | nil => simp [queryWindows]
  | cons w ws ih =>
    obtain ⟨r,I⟩ := w
    simp only [queryWindows,Bool.or_eq_true,windowQuery_correct _ _ _ _ _ _ _ _ hq hK,ih]
    constructor
    · rintro (⟨k,hr,hw,hbase,hbound,hm⟩|⟨k,⟨r',I',hmem,hr,hw⟩,hbase,hbound,hm⟩)
      · exact ⟨k,⟨r,I,by simp,hr,hw⟩,hbase,hbound,hm⟩
      · exact ⟨k,⟨r',I',List.mem_cons.mpr (Or.inr hmem),hr,hw⟩,hbase,hbound,hm⟩
    · rintro ⟨k,⟨r',I',hmem,hr,hw⟩,hbase,hbound,hm⟩
      rcases List.mem_cons.mp hmem with he|hmem
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        exact Or.inl ⟨k,hr,hw,hbase,hbound,hm⟩
      · exact Or.inr ⟨k,⟨r',I',hmem,hr,hw⟩,hbase,hbound,hm⟩

theorem allWindows_mem (K N r : Nat) (F : Formula) (I : Window) :
    (r,I)∈allWindows K N F ↔ r<K ∧ I∈ExponentIntervals.windows K r N F := by
  simp only [allWindows,List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨r',hr,I',hI,rfl,rfl⟩
    exact ⟨hr,hI⟩
  · rintro ⟨hr,hI⟩
    exact ⟨r,hr,I,hI,rfl,rfl⟩

theorem allWindows_nat_correct (K N k : Nat) (F : Formula) (hK : 0<K)
    (hF : Compatible K F) :
    (∃ r I,(r,I)∈allWindows K N F ∧ k%K=r ∧ I.has ((k/K:Nat):Int)) ↔
      k≤N ∧ Satisfies F [(k:Int)] := by
  have he : ((k%K:Nat):Int)+(K:Int)*((k/K:Nat):Int)=(k:Int) := by
    have hh := congrArg (fun n : Nat=>(n:Int)) (Nat.mod_add_div k K)
    simpa only [Int.ofNat_add,Int.ofNat_mul] using hh
  have hw := ExponentIntervals.windows_correct K (k%K) N F ((k/K:Nat):Int) hK (Nat.mod_lt k hK) hF
  rw [he] at hw
  constructor
  · rintro ⟨r,I,hmem,hr,hI⟩
    subst r
    have hh := hw.mp ⟨I,(allWindows_mem K N (k%K) F I).mp hmem |>.2,hI⟩
    exact ⟨by omega,hh.2⟩
  · rintro ⟨hk,hF'⟩
    obtain ⟨I,hmem,hI⟩ := hw.mpr ⟨⟨by omega,by omega⟩,hF'⟩
    exact ⟨k%K,I,(allWindows_mem K N (k%K) F I).mpr ⟨Nat.mod_lt k hK,hmem⟩,rfl,hI⟩

/-- Execute a compiled branch against an already prepared immutable-mask
    prefix array. The common modulus depends only on b,c,e. -/
def queryBranch {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat)
    (counts : Array Nat) (base q s : Nat) (K : Nat := modulus b c e) : MaskedProgression.Answer :=
  queryWindows counts base q K s (allWindows K N (projection data branch N).1)

theorem queryBranch_cached {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat)
    (counts : Array Nat) (base q s : Nat) (prepared : PreparedPattern b c e) :
    queryBranch data branch N counts base q s prepared.K=queryBranch data branch N counts base q s := by
  rw [prepared.exact]

theorem queryBranch_correct {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat)
    (mask : Array Bool) (base len q s : Nat) (hq : 0<q) :
    (queryBranch data branch N
      (MaskedProgression.build mask base len (modulus b c e*q)).counts base q s).answer=true ↔
      ∃ a k,Accepts data branch N a k ∧ base≤s+k*q ∧ s+k*q<base+len ∧
        MaskedProgression.readMask mask (s+k*q)=true := by
  rw [queryBranch,queryWindows_correct _ _ _ _ _ _ _ hq (modulus_pos b c e)]
  simp only [windows,allWindows_nat_correct _ _ _ _ (modulus_pos b c e)
    (projection_compatible data branch N),projection_correct]
  constructor
  · rintro ⟨k,⟨hk,⟨a,ha⟩⟩,hbase,hbound,hm⟩
    exact ⟨a,k,ha,hbase,hbound,hm⟩
  · rintro ⟨a,k,ha,hbase,hbound,hm⟩
    exact ⟨k,⟨accepts_target_bound data branch N a k ha,⟨a,ha⟩⟩,hbase,hbound,hm⟩

/-- Query counter only: constructing descriptors, projected syntax and
    clipped windows is separate. The actual list length is proved to be
    pattern-only, so no q-dependent phase/cut pairs appear here. -/
theorem queryBranch_work {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat)
    (counts : Array Nat) (base q s : Nat) :
    (queryBranch data branch N counts base q s).slots+
      (queryBranch data branch N counts base q s).arithmetic≤
        47*(modulus b c e*syntaxBudget b c e)+1 := by
  have hh := queryWindows_work counts base q (modulus b c e) s (windows data branch N)
  have hl := Nat.mul_le_mul_left 47 (windows_size data branch N)
  exact Nat.le_trans hh (by omega)

end REWB.MaskedPeriodic
