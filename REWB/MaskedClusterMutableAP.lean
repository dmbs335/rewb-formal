import REWB.MaskedClusterMutableSnapshot

/-! Source-only projected windows executed against the actual mutable
    progression tree. The source index is a persistent snapshot. Target
    queries continue to use immutable stepped-prefix arrays elsewhere.
    The returned counter includes every mutable AP operation and window
    traversal; finite-orbit/formula/window construction is still separate.
-/
namespace REWB.MaskedCluster.Mutable
open REWB.MaskedPeriodic REWB.AffineProjection REWB.ExponentIntervals
variable {m n : Nat}

def windowQuery (idx : Index) (q K s r : Nat) (I : Window) : Answer :=
  if I.hi<0 then ⟨false,1⟩
  else
    let out:=MaskedMutableProgression.ap idx q K s (r+I.lo.toNat*K) (r+I.hi.toNat*K) r
    ⟨out.answer,out.work+7⟩

theorem windowQuery_work (idx : Index) (q K s r : Nat) (I : Window) :
    (windowQuery idx q K s r I).work≤7*idx.levels+72 := by
  unfold windowQuery
  split
  · dsimp only
    omega
  · have h:=MaskedMutableProgression.ap_work idx q K s (r+I.lo.toNat*K) (r+I.hi.toNat*K) r
    dsimp only
    omega

theorem windowQuery_correct (idx : Index) (hv : idx.Valid) (q K s r : Nat) (I : Window)
    (hq : 0<q) (hK : 0<K) (hstep : idx.step=K*q) :
    (windowQuery idx q K s r I).answer=true ↔
      ∃k,k%K=r ∧ I.has ((k/K:Nat):Int) ∧ idx.base≤s+k*q ∧ s+k*q<idx.base+idx.len ∧ idx.Live (s+k*q) := by
  by_cases hi : I.hi<0
  · simp only [windowQuery,hi,if_true,Bool.false_eq_true,false_iff]
    rintro ⟨k,_,hwin,_⟩
    have hh:=hwin.2
    have hn : 0≤((k/K:Nat):Int) := Int.ofNat_nonneg _
    omega
  · have hnonneg : 0≤I.hi := by omega
    simp only [windowQuery,hi,if_false]
    rw [MaskedMutableProgression.ap_correct idx hv q K s _ _ r hq hK hstep]
    constructor
    · rintro ⟨k,hlo,hhi,hr,hbase,hbound,hm⟩
      exact ⟨k,hr,(window_bounds K r k I hK hr hnonneg).mp ⟨hlo,hhi⟩,hbase,hbound,hm⟩
    · rintro ⟨k,hr,hwin,hbase,hbound,hm⟩
      obtain ⟨hlo,hhi⟩:=(window_bounds K r k I hK hr hnonneg).mpr hwin
      exact ⟨k,hlo,hhi,hr,hbase,hbound,hm⟩

def queryWindows (idx : Index) (q K s : Nat) : List (Nat×Window)→Answer
  | [] => ⟨false,1⟩
  | (r,I)::rest => either (windowQuery idx q K s r I) (queryWindows idx q K s rest)

theorem queryWindows_work (idx : Index) (q K s : Nat) (ws : List (Nat×Window)) :
    (queryWindows idx q K s ws).work≤(7*idx.levels+73)*ws.length+1 := by
  induction ws with
  | nil => simp only [queryWindows,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.le_refl]
  | cons entry ws ih =>
    rcases entry with ⟨r,I⟩
    have h:=windowQuery_work idx q K s r I
    simp only [queryWindows,either,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem queryWindows_correct (idx : Index) (hv : idx.Valid) (q K s : Nat)
    (ws : List (Nat×Window)) (hq : 0<q) (hK : 0<K) (hstep : idx.step=K*q) :
    (queryWindows idx q K s ws).answer=true ↔
      ∃k,(∃r I,(r,I)∈ws ∧ k%K=r ∧ I.has ((k/K:Nat):Int)) ∧
        idx.base≤s+k*q ∧ s+k*q<idx.base+idx.len ∧ idx.Live (s+k*q) := by
  induction ws with
  | nil => simp [queryWindows]
  | cons entry ws ih =>
    rcases entry with ⟨r,I⟩
    simp only [queryWindows,either,Bool.or_eq_true,windowQuery_correct idx hv q K s r I hq hK hstep,ih]
    constructor
    · rintro (⟨k,hr,hw,hbase,hbound,hm⟩|⟨k,⟨r',I',hmem,hr,hw⟩,hbase,hbound,hm⟩)
      · exact ⟨k,⟨r,I,by simp,hr,hw⟩,hbase,hbound,hm⟩
      · exact ⟨k,⟨r',I',List.mem_cons.mpr (Or.inr hmem),hr,hw⟩,hbase,hbound,hm⟩
    · rintro ⟨k,⟨r',I',hmem,hr,hw⟩,hbase,hbound,hm⟩
      rcases List.mem_cons.mp hmem with he|hmem
      · obtain ⟨rfl,rfl⟩:=Prod.mk.inj he
        exact Or.inl ⟨k,hr,hw,hbase,hbound,hm⟩
      · exact Or.inr ⟨k,⟨r',I',hmem,hr,hw⟩,hbase,hbound,hm⟩

def sourcePairQuery (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (idx : Index) (q s K : Nat) (window : SourceWindow) : Answer :=
  if window.enabled then
    queryWindows idx q K s (allWindows K hi (sourceFormula before after lo hi s q window))
  else ⟨false,1⟩

theorem sourcePairQuery_correct (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (idx : Index) (hv : idx.Valid) (q s S : Nat) (window : SourceWindow)
    (hq : 0<q) (hm : m≤S) (hn : n≤S) (hstep : idx.step=common S*q) :
    (sourcePairQuery before after lo hi idx q s (common S) window).answer=true ↔
      ∃k,PairAccepts before after lo hi k ∧ idx.base≤s+k*q ∧ s+k*q<idx.base+idx.len ∧
        idx.Live (s+k*q) ∧ window.allows (s+k*q)=true := by
  by_cases he : window.enabled=true
  · simp only [sourcePairQuery,he,if_true]
    rw [queryWindows_correct idx hv q (common S) s _ hq (common_pos S) hstep]
    simp only [allWindows_nat_correct _ _ _ _ (common_pos S)
      (sourceFormula_compatible before after lo hi s q S window hm hn),sourceFormula_correct,
      SourceWindow.allows_iff,he,true_and]
    constructor
    · rintro ⟨k,⟨_,hk,hl,hh⟩,hb,hn,hm⟩
      exact ⟨k,hk,hb,hn,hm,hl,hh⟩
    · rintro ⟨k,hk,hb,hn,hm,hl,hh⟩
      exact ⟨k,⟨hk.2.1,hk,hl,hh⟩,hb,hn,hm⟩
  · simp only [sourcePairQuery,he,if_false,Bool.false_eq_true,false_iff]
    rintro ⟨k,_,_,_,_,hw⟩
    exact he ((SourceWindow.allows_iff window _).mp hw).1

theorem sourcePairQuery_work (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (idx : Index) (q s K : Nat) (window : SourceWindow) :
    (sourcePairQuery before after lo hi idx q s K window).work≤(7*idx.levels+73)*(K*(m*n))+1 := by
  unfold sourcePairQuery
  split
  · have hw:=queryWindows_work idx q K s (allWindows K hi (sourceFormula before after lo hi s q window))
    have hl:=Nat.mul_le_mul_left (7*idx.levels+73)
      (Nat.mul_le_mul_left K (sourceFormula_length before after lo hi s q window))
    rw [allWindows_length] at hw
    exact Nat.le_trans hw (by omega)
  · dsimp only
    omega

/-- Equality with the immutable proof reference concerns answers only;
    the executable mutable query never builds the ghost array/counts. -/
theorem sourcePairQuery_snapshot (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (idx : Index) (hv : idx.Valid) (q s S : Nat) (window : SourceWindow)
    (hq : 0<q) (hm : m≤S) (hn : n≤S) (hstep : idx.step=common S*q) :
    (sourcePairQuery before after lo hi idx q s (common S) window).answer=
      (REWB.MaskedCluster.sourcePairQuery before after lo hi
        (MaskedProgression.build (snapshot idx) idx.base idx.len (common S*q)).counts
        idx.base q s (common S) window).answer := by
  apply Bool.eq_iff_iff.mpr
  rw [sourcePairQuery_correct before after lo hi idx hv q s S window hq hm hn hstep,
    REWB.MaskedCluster.sourcePairQuery_correct before after lo hi (snapshot idx) idx.base idx.len q s S
      window hq hm hn]
  simp only [MaskedPeriodic.Marked,snapshot_live idx hv]
  constructor
  · rintro ⟨k,hk,hb,hn,hl,hw⟩
    exact ⟨k,hk,⟨hb,hn,hl⟩,hw⟩
  · rintro ⟨k,hk,⟨hb,hn,hl⟩,hw⟩
    exact ⟨k,hk,hb,hn,hl,hw⟩

end REWB.MaskedCluster.Mutable
