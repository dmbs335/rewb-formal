import REWB.MaskedClusterTransfer
import REWB.MaskedLocalAnchor

/-! Derive the dense cluster's periodic text premise from actual local
    anchor certificates. Equal anchored copies at q-spaced positions and
    density 2*q<=L<=H force one q-periodic interval. A singleton is kept
    on the separate point path, so no false periodicity is assumed.
-/
namespace REWB.MaskedCluster
open REWB.Periodic REWB.RunGeometry
variable {α : Type}

theorem copies_onPeriod (f : Nat→α) (s q H m : Nat) (hm : 0<m) (hd : 2*q≤H)
    (hc : ∀ k,k≤m→segment f s H=segment f (s+k*q) H) :
    OnPeriod f s (s+m*q+H) q := by
  have hcopy : segment f s H=segment f (s+q) H := by
    simpa only [Nat.one_mul] using hc 1 (by omega)
  have hper : Period (shift f s) H q := by
    intro i hi
    have he:=(segment_eq_points f s (s+q) H).mp hcopy i (by omega)
    change f (s+i)=f (s+(i+q))
    simpa only [Nat.add_assoc,Nat.add_comm q i] using he
  have aux : ∀ k,k≤m→OnPeriod f s (s+k*q+H) q := by
    intro k
    induction k with
    | zero =>
      intro _
      apply (on_iff _ _ _ _).mpr
      simpa only [Nat.zero_mul,Nat.add_zero,Nat.add_sub_cancel_left] using hper
    | succ k ih =>
      intro hk
      have old:=ih (by omega)
      have per:=MaskedLocalAnchor.period_copy f s (s+(k+1)*q) H q (hc (k+1) hk) hper
      have new : OnPeriod f (s+(k+1)*q) (s+(k+1)*q+H) q := by
        apply (on_iff _ _ _ _).mpr
        simpa only [Nat.add_sub_cancel_left] using per
      have hstep : (k+1)*q=k*q+q := by rw [Nat.add_mul,Nat.one_mul]
      have merged:=merge_periods f s (s+k*q+H) (s+(k+1)*q) (s+(k+1)*q+H) q
        (by omega) (by rw [hstep]; omega) old new
      have hmax : max (s+k*q+H) (s+(k+1)*q+H)=s+(k+1)*q+H := by
        apply Nat.max_eq_right
        rw [hstep]
        omega
      simpa only [hmax] using merged
  exact aux m (Nat.le_refl _)

theorem certificate_onPeriod (f : Nat→α) (n base L : Nat) (copies : List Nat)
    (s q m next : Nat) (previous following : Option Nat) (H : Nat)
    (cert : MaskedLocalAnchor.Certificate f n base L copies (s+m*q) next previous following H)
    (hm : 0<m) (hd : 2*q≤L) (hmem : ∀ k,k≤m→s+k*q∈copies) :
    OnPeriod f s (s+m*q+H) q := by
  apply copies_onPeriod f s q H m hm (Nat.le_trans hd cert.current)
  intro k hk
  have hfirst:=cert.words s (by simpa only [Nat.zero_mul,Nat.add_zero] using hmem 0 (Nat.zero_le _))
  exact hfirst.2.trans (cert.words (s+k*q) (hmem k hk)).2.symm

theorem cell_direct_certificate (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (base L : Nat) (copies : List Nat)
    (I s q m next : Nat) (previous following : Option Nat) (H lo hi O : Nat)
    (source target : Array Bool) (windowBase windowLen : Nat)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length base L copies
      (s+m*q) next previous following H)
    (hq : 0<q) (hm : 0<m) (hd : 2*q≤L) (hmem : ∀ k,k≤m→s+k*q∈copies)
    (hlo : lo≤hi) (hhi : hi≤m) (hI : I≤s+lo*q) (hO : s+hi*q+H≤O) (hOn : O≤w.length) :
    (cell C E prepared
      (contexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        I s H q lo hi O).maps
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s L H).maps lo hi
      (MaskedProgression.build source windowBase windowLen (prepared.K*q)).counts
      (MaskedProgression.build target windowBase windowLen (prepared.K*q)).counts
        windowBase q s input output).answer=true ↔
        ∃ k,lo≤k ∧ k≤hi ∧ windowBase≤s+k*q ∧ s+k*q<windowBase+windowLen ∧
          MaskedClusterStage.direct C E w I (s+k*q) L O
            (MaskedProgression.readMask source (s+k*q))
            (MaskedProgression.readMask target (s+k*q)) input=some output := by
  have hper:=certificate_onPeriod _ _ base L copies s q m next previous following H cert hm hd hmem
  have hmul:=Nat.mul_le_mul_right q hhi
  have hLH:=cert.current
  exact cell_direct_first C E prepared w fallback I s (s+m*q+H) q L H lo hi O source target
    windowBase windowLen input output hper hq (by omega) hlo hI (by omega) cert.lastBound hO hOn hLH

end REWB.MaskedCluster
