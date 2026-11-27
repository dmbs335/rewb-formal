import REWB.MaskedClusterCursorSemantics

/-! The complete dense cursor row is equivalent to real chronological
    text reading and zero/one physical jumps. The actual local anchor
    certificate derives periodicity and the penultimate endpoint bound;
    incoming safety is the predecessor anchor's following-cursor bound.
-/
namespace REWB.MaskedCluster
open REWB.Spec
variable {α : Type}

theorem rowCell_correct (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (classBase L : Nat) (copies : List Nat)
    (s q m H next incoming : Nat) (previous following : Option Nat)
    (enabled inMode outMode : Bool) (source target : Array Bool)
    (base len : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies (s+m*q) next previous following H)
    (hq : 0<q) (hm : 0<m) (hd : 2*q≤L) (hmem : ∀ k,k≤m→s+k*q∈copies)
    (hprev : previous=some (s+(m-1)*q)) (hsep : s+m*q<next) (hnext : next≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q)
    (hbase : base≤s) (hend : s+m*q+H≤base+len) :
    (rowCell C E prepared
      (prepareRow C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m H next incoming enabled inMode).1
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) s L H).maps
      source target (MaskedProgression.build source base len (prepared.K*q)).counts
      (MaskedProgression.build target base len (prepared.K*q)).counts base window outMode input output).answer=true ↔
        CursorStep C E w s q m L H next incoming enabled inMode outMode source target window input output := by
  by_cases ha : modeAllowed enabled inMode=true
  · have hper:=certificate_onPeriod _ _ classBase L copies s q m next previous following H cert hm hd hmem
    have hLH:=cert.current
    have hH : q≤H := by omega
    have hH0 : 0<H := by omega
    have hpen:=cert.previousSafe _ hprev
    have hlow:=cursor_before_lower s q incoming enabled inMode ha hin
    have hlast:=cursor_before_last s q m incoming enabled inMode hm ha hin
    have hcursor:=cursor_before_next s q m next incoming enabled inMode hm hsep ha hin
    have hu:=normalHi_le s q m H next
    have huend:=normalHi_end s q m H next hpen
    have huq:=Nat.mul_le_mul_right q hu
    have hanchor : s+H≤w.length := by have hh:=cert.lastBound; omega
    cases outMode with
    | false =>
      rw [rowCell_normal C E prepared _ _ s q m H next incoming enabled inMode ha]
      simp only [CursorStep,ha,true_and,Bool.false_eq_true,if_false]
      by_cases hcut : lower inMode≤normalHi s q m H next
      · rw [if_pos hcut,either_answer,
          passCell_correct C E w (cursor s incoming inMode) next input output hcursor hnext,
          filteredCell_direct_first C E prepared w fallback (cursor s incoming inMode) s (s+m*q+H)
            q L H (lower inMode) (normalHi s q m H next) next source target base len window input output
            hper hq hH hcut hlow (by omega) cert.lastBound huend hnext hLH]
        exact or_congr Iff.rfl (normal_window s q m L H next incoming base len enabled inMode
          (JumpAt C E w (cursor s incoming inMode) s q L next source target window input output)
          hq hH0 hLH hpen cert.overlap ha hin hbase hend)
      · rw [if_neg hcut,passCell_correct C E w (cursor s incoming inMode) next input output hcursor hnext]
        constructor
        · exact Or.inl
        · rintro (hp|⟨k,hk,hstart,hend,_⟩)
          · exact hp
          · have hh:=(normal_indices s q m L H next incoming k enabled inMode hq hLH hpen cert.overlap ha hin).mpr
              ⟨hk,hstart,hend⟩
            exact False.elim (hcut (Nat.le_trans hh.1 hh.2))
    | true =>
      rw [rowCell_over C E prepared _ _ s q m H next incoming enabled inMode ha]
      simp only [CursorStep,ha,true_and,if_true]
      by_cases ho : overMode s q m H next=true
      · rw [if_pos ho,filteredPointCell_direct C E w s (cursor s incoming inMode) (s+m*q) L H (s+m*q+H)
          source target window input output hlast hLH (Nat.le_refl _) cert.lastBound hanchor
          (MaskedPeriodic.Text.actual_equal_copies w fallback s (s+m*q+H) q H m hper cert.lastBound (Nat.le_refl _))]
        exact overshoot_single s q m L H next incoming enabled inMode
          (JumpAt C E w (cursor s incoming inMode) s q L (s+m*q+H) source target window input output)
          hm hLH hpen cert.overlap ha hin ho
      · rw [if_neg ho]
        simp only [Bool.false_eq_true,false_iff]
        rintro ⟨k,hk,_,hend,_⟩
        exact ho ((overshoot_current s q m L H next k hLH hpen cert.overlap).mp ⟨hk,hend⟩).1
  · rw [rowCell_inactive C E prepared _ _ s q m H next incoming enabled inMode ha]
    simp only [Bool.false_eq_true,CursorStep,ha,false_and]

theorem rowMatrix_correct (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (classBase L : Nat) (copies : List Nat)
    (s q m H next incoming : Nat) (previous following : Option Nat)
    (enabled inMode outMode : Bool) (source target : Array Bool)
    (base len : Nat) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies (s+m*q) next previous following H)
    (hq : 0<q) (hm : 0<m) (hd : 2*q≤L) (hmem : ∀ k,k≤m→s+k*q∈copies)
    (hprev : previous=some (s+(m-1)*q)) (hsep : s+m*q<next) (hnext : next≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q)
    (hbase : base≤s) (hend : s+m*q+H≤base+len) :
    ((((rowMatrix C E prepared
      (prepareRow C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m H next incoming enabled inMode).1
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) s L H).maps
      source target (MaskedProgression.build source base len (prepared.K*q)).counts
      (MaskedProgression.build target base len (prepared.K*q)).counts base window).get outMode).cells.get i).get j)=true ↔
        CursorStep C E w s q m L H next incoming enabled inMode outMode source target window
          (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  rw [rowMatrix_get]
  exact rowCell_correct C E prepared w fallback classBase L copies s q m H next incoming previous following
    enabled inMode outMode source target base len window _ _ cert hq hm hd hmem hprev hsep hnext hin hbase hend

end REWB.MaskedCluster
