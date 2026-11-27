import REWB.ShortOuterBandCost

namespace REWB.ShortOuter.Band.Regression

def zero : Fin 2 := ⟨0,by decide⟩
def one : Fin 2 := ⟨1,by decide⟩
def any : DFA (Fin 2) := ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>true⟩
def eps : DFA (Fin 2) :=
  ⟨2,zero,fun _ _=>one,fun q=>decide (q=zero)⟩
def nonempty : DFA (Fin 2) :=
  ⟨2,zero,fun _ _=>one,fun q=>decide (q=one)⟩
def lastOne : DFA (Fin 2) := ⟨2,zero,fun _ c=>c,fun q=>decide (q=one)⟩

theorem empty_capture : get (build any any #[] zero 1) 0 0=true := by
  apply (get_correct any any #[] zero 1 0 0 (by decide) (by decide)).mpr
  exact ⟨0,by unfold DFA.accepts; decide⟩
theorem zero_limit : get (build any any #[zero,zero] zero 0) 0 0=false := by decide
theorem strict_limit : get (build any any #[zero,zero] zero 1) 0 1=false := by decide
theorem empty_gap : get (build any eps #[zero,zero] zero 2) 0 1=true := by
  apply (get_correct any eps #[zero,zero] zero 2 0 1 (by decide) (by decide)).mpr
  exact ⟨1,by unfold DFA.accepts; decide⟩
theorem distinct_copies : get (build any any #[zero,one] zero 2) 0 1=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨k,hk,hkn,he,_,_⟩:=(get_correct any any #[zero,one] zero 2 0 1 (by decide) (by decide)).mp h
  have hk1 : k=1 := by change k+1≤2 at hkn; omega
  subst k
  have hn : Spec.slice [zero,one] 0 1≠Spec.slice [zero,one] 1 2 := by decide
  exact hn he
theorem no_space : get (build any any #[zero] zero 2) 0 1=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨k,hk,hkn,_⟩:=(get_correct any any #[zero] zero 2 0 1 (by decide) (by decide)).mp h
  change k+1≤1 at hkn
  omega
theorem empty_outer_nonempty_gap : get (build nonempty eps #[one] zero 1) 0 0=true := by
  apply (get_correct nonempty eps #[one] zero 1 0 0 (by decide) (by decide)).mpr
  exact ⟨1,by unfold DFA.accepts; decide⟩
theorem empty_outer_gap_reject : get (build nonempty eps #[one] zero 1) 1 0=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨k,hk,hkn,_,hG,_⟩:=(get_correct nonempty eps #[one] zero 1 1 0 (by decide) (by decide)).mp h
  have hk1 : k=1 := by change k+0≤1 at hkn; omega
  subst k
  have hn : ¬nonempty.accepts [] := by unfold DFA.accepts; decide
  exact hn hG
theorem noninjective_gap : get (build lastOne eps #[zero,one,zero] zero 2) 0 1=true := by
  apply (get_correct lastOne eps #[zero,one,zero] zero 2 0 1 (by decide) (by decide)).mpr
  exact ⟨2,by unfold DFA.accepts; decide⟩
theorem query_eight : (query (build any any #[] zero 1) 0 0).2=8 := by decide
theorem key_capacity : (Keys.build #[zero,one] zero 100).ranks.size=9 := by decide

end REWB.ShortOuter.Band.Regression
