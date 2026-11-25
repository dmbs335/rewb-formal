import REWB.ResidualDispatchSchedule

/-! Geometry of the actual dispatch list. Every emitted item is a
separated equality window; every nonshort indexed residual witness is
contained in an emitted item with its exact outer displacement. -/
namespace REWB.ResidualDispatch
open REWB.RunGeometry REWB.IndexedGrid REWB.GlobalCoverage REWB.Periodic
variable {σ : Nat}

theorem prepare_sound (f : Nat→Fin σ) (n s L D Q : Nat) (c : Strip)
    (hm : c∈(prepare f n s L D Q).windows) :
    ResidualSeparated.Window (segment f 0 n) c.lo c.hi c.distance := by
  rcases (prepare_mem f n s L D Q c).mp hm with h|h|h
  · obtain ⟨W,hW,he⟩:=h
    subst c
    exact (ResidualStripSchedule.prepare_sound f n s L D W hW).2.2
  · obtain ⟨R,p,hR,hc⟩:=h
    exact ResidualRunWindows.low_window f n s D R p hR c hc
  · obtain ⟨R,p,d,hR,hc⟩:=h
    exact ResidualRunWindows.large_window f n s Q R p d hR c hc

theorem residual_window (f : Nat→Fin σ) (n s L D Q p e k : Nat)
    (hD : 0<D) (hc : Copy f n p e k) (hL : L≤e-p)
    (hr : IndexedGlobalCoverage.Residual f n s L D Q p e k) :
    ∃c,c∈(prepare f n s L D Q).windows ∧ c.lo≤p ∧ e≤c.hi ∧ c.distance=k-p := by
  have hp:=hc.positive
  have hk:=hc.separated
  cases hr with
  | short h => omega
  | separated lo hi hmem hl hr hd =>
    let R : Strip:=⟨lo,hi,k-p⟩
    have hm:R∈(ResidualStripSchedule.generate f n s L).strips :=
      (ResidualStripSchedule.generate_mem f n s L R).mpr
        ⟨hmem,by simp only [ResidualStripSchedule.span,R]; omega⟩
    have hW : ResidualStripSchedule.direct R∈(ResidualStripSchedule.prepare f n s L D).batch.jobs := by
      apply (ResidualStripSchedule.collect_mem D L _ _).mpr
      refine ⟨R,hm,?_⟩
      rw [ResidualStripSchedule.local_direct D L R hd]
      exact List.mem_singleton_self _
    refine ⟨R,(prepare_mem f n s L D Q R).mpr (Or.inl
      ⟨ResidualStripSchedule.direct R,hW,rfl⟩),hl,hr,rfl⟩
  | longGap lo hi a hmem hl hr hea hak _ _ _ =>
    let R : Strip:=⟨lo,hi,k-p⟩
    obtain ⟨W,hW,hwlo,hwhi,hwq⟩:=ResidualStripSchedule.prepare_existing_cut f n s L D R p e a
      hmem hD hp hl hr hL hea (by change a*D≤p+(k-p); omega)
    exact ⟨stripWindow W,(prepare_mem f n s L D Q _).mpr (Or.inl ⟨W,hW,rfl⟩),hwlo,hwhi,hwq⟩
  | low R hm hl hr hd _ =>
    obtain ⟨c,hs,hlo,hhi,hq⟩:=ResidualRunWindows.candidate_complete R p e (k-p) hl
      (by omega) (by omega) hr
    rw [←hd] at hs
    exact ⟨c,(prepare_mem f n s L D Q c).mpr (Or.inr (Or.inl ⟨R,p,hm,hs⟩)),by omega,hhi,hq⟩
  | large R hm hl hr =>
    obtain ⟨c,hs,hlo,hhi,hq⟩:=ResidualRunWindows.candidate_complete R p e (k-p) hl
      (by omega) (by omega) hr
    exact ⟨c,(prepare_mem f n s L D Q c).mpr (Or.inr (Or.inr ⟨R,p,k-p,hm,hs⟩)),by omega,hhi,hq⟩

end REWB.ResidualDispatch
