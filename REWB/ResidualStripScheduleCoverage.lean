import REWB.ResidualStripSchedule
import REWB.ResidualSeparatedWindow

/-! Every emitted job is an actual separated equality window. Long
copies in separated strips use their one direct window; copies with a
long gap in an overlapping strip are covered by one executed grid cut.
No candidate or maximal-strip oracle is supplied to prepare_complete. -/
namespace REWB.ResidualStripSchedule
open REWB.IndexedGrid REWB.GlobalCoverage REWB.Periodic
variable {α : Type} {σ : Nat}

theorem inside_window (f : Nat→α) (n : Nat) (R : Strip)
    (hv : MaximalStrip f n R.lo R.hi R.distance) (left right : Nat)
    (hl : R.lo≤left) (ho : left≤right) (hr : right≤R.hi) (hs : right≤left+R.distance) :
    ResidualSeparated.Window (segment f 0 n) left right R.distance := by
  obtain ⟨hd,hlr,hrn,he,_,_⟩:=hv
  refine ⟨ho,by simpa only [segment_length] using (show right+R.distance≤n by omega),hs,?_⟩
  rw [←GlobalSemanticCoverage.factor_slice f n left right ho (by omega),
    ←GlobalSemanticCoverage.factor_slice f n (left+R.distance) (right+R.distance) (by omega) (by omega)]
  simp only [P2Periodic.factor,Nat.add_sub_add_right]
  apply (segment_eq_points f left (left+R.distance) (right-left)).mpr
  intro i hi
  simpa only [Nat.add_assoc,Nat.add_comm R.distance i] using he (left+i) (by omega) (by omega)

theorem cut_sound (f : Nat→α) (n D L : Nat) (R : Strip)
    (hv : MaximalStrip f n R.lo R.hi R.distance) (a : Nat)
    (he : Eligible L (atCut D R a)) :
    ResidualSeparated.Window (segment f 0 n) (atCut D R a).left (atCut D R a).right R.distance := by
  have ho:=he.1
  simp only [atCut] at ho ⊢
  exact inside_window f n R hv _ _ (by omega) (by omega) (by omega) (by omega)

theorem one_sound (f : Nat→α) (n D L : Nat) (R : Strip)
    (hv : MaximalStrip f n R.lo R.hi R.distance) (hl : L≤span R) (W : Job)
    (hm : W∈(one D L R).jobs) :
    W.origin=R ∧ Eligible L W ∧
      ResidualSeparated.Window (segment f 0 n) W.left W.right W.distance := by
  by_cases hs : span R≤R.distance
  · rw [local_direct D L R hs] at hm
    have he:W=direct R := by simpa only [List.mem_singleton] using hm
    subst W
    exact ⟨rfl,⟨hv.2.1,hl⟩,ResidualSeparated.window_of_strip f n R.lo R.hi R.distance hv hs⟩
  · obtain ⟨a,_,_,he,hW⟩:=(local_cut D L R (by omega) W).mp hm
    subst W
    exact ⟨rfl,he,cut_sound f n D L R hv a he⟩

theorem collect_sound (f : Nat→α) (n D L : Nat) (Rs : List Strip)
    (hv : ∀R,R∈Rs→MaximalStrip f n R.lo R.hi R.distance)
    (hl : ∀R,R∈Rs→L≤span R) (W : Job) (hm : W∈(collect D L Rs).jobs) :
    W.origin∈Rs ∧ Eligible L W ∧
      ResidualSeparated.Window (segment f 0 n) W.left W.right W.distance := by
  obtain ⟨R,hR,hW⟩:=(collect_mem D L Rs W).mp hm
  obtain ⟨he,hE,hs⟩:=one_sound f n D L R (hv R hR) (hl R hR) W hW
  exact ⟨he.symm ▸ hR,hE,hs⟩

theorem prepare_sound (f : Nat→Fin σ) (n s L D : Nat) (W : Job)
    (hm : W∈(prepare f n s L D).batch.jobs) :
    W.origin∈(prepare f n s L D).strips.strips ∧ Eligible L W ∧
      ResidualSeparated.Window (segment f 0 n) W.left W.right W.distance :=
  collect_sound f n D L _ (fun R hR=>(generate_sound f n s L R hR).1)
    (fun R hR=>(generate_sound f n s L R hR).2) W hm

theorem one_complete (D L : Nat) (R : Strip) (p e : Nat) (hD : 0<D)
    (hp : p<e) (hl : R.lo≤p) (hr : e≤R.hi) (hL : L≤e-p)
    (hcase : span R≤R.distance ∨ e+D≤p+R.distance) :
    ∃W,W∈(one D L R).jobs ∧ W.left≤p ∧ e≤W.right ∧ W.distance=R.distance := by
  by_cases hs : span R≤R.distance
  · refine ⟨direct R,?_,hl,hr,rfl⟩
    rw [local_direct D L R hs]
    exact List.mem_singleton_self _
  · have hgap : e+D≤p+R.distance := hcase.resolve_left hs
    obtain ⟨a,hea,hap,hleft,hright,_⟩:=long_gap_cut D R.lo R.hi p e R.distance hD hl hp hr hgap
    have hgrid:=grid_contains D R a hD (by omega) (by omega)
    have hE : Eligible L (atCut D R a) := by simp only [Eligible,atCut]; omega
    refine ⟨atCut D R a,(local_cut D L R (by omega) _).mpr
      ⟨a,hgrid.1,hgrid.2,hE,rfl⟩,hleft,hright,rfl⟩

/-- An already chosen grid cut is enough; its surrounding gap need not
have length D. This is the interface for Residual.longGap records. -/
theorem one_existing_cut (D L : Nat) (R : Strip) (p e a : Nat) (hD : 0<D)
    (hp : p<e) (hl : R.lo≤p) (hr : e≤R.hi) (hL : L≤e-p)
    (hea : e≤a*D) (hap : a*D≤p+R.distance) :
    ∃W,W∈(one D L R).jobs ∧ W.left≤p ∧ e≤W.right ∧ W.distance=R.distance := by
  by_cases hs : span R≤R.distance
  · refine ⟨direct R,?_,hl,hr,rfl⟩
    rw [local_direct D L R hs]
    exact List.mem_singleton_self _
  · have hc:=cut_separates R.lo R.hi p e R.distance (a*D) hl hp hr hea hap
    have hgrid:=grid_contains D R a hD (by omega) (by omega)
    have hE : Eligible L (atCut D R a) := by simp only [Eligible,atCut]; omega
    exact ⟨atCut D R a,(local_cut D L R (by omega) _).mpr
      ⟨a,hgrid.1,hgrid.2,hE,rfl⟩,hc.1,hc.2.1,rfl⟩

theorem prepare_existing_cut (f : Nat→Fin σ) (n s L D : Nat) (R : Strip) (p e a : Nat)
    (hR : R∈(IndexedGrid.generate f n s).strips) (hD : 0<D)
    (hp : p<e) (hl : R.lo≤p) (hr : e≤R.hi) (hL : L≤e-p)
    (hea : e≤a*D) (hap : a*D≤p+R.distance) :
    ∃W,W∈(prepare f n s L D).batch.jobs ∧ W.left≤p ∧ e≤W.right ∧ W.distance=R.distance := by
  have hm:R∈(generate f n s L).strips :=
    (generate_mem f n s L R).mpr ⟨hR,by simp only [span]; omega⟩
  obtain ⟨W,hW,hp,he,hq⟩:=one_existing_cut D L R p e a hD hp hl hr hL hea hap
  exact ⟨W,(collect_mem D L _ W).mpr ⟨R,hm,hW⟩,hp,he,hq⟩

theorem prepare_complete (f : Nat→Fin σ) (n s L D p e k : Nat)
    (hs : 0<s) (hSL : s≤L) (hD : 0<D)
    (hc : Copy f n p e k) (hL : L≤e-p)
    (hcase : e+D≤k ∨ ∃lo hi,MaximalStrip f n lo hi (k-p) ∧
      lo≤p ∧ e≤hi ∧ hi-lo≤k-p) :
    ∃W,W∈(prepare f n s L D).batch.jobs ∧ W.left≤p ∧ e≤W.right ∧ W.distance=k-p := by
  obtain ⟨R,hR,hl,hr,hd⟩:=generate_complete f n s L p e k hs hSL hc hL
  have hv:=(generate_sound f n s L R hR).1
  have hsplit : span R≤R.distance ∨ e+D≤p+R.distance := by
    rcases hcase with hgap|⟨lo,hi,hS,hlo,hhi,hsep⟩
    · right
      have hk:=hc.separated
      omega
    · have hv':MaximalStrip f n R.lo R.hi (k-p) := hd ▸ hv
      obtain ⟨ha,hb⟩:=IndexedGlobalCoverage.strip_unique f n R.lo R.hi lo hi (k-p) p
        hv' hS hl (by have hh:=hc.positive; omega) hlo (by have hh:=hc.positive; omega)
      left
      simp only [span]
      omega
  obtain ⟨W,hW,hp,he,hq⟩:=one_complete D L R p e hD hc.positive hl hr hL hsplit
  exact ⟨W,(collect_mem D L _ W).mpr ⟨R,hR,hW⟩,hp,he,hq.trans hd⟩

/-- With sampling stride at most the long threshold, selection contains
every long maximal strip, including strips whose two copies overlap. -/
theorem generate_maximal (f : Nat→Fin σ) (n s L : Nat) (R : Strip)
    (hs : 0<s) (hSL : s≤L) (hv : MaximalStrip f n R.lo R.hi R.distance)
    (hL : L≤span R) : R∈(generate f n s L).strips := by
  obtain ⟨hd,hlr,hrn,he,hleft,hright⟩:=hv
  have hend : R.lo+span R=R.hi := by simp only [span]; omega
  have hreg : GridCoverage.EqualityRegion f n R.lo (span R) R.distance :=
    ⟨hd,by omega,by intro x ha hb; exact he x ha (by omega)⟩
  obtain ⟨i,hgrid,hlo,hhi,_⟩:=GridCoverage.equality_grid f n s R.lo (span R) R.distance hs
    (Nat.le_trans hSL hL) hreg
  have hreg' : GridCoverage.EqualityRegion f n R.lo (span R) (i+R.distance-i) := by
    simpa only [Nat.add_sub_cancel_left] using hreg
  obtain ⟨S,hcand,hSl,hSr,hSd⟩:=IndexedGrid.candidate_contains f n i (i+R.distance) R.lo (span R)
    hreg' hlo hhi (by omega)
  simp only [Nat.add_sub_cancel_left] at hSd
  have hSv:=IndexedGrid.candidate_sound f n (i,i+R.distance) S hcand
  rw [hSd] at hSv
  obtain ⟨hloeq,hhieq⟩:=IndexedGlobalCoverage.strip_unique f n S.lo S.hi R.lo R.hi R.distance R.lo
    hSv ⟨hd,hlr,hrn,he,hleft,hright⟩ hSl (by omega) (Nat.le_refl _) hlr
  have hSR : S=R := by cases S; cases R; simp_all only [Strip.mk.injEq]
  subst S
  apply (generate_mem f n s L R).mpr
  refine ⟨?_,hL⟩
  exact (IndexedGrid.collect_mem _ _ n _ R).mpr ⟨(i,i+R.distance),hgrid,hcand⟩

end REWB.ResidualStripSchedule
