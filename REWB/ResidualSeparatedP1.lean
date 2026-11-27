import REWB.ResidualSeparatedWindow

/-! The separated outer-copy P1 case is one fixed finite family of
boundary queries. The earlier inner source keeps its absolute position
and can lie wholly before the equality strip. -/
namespace REWB.ResidualSeparated
open REWB.Spec (slice)
open REWB.BoundaryApplication
open REWB.BoundaryRange
variable {α : Type}

structure P1Witness (P : SevenDFA α) (w : Word α) (left right shift : Nat) where
  i : Nat
  a : Nat
  p : Nat
  j : Nat
  t : Nat
  e : Nat
  ia : i≤a
  ap : a≤p
  pj : p≤j
  jt : j≤t
  te : t≤e
  lp : left≤p
  er : e≤right
  inner : slice w i a=slice w j t
  prefix_ok : P.A.accepts (slice w 0 i)
  capture : P.B.accepts (slice w i a)
  before : P.C.accepts (slice w a p)
  middle : P.D.accepts (slice w p j)
  after : P.F.accepts (slice w t e)
  gap : P.G.accepts (slice w e (p+shift))
  tail : P.H.accepts (slice w (e+shift) w.length)

theorem p1_iff (P : SevenDFA α) (w : Word α) (left right shift : Nat)
    (h : Window w left right shift) :
    (∃q : Fin P.G.stateCount,Spec.boundaryRange P.A P.B P.C
      (gapStart P.G (Range.build P.G w) left right shift q) P.D
      (outerSuffix P.F P.G P.H (Range.build P.H w) right shift w.length q)
      w left right) ↔ Nonempty (P1Witness P w left right shift) := by
  constructor
  · rintro ⟨q,_,_,i,a,p,j,t,hia,hap,hpj,hjt,htr,hlp,he,hA,hB,hC,hK,hD,hE⟩
    obtain ⟨e,hte,her,hF,hq,hH⟩:=
      (outerSuffix_accepts P.F P.G P.H w left right shift t h (by omega) htr q).mp hE
    have hG : P.G.accepts (slice w e (p+shift)) := by
      change P.G.final (P.G.run P.G.initial (slice w e (p+shift)))=true
      rw [gap_run P.G w left right shift p e h hlp (by omega) her,hq]
      exact (Automata.start_accepts P.G _ _).mp hK
    exact ⟨⟨i,a,p,j,t,e,hia,hap,hpj,hjt,hte,hlp,her,he,hA,hB,hC,hD,hF,hG,hH⟩⟩
  · rintro ⟨v⟩
    let q:=P.G.run P.G.initial (slice w v.e right)
    refine ⟨q,h.ordered,by have hh:=h.within; omega,
      v.i,v.a,v.p,v.j,v.t,v.ia,v.ap,v.pj,v.jt,by have ht:=v.te; have he:=v.er; omega,
      v.lp,v.inner,v.prefix_ok,v.capture,v.before,?_,v.middle,?_⟩
    · apply (Automata.start_accepts P.G _ _).mpr
      have hh:=v.gap
      change P.G.final (P.G.run P.G.initial (slice w v.e (v.p+shift)))=true at hh
      rw [gap_run P.G w left right shift v.p v.e h v.lp (by have hp:=v.pj; have ht:=v.jt; have he:=v.te; omega) v.er] at hh
      exact hh
    · apply (outerSuffix_accepts P.F P.G P.H w left right shift v.t h
        (by have hl:=v.lp; have hp:=v.pj; have ht:=v.jt; omega)
        (by have ht:=v.te; have he:=v.er; omega) q).mpr
      exact ⟨v.e,v.te,v.er,v.after,rfl,v.tail⟩

theorem P1Witness.sound (P : SevenDFA α) (w : Word α) (left right shift : Nat)
    (h : Window w left right shift) (v : P1Witness P w left right shift) :
    MatchesWithin P.nested1 w 2 := by
  have hpj:=v.pj
  have hjt:=v.jt
  have hte:=v.te
  have hap:=v.ap
  have hia:=v.ia
  have her:=v.er
  have hlp:=v.lp
  have hr:=h.within
  have hs:=h.separated
  have houter : slice w v.p v.e=
      slice w v.p v.j++slice w v.i v.a++slice w v.t v.e := by
    rw [OuterColumn.slice_split w v.p v.j v.e hpj (by omega),
      OuterColumn.slice_split w v.j v.t v.e hjt hte,←v.inner]
    simp only [List.append_assoc]
  have heq:=h.copy w left right shift v.p v.e hlp (by omega) her
  apply (REWB.Witness.nested1_iff P w).mpr
  refine ⟨slice w 0 v.i,slice w v.i v.a,slice w v.a v.p,
    slice w v.p v.j,slice w v.t v.e,slice w v.e (v.p+shift),slice w (v.e+shift) w.length,
    v.prefix_ok,v.capture,v.before,v.middle,v.after,v.gap,v.tail,?_⟩
  have parts : w=slice w 0 v.i++slice w v.i v.a++slice w v.a v.p++slice w v.p v.e++
      slice w v.e (v.p+shift)++slice w (v.p+shift) (v.e+shift)++slice w (v.e+shift) w.length := by
    conv => lhs; rw [show w=slice w 0 w.length by simp [slice]]
    rw [OuterColumn.slice_split w 0 v.i w.length (by omega) (by omega),
      OuterColumn.slice_split w v.i v.a w.length hia (by omega),
      OuterColumn.slice_split w v.a v.p w.length hap (by omega),
      OuterColumn.slice_split w v.p v.e w.length (by omega) (by omega),
      OuterColumn.slice_split w v.e (v.p+shift) w.length (by omega) (by omega),
      OuterColumn.slice_split w (v.p+shift) (v.e+shift) w.length (by omega) (by omega)]
    simp only [List.append_assoc]
  rw [←heq] at parts
  simpa only [houter,List.append_assoc] using parts

def of_global (P : SevenDFA α) (f : Nat→α) (n left right shift : Nat)
    (v : GlobalCoverageP1.Witness P f n) (hl : left≤v.outerStart) (hr : v.target.e≤right)
    (hk : v.target.k=v.outerStart+shift) :
    P1Witness P (Periodic.segment f 0 n) left right shift := by
  obtain ⟨hpj,hjt,hte,hek,hkf,hfn,hD,hB,hF,hG,hH,houter⟩:=v.target_ok
  have hin:=v.earlier
  have hs : v.earlierStart+(v.target.t-v.target.j)≤n := by omega
  have hi : v.earlierStart≤n := by omega
  have hlen:=congrArg List.length houter
  simp only [P2Periodic.factor,Periodic.segment_length] at hlen
  have hf : v.target.f=v.target.e+shift := by omega
  have inner : slice (Periodic.segment f 0 n) v.earlierStart
      (v.earlierStart+(v.target.t-v.target.j))=
      slice (Periodic.segment f 0 n) v.target.j v.target.t := by
    rw [←GlobalSemanticCoverage.factor_slice f n _ _ (by omega) hs,
      ←GlobalSemanticCoverage.factor_slice f n _ _ hjt (by omega)]
    simpa only [P2Periodic.factor,Nat.add_sub_cancel_left] using v.equal_inner
  refine ⟨v.earlierStart,v.earlierStart+(v.target.t-v.target.j),v.outerStart,v.target.j,
    v.target.t,v.target.e,by omega,hin,hpj,hjt,hte,hl,hr,inner,?_,?_,v.gap_ok,?_,?_,?_,?_⟩
  · rw [←GlobalSemanticCoverage.factor_slice f n 0 v.earlierStart (Nat.zero_le _) hi]
    simpa only [P2Periodic.factor,Nat.sub_zero] using v.prefix_ok
  · rw [inner,←GlobalSemanticCoverage.factor_slice f n v.target.j v.target.t hjt (by omega)]
    exact hB
  · rwa [GlobalSemanticCoverage.factor_slice f n v.outerStart v.target.j hpj (by omega)] at hD
  · rwa [GlobalSemanticCoverage.factor_slice f n v.target.t v.target.e hte (by omega)] at hF
  · rw [GlobalSemanticCoverage.factor_slice f n v.target.e v.target.k hek (by omega),hk] at hG
    exact hG
  · simp only [List.append_nil] at hH
    rw [GlobalSemanticCoverage.factor_slice f n v.target.f n hfn (Nat.le_refl _),hf] at hH
    simpa only [Periodic.segment_length] using hH

theorem p1_complete (P : SevenDFA α) (f : Nat→α) (n left right shift : Nat)
    (h : Window (Periodic.segment f 0 n) left right shift)
    (v : GlobalCoverageP1.Witness P f n) (hl : left≤v.outerStart) (hr : v.target.e≤right)
    (hk : v.target.k=v.outerStart+shift) :
    ∃q : Fin P.G.stateCount,Spec.boundaryRange P.A P.B P.C
      (gapStart P.G (Range.build P.G (Periodic.segment f 0 n)) left right shift q) P.D
      (outerSuffix P.F P.G P.H (Range.build P.H (Periodic.segment f 0 n)) right shift n q)
      (Periodic.segment f 0 n) left right := by
  simpa only [Periodic.segment_length] using
    (p1_iff P (Periodic.segment f 0 n) left right shift h).mpr ⟨of_global P f n left right shift v hl hr hk⟩

end REWB.ResidualSeparated
