import REWB.ResidualSeparatedWindow

/-! The P2 separated strip reduces to an ordinary one-use query with
its first copy inside the queried interval. This lower-source bound is
part of the contract; a boundary query allowing earlier sources is not
an interchangeable implementation. -/
namespace REWB.ResidualSeparated
open REWB.Spec (slice)
open REWB.BoundaryApplication
open REWB.BoundaryRange
variable {α : Type}

def innerPrefix (A B G : DFA α) (aranges : Range.Index A) (granges : Range.Index G)
    (left right shift : Nat) (q : Fin G.stateCount) : DFA α :=
  Automata.join (Automata.meet
    (Automata.start A ((Range.query A aranges 0 left).map.get A.initial))
    (gapStart G granges left right shift q)) B

theorem innerPrefix_accepts (A B G : DFA α) (w : Word α)
    (left right shift i : Nat) (hli : left≤i) (hin : i≤w.length) (q : Fin G.stateCount) :
    (innerPrefix A B G (Range.build A w) (Range.build G w) left right shift q).accepts
      (slice w left i) ↔
      ∃p,left≤p ∧ p≤i ∧ A.accepts (slice w 0 p) ∧
        (gapStart G (Range.build G w) left right shift q).accepts (slice w left p) ∧
        B.accepts (slice w p i) := by
  rw [innerPrefix,Automata.join_slice _ _ w left i hli hin]
  constructor
  · rintro ⟨p,hlp,hpi,hBoth,hB⟩
    obtain ⟨hA,hG⟩:=(Automata.meet_accepts _ _ _).mp hBoth
    exact ⟨p,hlp,hpi,(Automata.start_slice A w 0 left p (Nat.zero_le _) hlp (by omega)).mp hA,hG,hB⟩
  · rintro ⟨p,hlp,hpi,hA,hG,hB⟩
    exact ⟨p,hlp,hpi,(Automata.meet_accepts _ _ _).mpr
      ⟨(Automata.start_slice A w 0 left p (Nat.zero_le _) hlp (by omega)).mpr hA,hG⟩,hB⟩

structure P2Witness (P : SevenDFA α) (w : Word α) (left right shift : Nat) where
  p : Nat
  i : Nat
  a : Nat
  j : Nat
  t : Nat
  e : Nat
  pi : p≤i
  ia : i≤a
  aj : a≤j
  jt : j≤t
  te : t≤e
  lp : left≤p
  er : e≤right
  inner : slice w i a=slice w j t
  prefix_ok : P.A.accepts (slice w 0 p)
  before : P.B.accepts (slice w p i)
  capture : P.C.accepts (slice w i a)
  middle : P.D.accepts (slice w a j)
  after : P.F.accepts (slice w t e)
  gap : P.G.accepts (slice w e (p+shift))
  tail : P.H.accepts (slice w (e+shift) w.length)

theorem p2_iff (P : SevenDFA α) (w : Word α) (left right shift : Nat)
    (h : Window w left right shift) :
    (∃q : Fin P.G.stateCount,Spec.oneUseRange
      (innerPrefix P.A P.B P.G (Range.build P.A w) (Range.build P.G w) left right shift q)
      P.C P.D (outerSuffix P.F P.G P.H (Range.build P.H w) right shift w.length q)
      w left right) ↔ Nonempty (P2Witness P w left right shift) := by
  constructor
  · rintro ⟨q,_,hr,i,a,j,t,hli,hia,haj,hjt,htr,he,hPrefix,hC,hD,hSuffix⟩
    obtain ⟨p,hlp,hpi,hA,hK,hB⟩:=
      (innerPrefix_accepts P.A P.B P.G w left right shift i hli (by omega) q).mp hPrefix
    obtain ⟨e,hte,her,hF,hq,hH⟩:=
      (outerSuffix_accepts P.F P.G P.H w left right shift t h (by omega) htr q).mp hSuffix
    have hG : P.G.accepts (slice w e (p+shift)) := by
      change P.G.final (P.G.run P.G.initial (slice w e (p+shift)))=true
      rw [gap_run P.G w left right shift p e h hlp (by omega) her,hq]
      exact (Automata.start_accepts P.G _ _).mp hK
    exact ⟨⟨p,i,a,j,t,e,hpi,hia,haj,hjt,hte,hlp,her,he,hA,hB,hC,hD,hF,hG,hH⟩⟩
  · rintro ⟨v⟩
    have hp:=v.pi
    have hi:=v.ia
    have ha:=v.aj
    have hj:=v.jt
    have ht:=v.te
    have hl:=v.lp
    have hr:=v.er
    have hn:=h.within
    let q:=P.G.run P.G.initial (slice w v.e right)
    refine ⟨q,h.ordered,by omega,v.i,v.a,v.j,v.t,by omega,hi,ha,hj,by omega,v.inner,?_,v.capture,v.middle,?_⟩
    · apply (innerPrefix_accepts P.A P.B P.G w left right shift v.i (by omega) (by omega) q).mpr
      refine ⟨v.p,hl,hp,v.prefix_ok,?_,v.before⟩
      apply (Automata.start_accepts P.G _ _).mpr
      have hh:=v.gap
      change P.G.final (P.G.run P.G.initial (slice w v.e (v.p+shift)))=true at hh
      rw [gap_run P.G w left right shift v.p v.e h hl (by omega) hr] at hh
      exact hh
    · apply (outerSuffix_accepts P.F P.G P.H w left right shift v.t h (by omega) (by omega) q).mpr
      exact ⟨v.e,ht,hr,v.after,rfl,v.tail⟩

theorem P2Witness.sound (P : SevenDFA α) (w : Word α) (left right shift : Nat)
    (h : Window w left right shift) (v : P2Witness P w left right shift) :
    MatchesWithin P.nested2 w 2 := by
  have hp:=v.pi
  have hi:=v.ia
  have ha:=v.aj
  have hj:=v.jt
  have ht:=v.te
  have hl:=v.lp
  have hr:=v.er
  have hn:=h.within
  have hs:=h.separated
  have houter : slice w v.p v.e=
      slice w v.p v.i++slice w v.i v.a++slice w v.a v.j++slice w v.i v.a++slice w v.t v.e := by
    rw [OuterColumn.slice_split w v.p v.i v.e hp (by omega),
      OuterColumn.slice_split w v.i v.a v.e hi (by omega),
      OuterColumn.slice_split w v.a v.j v.e ha (by omega),
      OuterColumn.slice_split w v.j v.t v.e hj ht,←v.inner]
    simp only [List.append_assoc]
  have heq:=h.copy w left right shift v.p v.e hl (by omega) hr
  apply (REWB.Witness.nested2_iff P w).mpr
  refine ⟨slice w 0 v.p,slice w v.p v.i,slice w v.i v.a,
    slice w v.a v.j,slice w v.t v.e,slice w v.e (v.p+shift),slice w (v.e+shift) w.length,
    v.prefix_ok,v.before,v.capture,v.middle,v.after,v.gap,v.tail,?_⟩
  have parts : w=slice w 0 v.p++slice w v.p v.e++slice w v.e (v.p+shift)++
      slice w (v.p+shift) (v.e+shift)++slice w (v.e+shift) w.length := by
    conv => lhs; rw [show w=slice w 0 w.length by simp [slice]]
    rw [OuterColumn.slice_split w 0 v.p w.length (by omega) (by omega),
      OuterColumn.slice_split w v.p v.e w.length (by omega) (by omega),
      OuterColumn.slice_split w v.e (v.p+shift) w.length (by omega) (by omega),
      OuterColumn.slice_split w (v.p+shift) (v.e+shift) w.length (by omega) (by omega)]
    simp only [List.append_assoc]
  rw [←heq] at parts
  simpa only [houter,List.append_assoc] using parts

def p2_of_global (P : SevenDFA α) (f : Nat→α) (n left right shift : Nat)
    (x : P2Periodic.Layout Nat) (v : P2Periodic.Witness P f n [] [] x)
    (hl : left≤x.p) (hr : x.e≤right) (hk : x.k=x.p+shift) :
    P2Witness P (Periodic.segment f 0 n) left right shift := by
  obtain ⟨hpi,hia,haj,hjt,hte,hek,hkf,hfn,hA,hB,hC,hD,hF,hG,hH,he,houter⟩:=v
  have hlen:=congrArg List.length houter
  simp only [P2Periodic.factor,Periodic.segment_length] at hlen
  have hf : x.f=x.e+shift := by omega
  simp only [List.nil_append,List.append_nil] at hA hH
  have fac (a b : Nat) (hab : a≤b) (hbn : b≤n):=
    GlobalSemanticCoverage.factor_slice f n a b hab hbn
  refine ⟨x.p,x.i,x.a,x.j,x.t,x.e,hpi,hia,haj,hjt,hte,hl,hr,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rwa [fac x.i x.a hia (by omega),fac x.j x.t hjt (by omega)] at he
  · rwa [fac 0 x.p (Nat.zero_le _) (by omega)] at hA
  · rwa [fac x.p x.i hpi (by omega)] at hB
  · rwa [fac x.i x.a hia (by omega)] at hC
  · rwa [fac x.a x.j haj (by omega)] at hD
  · rwa [fac x.t x.e hte (by omega)] at hF
  · rw [fac x.e x.k hek (by omega),hk] at hG
    exact hG
  · rw [fac x.f n hfn (Nat.le_refl _),hf] at hH
    simpa only [Periodic.segment_length] using hH

theorem p2_complete (P : SevenDFA α) (f : Nat→α) (n left right shift : Nat)
    (h : Window (Periodic.segment f 0 n) left right shift)
    (x : P2Periodic.Layout Nat) (v : P2Periodic.Witness P f n [] [] x)
    (hl : left≤x.p) (hr : x.e≤right) (hk : x.k=x.p+shift) :
    ∃q : Fin P.G.stateCount,Spec.oneUseRange
      (innerPrefix P.A P.B P.G (Range.build P.A (Periodic.segment f 0 n))
        (Range.build P.G (Periodic.segment f 0 n)) left right shift q)
      P.C P.D (outerSuffix P.F P.G P.H (Range.build P.H (Periodic.segment f 0 n)) right shift n q)
      (Periodic.segment f 0 n) left right := by
  simpa only [Periodic.segment_length] using
    (p2_iff P (Periodic.segment f 0 n) left right shift h).mpr
      ⟨p2_of_global P f n left right shift x v hl hr hk⟩

end REWB.ResidualSeparated
