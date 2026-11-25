import REWB.BoundaryRangeAutomata
import REWB.IndexedGlobalCoverage

/-! Actual separated equality strips reduce the outer repeated word
to fixed-state boundary conditions. The copied interval is allowed to
have empty subintervals. The shift and all endpoints remain explicit. -/
namespace REWB.ResidualSeparated
open REWB.Spec (slice)
open REWB.BoundaryApplication
open REWB.BoundaryRange
variable {α : Type}

structure Window (w : Word α) (left right shift : Nat) : Prop where
  ordered : left≤right
  within : right+shift≤w.length
  separated : right≤left+shift
  equal : slice w left right=slice w (left+shift) (right+shift)

theorem slice_inside (w : Word α) (left right a b : Nat)
    (hla : left≤a) (hab : a≤b) (hbr : b≤right) :
    slice (slice w left right) (a-left) (b-left)=slice w a b := by
  unfold slice
  rw [List.drop_take,List.drop_drop,List.take_take]
  congr 1
  · omega
  · congr 1
    omega

theorem Window.copy (w : Word α) (left right shift a b : Nat)
    (h : Window w left right shift) (hla : left≤a) (hab : a≤b) (hbr : b≤right) :
    slice w a b=slice w (a+shift) (b+shift) := by
  have he:=congrArg (fun v=>slice v (a-left) (b-left)) h.equal
  dsimp only at he
  rw [slice_inside w left right a b hla hab hbr] at he
  have ht:=slice_inside w (left+shift) (right+shift) (a+shift) (b+shift)
    (by omega) (by omega) (by omega)
  simp only [Nat.add_sub_add_right] at ht
  exact he.trans ht

theorem window_of_strip (f : Nat→α) (n left right shift : Nat)
    (h : GlobalCoverage.MaximalStrip f n left right shift)
    (hs : right-left≤shift) :
    Window (Periodic.segment f 0 n) left right shift := by
  obtain ⟨hd,hlr,hrn,he,_,_⟩:=h
  refine ⟨by omega,by simpa only [Periodic.segment_length] using hrn,by omega,?_⟩
  rw [←GlobalSemanticCoverage.factor_slice f n left right (by omega) (by omega),
    ←GlobalSemanticCoverage.factor_slice f n (left+shift) (right+shift) (by omega) hrn]
  simp only [P2Periodic.factor,Nat.add_sub_add_right]
  apply (Periodic.segment_eq_points f left (left+shift) (right-left)).mpr
  intro i hi
  simpa only [Nat.add_assoc,Nat.add_comm shift i] using he (left+i) (by omega) (by omega)

def gapStart (G : DFA α) (ranges : Range.Index G) (left right shift : Nat)
    (q : Fin G.stateCount) : DFA α :=
  Automata.start G ((Range.query G ranges right (left+shift)).map.get q)

def outerSuffix (F G H : DFA α) (ranges : Range.Index H) (right shift n : Nat)
    (q : Fin G.stateCount) : DFA α :=
  Automata.join F (Automata.meet (Automata.stop G q)
    (Automata.tail H (Range.query H ranges (right+shift) n).map))

theorem gap_run (G : DFA α) (w : Word α) (left right shift p e : Nat)
    (h : Window w left right shift) (hlp : left≤p) (hpe : p≤e) (her : e≤right) :
    G.run G.initial (slice w e (p+shift))=
      G.run ((Range.query G (Range.build G w) right (left+shift)).map.get
        (G.run G.initial (slice w e right))) (slice w left p) := by
  rw [Range.query_correct G w right (left+shift) h.separated (by have hh:=h.within; omega),
    OuterColumn.slice_split w e right (p+shift) her (by have hh:=h.separated; omega),
    DFA.run_append,OuterColumn.slice_split w right (left+shift) (p+shift)
      h.separated (by omega),DFA.run_append,
    ←h.copy w left right shift left p (Nat.le_refl _) hlp (by omega)]

theorem tail_accepts (H : DFA α) (w : Word α) (left right shift e : Nat)
    (h : Window w left right shift) (hle : left≤e) (her : e≤right) :
    (Automata.tail H (Range.query H (Range.build H w) (right+shift) w.length).map).accepts
      (slice w e right) ↔ H.accepts (slice w (e+shift) w.length) := by
  rw [Automata.tail_accepts,Range.query_correct H w (right+shift) w.length h.within (Nat.le_refl _),
    h.copy w left right shift e right hle her (Nat.le_refl _)]
  rw [OuterColumn.slice_split w (e+shift) (right+shift) w.length (by omega) h.within]
  simp only [DFA.accepts,DFA.run_append]

theorem outerSuffix_accepts (F G H : DFA α) (w : Word α) (left right shift t : Nat)
    (h : Window w left right shift) (hlt : left≤t) (htr : t≤right)
    (q : Fin G.stateCount) :
    (outerSuffix F G H (Range.build H w) right shift w.length q).accepts (slice w t right) ↔
      ∃e,t≤e ∧ e≤right ∧ F.accepts (slice w t e) ∧
        G.run G.initial (slice w e right)=q ∧ H.accepts (slice w (e+shift) w.length) := by
  rw [outerSuffix,Automata.join_slice _ _ w t right htr (by have hh:=h.within; omega)]
  constructor
  · rintro ⟨e,hte,her,hF,hBoth⟩
    obtain ⟨hG,hH⟩:=(Automata.meet_accepts _ _ _).mp hBoth
    exact ⟨e,hte,her,hF,(Automata.stop_accepts G q _).mp hG,
      (tail_accepts H w left right shift e h (by omega) her).mp hH⟩
  · rintro ⟨e,hte,her,hF,hG,hH⟩
    exact ⟨e,hte,her,hF,(Automata.meet_accepts _ _ _).mpr
      ⟨(Automata.stop_accepts G q _).mpr hG,
       (tail_accepts H w left right shift e h (by omega) her).mpr hH⟩⟩

end REWB.ResidualSeparated
