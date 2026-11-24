import REWB.Semantics

/-! Exact witnesses for four fixed normal forms. Normalization of an arbitrary
    expression is a separate obligation, as is the time bound. -/
namespace REWB
variable {α : Type}

structure SevenDFA (α : Type) where
  A : DFA α
  B : DFA α
  C : DFA α
  D : DFA α
  F : DFA α
  G : DFA α
  H : DFA α

structure FiveDFA (α : Type) where
  A : DFA α
  B : DFA α
  C : DFA α
  D : DFA α
  E : DFA α

def FiveDFA.sameValue (p : FiveDFA α) : Expr α :=
  .atom p.A ⋙ .capture (.atom p.B) ⋙ .atom p.C ⋙ .reference ⋙ .atom p.D ⋙ .reference ⋙ .atom p.E

def SevenDFA.independent (p : SevenDFA α) : Expr α :=
  .atom p.A ⋙ .capture (.atom p.B) ⋙ .atom p.C ⋙ .reference ⋙ .atom p.D ⋙ .capture (.atom p.F) ⋙ .atom p.G ⋙ .reference ⋙ .atom p.H

def SevenDFA.nested1 (p : SevenDFA α) : Expr α :=
  .atom p.A ⋙ .capture (.atom p.B) ⋙ .atom p.C ⋙ .capture (.atom p.D ⋙ .reference ⋙ .atom p.F) ⋙ .atom p.G ⋙ .reference ⋙ .atom p.H

def SevenDFA.nested2 (p : SevenDFA α) : Expr α :=
  .atom p.A ⋙ .capture (.atom p.B ⋙ .capture (.atom p.C) ⋙ .atom p.D ⋙ .reference ⋙ .atom p.F) ⋙ .atom p.G ⋙ .reference ⋙ .atom p.H

namespace TraceOf

theorem atom_iff {d : DFA α} {es : List (Event α)} :
    TraceOf (.atom d) es ↔ ∃ u, d.accepts u ∧ es = [.emit u] := by
  constructor
  · intro h
    cases h
    exact ⟨_, by assumption, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact .atom d u hu

theorem seq_iff {p q : Expr α} {es : List (Event α)} :
    TraceOf (p ⋙ q) es ↔
      ∃ xs ys, TraceOf p xs ∧ TraceOf q ys ∧ es = xs ++ ys := by
  constructor
  · intro h
    cases h with
    | seq hp hq => exact ⟨_, _, hp, hq, rfl⟩
  · rintro ⟨xs, ys, hp, hq, rfl⟩
    exact .seq hp hq

theorem capture_iff {p : Expr α} {es : List (Event α)} :
    TraceOf (.capture p) es ↔
      ∃ xs, TraceOf p xs ∧ es = [.openCap] ++ xs ++ [.closeCap] := by
  constructor
  · intro h
    cases h with
    | capture hp => exact ⟨_, hp, rfl⟩
  · rintro ⟨xs, hp, rfl⟩
    exact .capture hp

theorem reference_iff {es : List (Event α)} :
    TraceOf (.reference : Expr α) es ↔ es = [.recall] := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst es
    exact .reference

end TraceOf

namespace Witness

def sameTrace (a u c d e : Word α) : List (Event α) :=
  [.emit a, .openCap, .emit u, .closeCap, .emit c, .recall, .emit d, .recall, .emit e]

theorem sameTrace_execute (a u c d e : Word α) :
    State.execute (State.initial []) (sameTrace a u c d e) =
      some ⟨a ++ u ++ c ++ u ++ d ++ u ++ e, u, [], 2⟩ := by
  simp [sameTrace, State.execute, State.step, State.appendText,
    State.initial, Option.bind, List.append_assoc]

theorem sameTrace_generated (p : FiveDFA α) (a u c d e : Word α)
    (ha : p.A.accepts a) (hu : p.B.accepts u) (hc : p.C.accepts c) (hd : p.D.accepts d) (he : p.E.accepts e) :
    TraceOf p.sameValue (sameTrace a u c d e) := by
  exact .seq (.atom p.A a ha) (.seq (.capture (.atom p.B u hu)) (.seq (.atom p.C c hc) (.seq (.reference) (.seq (.atom p.D d hd) (.seq (.reference) (.atom p.E e he))))))

theorem sameTrace_iff (p : FiveDFA α) (es : List (Event α)) :
    TraceOf p.sameValue es ↔
      ∃ a u c d e : Word α, p.A.accepts a ∧ p.B.accepts u ∧ p.C.accepts c ∧ p.D.accepts d ∧ p.E.accepts e ∧
        es = sameTrace a u c d e := by
  constructor
  · intro ht
    unfold FiveDFA.sameValue at ht
    rcases TraceOf.seq_iff.mp ht with ⟨es1l, es1r, ht1l, ht1r, he1⟩
    rcases TraceOf.atom_iff.mp ht1l with ⟨a, ha, he2⟩
    rcases TraceOf.seq_iff.mp ht1r with ⟨es3l, es3r, ht3l, ht3r, he3⟩
    rcases TraceOf.capture_iff.mp ht3l with ⟨es4c, ht4c, he4⟩
    rcases TraceOf.atom_iff.mp ht4c with ⟨u, hu, he5⟩
    rcases TraceOf.seq_iff.mp ht3r with ⟨es6l, es6r, ht6l, ht6r, he6⟩
    rcases TraceOf.atom_iff.mp ht6l with ⟨c, hc, he7⟩
    rcases TraceOf.seq_iff.mp ht6r with ⟨es8l, es8r, ht8l, ht8r, he8⟩
    have he9 := TraceOf.reference_iff.mp ht8l
    rcases TraceOf.seq_iff.mp ht8r with ⟨es10l, es10r, ht10l, ht10r, he10⟩
    rcases TraceOf.atom_iff.mp ht10l with ⟨d, hd, he11⟩
    rcases TraceOf.seq_iff.mp ht10r with ⟨es12l, es12r, ht12l, ht12r, he12⟩
    have he13 := TraceOf.reference_iff.mp ht12l
    rcases TraceOf.atom_iff.mp ht12r with ⟨e, he, he14⟩
    refine ⟨a, u, c, d, e, ha, hu, hc, hd, he, ?_⟩
    simp [he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12, he13, he14, sameTrace]
  · rintro ⟨a, u, c, d, e, ha, hu, hc, hd, he, rfl⟩
    exact sameTrace_generated p a u c d e ha hu hc hd he

theorem same_iff (p : FiveDFA α) (w : Word α) :
    MatchesWithin p.sameValue w 2 ↔
      ∃ a u c d e : Word α, p.A.accepts a ∧ p.B.accepts u ∧ p.C.accepts c ∧ p.D.accepts d ∧ p.E.accepts e ∧
        w = a ++ u ++ c ++ u ++ d ++ u ++ e := by
  constructor
  · intro hm
    rcases hm with ⟨es, st, ht, hr, _, ho, _⟩
    rcases (sameTrace_iff p es).mp ht with ⟨a, u, c, d, e, ha, hu, hc, hd, he, rfl⟩
    rw [sameTrace_execute] at hr
    simp only [Option.some.injEq] at hr
    subst st
    exact ⟨a, u, c, d, e, ha, hu, hc, hd, he, ho.symm⟩
  · rintro ⟨a, u, c, d, e, ha, hu, hc, hd, he, rfl⟩
    exact ⟨sameTrace a u c d e, _, sameTrace_generated p a u c d e ha hu hc hd he,
      sameTrace_execute a u c d e, rfl, rfl, Nat.le_refl 2⟩

def independentTrace (a u c d v g h : Word α) : List (Event α) :=
  [.emit a, .openCap, .emit u, .closeCap, .emit c, .recall, .emit d, .openCap, .emit v, .closeCap, .emit g, .recall, .emit h]

theorem independentTrace_execute (a u c d v g h : Word α) :
    State.execute (State.initial []) (independentTrace a u c d v g h) =
      some ⟨a ++ u ++ c ++ u ++ d ++ v ++ g ++ v ++ h, v, [], 2⟩ := by
  simp [independentTrace, State.execute, State.step, State.appendText,
    State.initial, Option.bind, List.append_assoc]

theorem independentTrace_generated (p : SevenDFA α) (a u c d v g h : Word α)
    (ha : p.A.accepts a) (hu : p.B.accepts u) (hc : p.C.accepts c) (hd : p.D.accepts d) (hv : p.F.accepts v) (hg : p.G.accepts g) (hh : p.H.accepts h) :
    TraceOf p.independent (independentTrace a u c d v g h) := by
  exact .seq (.atom p.A a ha) (.seq (.capture (.atom p.B u hu)) (.seq (.atom p.C c hc) (.seq (.reference) (.seq (.atom p.D d hd) (.seq (.capture (.atom p.F v hv)) (.seq (.atom p.G g hg) (.seq (.reference) (.atom p.H h hh))))))))

theorem independentTrace_iff (p : SevenDFA α) (es : List (Event α)) :
    TraceOf p.independent es ↔
      ∃ a u c d v g h : Word α, p.A.accepts a ∧ p.B.accepts u ∧ p.C.accepts c ∧ p.D.accepts d ∧ p.F.accepts v ∧ p.G.accepts g ∧ p.H.accepts h ∧
        es = independentTrace a u c d v g h := by
  constructor
  · intro ht
    unfold SevenDFA.independent at ht
    rcases TraceOf.seq_iff.mp ht with ⟨es1l, es1r, ht1l, ht1r, he1⟩
    rcases TraceOf.atom_iff.mp ht1l with ⟨a, ha, he2⟩
    rcases TraceOf.seq_iff.mp ht1r with ⟨es3l, es3r, ht3l, ht3r, he3⟩
    rcases TraceOf.capture_iff.mp ht3l with ⟨es4c, ht4c, he4⟩
    rcases TraceOf.atom_iff.mp ht4c with ⟨u, hu, he5⟩
    rcases TraceOf.seq_iff.mp ht3r with ⟨es6l, es6r, ht6l, ht6r, he6⟩
    rcases TraceOf.atom_iff.mp ht6l with ⟨c, hc, he7⟩
    rcases TraceOf.seq_iff.mp ht6r with ⟨es8l, es8r, ht8l, ht8r, he8⟩
    have he9 := TraceOf.reference_iff.mp ht8l
    rcases TraceOf.seq_iff.mp ht8r with ⟨es10l, es10r, ht10l, ht10r, he10⟩
    rcases TraceOf.atom_iff.mp ht10l with ⟨d, hd, he11⟩
    rcases TraceOf.seq_iff.mp ht10r with ⟨es12l, es12r, ht12l, ht12r, he12⟩
    rcases TraceOf.capture_iff.mp ht12l with ⟨es13c, ht13c, he13⟩
    rcases TraceOf.atom_iff.mp ht13c with ⟨v, hv, he14⟩
    rcases TraceOf.seq_iff.mp ht12r with ⟨es15l, es15r, ht15l, ht15r, he15⟩
    rcases TraceOf.atom_iff.mp ht15l with ⟨g, hg, he16⟩
    rcases TraceOf.seq_iff.mp ht15r with ⟨es17l, es17r, ht17l, ht17r, he17⟩
    have he18 := TraceOf.reference_iff.mp ht17l
    rcases TraceOf.atom_iff.mp ht17r with ⟨h, hh, he19⟩
    refine ⟨a, u, c, d, v, g, h, ha, hu, hc, hd, hv, hg, hh, ?_⟩
    simp [he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12, he13, he14, he15, he16, he17, he18, he19, independentTrace]
  · rintro ⟨a, u, c, d, v, g, h, ha, hu, hc, hd, hv, hg, hh, rfl⟩
    exact independentTrace_generated p a u c d v g h ha hu hc hd hv hg hh

theorem independent_iff (p : SevenDFA α) (w : Word α) :
    MatchesWithin p.independent w 2 ↔
      ∃ a u c d v g h : Word α, p.A.accepts a ∧ p.B.accepts u ∧ p.C.accepts c ∧ p.D.accepts d ∧ p.F.accepts v ∧ p.G.accepts g ∧ p.H.accepts h ∧
        w = a ++ u ++ c ++ u ++ d ++ v ++ g ++ v ++ h := by
  constructor
  · intro hm
    rcases hm with ⟨es, st, ht, hr, _, ho, _⟩
    rcases (independentTrace_iff p es).mp ht with ⟨a, u, c, d, v, g, h, ha, hu, hc, hd, hv, hg, hh, rfl⟩
    rw [independentTrace_execute] at hr
    simp only [Option.some.injEq] at hr
    subst st
    exact ⟨a, u, c, d, v, g, h, ha, hu, hc, hd, hv, hg, hh, ho.symm⟩
  · rintro ⟨a, u, c, d, v, g, h, ha, hu, hc, hd, hv, hg, hh, rfl⟩
    exact ⟨independentTrace a u c d v g h, _, independentTrace_generated p a u c d v g h ha hu hc hd hv hg hh,
      independentTrace_execute a u c d v g h, rfl, rfl, Nat.le_refl 2⟩

def nested1Trace (a u c d f g h : Word α) : List (Event α) :=
  [.emit a, .openCap, .emit u, .closeCap, .emit c, .openCap, .emit d, .recall, .emit f, .closeCap, .emit g, .recall, .emit h]

theorem nested1Trace_execute (a u c d f g h : Word α) :
    State.execute (State.initial []) (nested1Trace a u c d f g h) =
      some ⟨a ++ u ++ c ++ (d ++ u ++ f) ++ g ++ (d ++ u ++ f) ++ h, d ++ u ++ f, [], 2⟩ := by
  simp [nested1Trace, State.execute, State.step, State.appendText,
    State.initial, Option.bind, List.append_assoc]

theorem nested1Trace_generated (p : SevenDFA α) (a u c d f g h : Word α)
    (ha : p.A.accepts a) (hu : p.B.accepts u) (hc : p.C.accepts c) (hd : p.D.accepts d) (hf : p.F.accepts f) (hg : p.G.accepts g) (hh : p.H.accepts h) :
    TraceOf p.nested1 (nested1Trace a u c d f g h) := by
  exact .seq (.atom p.A a ha) (.seq (.capture (.atom p.B u hu)) (.seq (.atom p.C c hc) (.seq (.capture (.seq (.atom p.D d hd) (.seq (.reference) (.atom p.F f hf)))) (.seq (.atom p.G g hg) (.seq (.reference) (.atom p.H h hh))))))

theorem nested1Trace_iff (p : SevenDFA α) (es : List (Event α)) :
    TraceOf p.nested1 es ↔
      ∃ a u c d f g h : Word α, p.A.accepts a ∧ p.B.accepts u ∧ p.C.accepts c ∧ p.D.accepts d ∧ p.F.accepts f ∧ p.G.accepts g ∧ p.H.accepts h ∧
        es = nested1Trace a u c d f g h := by
  constructor
  · intro ht
    unfold SevenDFA.nested1 at ht
    rcases TraceOf.seq_iff.mp ht with ⟨es1l, es1r, ht1l, ht1r, he1⟩
    rcases TraceOf.atom_iff.mp ht1l with ⟨a, ha, he2⟩
    rcases TraceOf.seq_iff.mp ht1r with ⟨es3l, es3r, ht3l, ht3r, he3⟩
    rcases TraceOf.capture_iff.mp ht3l with ⟨es4c, ht4c, he4⟩
    rcases TraceOf.atom_iff.mp ht4c with ⟨u, hu, he5⟩
    rcases TraceOf.seq_iff.mp ht3r with ⟨es6l, es6r, ht6l, ht6r, he6⟩
    rcases TraceOf.atom_iff.mp ht6l with ⟨c, hc, he7⟩
    rcases TraceOf.seq_iff.mp ht6r with ⟨es8l, es8r, ht8l, ht8r, he8⟩
    rcases TraceOf.capture_iff.mp ht8l with ⟨es9c, ht9c, he9⟩
    rcases TraceOf.seq_iff.mp ht9c with ⟨es10l, es10r, ht10l, ht10r, he10⟩
    rcases TraceOf.atom_iff.mp ht10l with ⟨d, hd, he11⟩
    rcases TraceOf.seq_iff.mp ht10r with ⟨es12l, es12r, ht12l, ht12r, he12⟩
    have he13 := TraceOf.reference_iff.mp ht12l
    rcases TraceOf.atom_iff.mp ht12r with ⟨f, hf, he14⟩
    rcases TraceOf.seq_iff.mp ht8r with ⟨es15l, es15r, ht15l, ht15r, he15⟩
    rcases TraceOf.atom_iff.mp ht15l with ⟨g, hg, he16⟩
    rcases TraceOf.seq_iff.mp ht15r with ⟨es17l, es17r, ht17l, ht17r, he17⟩
    have he18 := TraceOf.reference_iff.mp ht17l
    rcases TraceOf.atom_iff.mp ht17r with ⟨h, hh, he19⟩
    refine ⟨a, u, c, d, f, g, h, ha, hu, hc, hd, hf, hg, hh, ?_⟩
    simp [he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12, he13, he14, he15, he16, he17, he18, he19, nested1Trace]
  · rintro ⟨a, u, c, d, f, g, h, ha, hu, hc, hd, hf, hg, hh, rfl⟩
    exact nested1Trace_generated p a u c d f g h ha hu hc hd hf hg hh

theorem nested1_iff (p : SevenDFA α) (w : Word α) :
    MatchesWithin p.nested1 w 2 ↔
      ∃ a u c d f g h : Word α, p.A.accepts a ∧ p.B.accepts u ∧ p.C.accepts c ∧ p.D.accepts d ∧ p.F.accepts f ∧ p.G.accepts g ∧ p.H.accepts h ∧
        w = a ++ u ++ c ++ (d ++ u ++ f) ++ g ++ (d ++ u ++ f) ++ h := by
  constructor
  · intro hm
    rcases hm with ⟨es, st, ht, hr, _, ho, _⟩
    rcases (nested1Trace_iff p es).mp ht with ⟨a, u, c, d, f, g, h, ha, hu, hc, hd, hf, hg, hh, rfl⟩
    rw [nested1Trace_execute] at hr
    simp only [Option.some.injEq] at hr
    subst st
    exact ⟨a, u, c, d, f, g, h, ha, hu, hc, hd, hf, hg, hh, ho.symm⟩
  · rintro ⟨a, u, c, d, f, g, h, ha, hu, hc, hd, hf, hg, hh, rfl⟩
    exact ⟨nested1Trace a u c d f g h, _, nested1Trace_generated p a u c d f g h ha hu hc hd hf hg hh,
      nested1Trace_execute a u c d f g h, rfl, rfl, Nat.le_refl 2⟩

theorem nested1_sound (p : SevenDFA α) (a u c d f g h : Word α)
    (ha : p.A.accepts a) (hu : p.B.accepts u) (hc : p.C.accepts c) (hd : p.D.accepts d) (hf : p.F.accepts f) (hg : p.G.accepts g) (hh : p.H.accepts h) :
    MatchesWithin p.nested1 (a ++ u ++ c ++ (d ++ u ++ f) ++ g ++ (d ++ u ++ f) ++ h) 2 := by
  exact (nested1_iff p _).mpr ⟨a, u, c, d, f, g, h, ha, hu, hc, hd, hf, hg, hh, rfl⟩

def nested2Trace (a b u d f g h : Word α) : List (Event α) :=
  [.emit a, .openCap, .emit b, .openCap, .emit u, .closeCap, .emit d, .recall, .emit f, .closeCap, .emit g, .recall, .emit h]

theorem nested2Trace_execute (a b u d f g h : Word α) :
    State.execute (State.initial []) (nested2Trace a b u d f g h) =
      some ⟨a ++ (b ++ u ++ d ++ u ++ f) ++ g ++ (b ++ u ++ d ++ u ++ f) ++ h, b ++ u ++ d ++ u ++ f, [], 2⟩ := by
  simp [nested2Trace, State.execute, State.step, State.appendText,
    State.initial, Option.bind, List.append_assoc]

theorem nested2Trace_generated (p : SevenDFA α) (a b u d f g h : Word α)
    (ha : p.A.accepts a) (hb : p.B.accepts b) (hu : p.C.accepts u) (hd : p.D.accepts d) (hf : p.F.accepts f) (hg : p.G.accepts g) (hh : p.H.accepts h) :
    TraceOf p.nested2 (nested2Trace a b u d f g h) := by
  exact .seq (.atom p.A a ha) (.seq (.capture (.seq (.atom p.B b hb) (.seq (.capture (.atom p.C u hu)) (.seq (.atom p.D d hd) (.seq (.reference) (.atom p.F f hf)))))) (.seq (.atom p.G g hg) (.seq (.reference) (.atom p.H h hh))))

theorem nested2Trace_iff (p : SevenDFA α) (es : List (Event α)) :
    TraceOf p.nested2 es ↔
      ∃ a b u d f g h : Word α, p.A.accepts a ∧ p.B.accepts b ∧ p.C.accepts u ∧ p.D.accepts d ∧ p.F.accepts f ∧ p.G.accepts g ∧ p.H.accepts h ∧
        es = nested2Trace a b u d f g h := by
  constructor
  · intro ht
    unfold SevenDFA.nested2 at ht
    rcases TraceOf.seq_iff.mp ht with ⟨es1l, es1r, ht1l, ht1r, he1⟩
    rcases TraceOf.atom_iff.mp ht1l with ⟨a, ha, he2⟩
    rcases TraceOf.seq_iff.mp ht1r with ⟨es3l, es3r, ht3l, ht3r, he3⟩
    rcases TraceOf.capture_iff.mp ht3l with ⟨es4c, ht4c, he4⟩
    rcases TraceOf.seq_iff.mp ht4c with ⟨es5l, es5r, ht5l, ht5r, he5⟩
    rcases TraceOf.atom_iff.mp ht5l with ⟨b, hb, he6⟩
    rcases TraceOf.seq_iff.mp ht5r with ⟨es7l, es7r, ht7l, ht7r, he7⟩
    rcases TraceOf.capture_iff.mp ht7l with ⟨es8c, ht8c, he8⟩
    rcases TraceOf.atom_iff.mp ht8c with ⟨u, hu, he9⟩
    rcases TraceOf.seq_iff.mp ht7r with ⟨es10l, es10r, ht10l, ht10r, he10⟩
    rcases TraceOf.atom_iff.mp ht10l with ⟨d, hd, he11⟩
    rcases TraceOf.seq_iff.mp ht10r with ⟨es12l, es12r, ht12l, ht12r, he12⟩
    have he13 := TraceOf.reference_iff.mp ht12l
    rcases TraceOf.atom_iff.mp ht12r with ⟨f, hf, he14⟩
    rcases TraceOf.seq_iff.mp ht3r with ⟨es15l, es15r, ht15l, ht15r, he15⟩
    rcases TraceOf.atom_iff.mp ht15l with ⟨g, hg, he16⟩
    rcases TraceOf.seq_iff.mp ht15r with ⟨es17l, es17r, ht17l, ht17r, he17⟩
    have he18 := TraceOf.reference_iff.mp ht17l
    rcases TraceOf.atom_iff.mp ht17r with ⟨h, hh, he19⟩
    refine ⟨a, b, u, d, f, g, h, ha, hb, hu, hd, hf, hg, hh, ?_⟩
    simp [he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12, he13, he14, he15, he16, he17, he18, he19, nested2Trace]
  · rintro ⟨a, b, u, d, f, g, h, ha, hb, hu, hd, hf, hg, hh, rfl⟩
    exact nested2Trace_generated p a b u d f g h ha hb hu hd hf hg hh

theorem nested2_iff (p : SevenDFA α) (w : Word α) :
    MatchesWithin p.nested2 w 2 ↔
      ∃ a b u d f g h : Word α, p.A.accepts a ∧ p.B.accepts b ∧ p.C.accepts u ∧ p.D.accepts d ∧ p.F.accepts f ∧ p.G.accepts g ∧ p.H.accepts h ∧
        w = a ++ (b ++ u ++ d ++ u ++ f) ++ g ++ (b ++ u ++ d ++ u ++ f) ++ h := by
  constructor
  · intro hm
    rcases hm with ⟨es, st, ht, hr, _, ho, _⟩
    rcases (nested2Trace_iff p es).mp ht with ⟨a, b, u, d, f, g, h, ha, hb, hu, hd, hf, hg, hh, rfl⟩
    rw [nested2Trace_execute] at hr
    simp only [Option.some.injEq] at hr
    subst st
    exact ⟨a, b, u, d, f, g, h, ha, hb, hu, hd, hf, hg, hh, ho.symm⟩
  · rintro ⟨a, b, u, d, f, g, h, ha, hb, hu, hd, hf, hg, hh, rfl⟩
    exact ⟨nested2Trace a b u d f g h, _, nested2Trace_generated p a b u d f g h ha hb hu hd hf hg hh,
      nested2Trace_execute a b u d f g h, rfl, rfl, Nat.le_refl 2⟩

theorem nested2_sound (p : SevenDFA α) (a b u d f g h : Word α)
    (ha : p.A.accepts a) (hb : p.B.accepts b) (hu : p.C.accepts u) (hd : p.D.accepts d) (hf : p.F.accepts f) (hg : p.G.accepts g) (hh : p.H.accepts h) :
    MatchesWithin p.nested2 (a ++ (b ++ u ++ d ++ u ++ f) ++ g ++ (b ++ u ++ d ++ u ++ f) ++ h) 2 := by
  exact (nested2_iff p _).mpr ⟨a, b, u, d, f, g, h, ha, hb, hu, hd, hf, hg, hh, rfl⟩

end Witness

/-- Selected supplier event intervals, not character intervals. -/
def Laminar (o₁ c₁ o₂ c₂ : Nat) : Prop :=
  c₁ < o₂ ∨ c₂ < o₁ ∨ (o₁ < o₂ ∧ c₂ < c₁) ∨ (o₂ < o₁ ∧ c₁ < c₂)

theorem classify_distinct_suppliers (o₁ c₁ r₁ o₂ c₂ r₂ : Nat)
    (h₁ : o₁ < c₁) (h₂ : c₁ < r₁) (h₃ : r₁ < c₂)
    (h₄ : c₂ < r₂) (h₅ : o₂ < c₂) (hne : o₂ ≠ r₁)
    (hlam : Laminar o₁ c₁ o₂ c₂) :
    (r₁ < o₂) ∨ (c₁ < o₂ ∧ o₂ < r₁) ∨ (o₂ < o₁ ∧ r₁ < c₂) := by
  rcases hlam with h | h | h | h <;> omega

end REWB
