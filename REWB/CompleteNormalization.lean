import REWB.RegularDFA

/-! Complete fixed-pattern normalization from the original operational
semantics to a finite union of ordinary, one-use, and the four concrete
two-use forms. The compiler constructs the factor DFAs; no regularity or
normalization oracle is assumed. -/
namespace REWB.CompleteNormalization
open REWB.ControlShapes
open REWB.MarkedFactors
variable {α : Type}

def cat (A B : DFA α) : DFA α :=
  (RegularDFA.concatenate (RegularDFA.lift A) (RegularDFA.lift B)).toDFA

theorem cat_accepts (A B : DFA α) (w : Word α) :
    (cat A B).accepts w ↔ ∃ u v,w=u++v ∧ A.accepts u ∧ B.accepts v := by
  rw [cat,RegularDFA.Machine.toDFA_correct,RegularDFA.concatenate_correct]
  simp only [LiveLanguage.join,RegularDFA.lift_correct]

def once (A B C E : DFA α) : Expr α :=
  .atom A ⋙ .capture (.atom B) ⋙ .atom C ⋙ .reference ⋙ .atom E

theorem atom_matches (A : DFA α) (w : Word α) :
    MatchesWithin (.atom A) w 2 ↔ A.accepts w := by
  constructor
  · rintro ⟨es,s,ht,hr,_,ho,_⟩
    obtain ⟨u,hu,rfl⟩ := TraceOf.atom_iff.mp ht
    have he : s={ State.initial [] with output := u } := by
      simpa [State.execute,State.step,State.initial,State.appendText] using hr.symm
    subst s
    simpa using ho ▸ hu
  · intro hw
    refine ⟨[.emit w],⟨w,[],[],0⟩,.atom A w hw,?_,rfl,rfl,by change 0≤2; decide⟩
    simp [State.execute,State.step,State.initial,State.appendText]

theorem once_matches (A B C E : DFA α) (w : Word α) :
    MatchesWithin (once A B C E) w 2 ↔
      ∃ a b c e,A.accepts a ∧ B.accepts b ∧ C.accepts c ∧ E.accepts e ∧
        w=a++b++c++b++e := by
  constructor
  · rintro ⟨es,s,ht,hr,hb,ho,hk⟩
    unfold once at ht
    obtain ⟨esA,restA,hAtrace,hRestA,rfl⟩ := TraceOf.seq_iff.mp ht
    obtain ⟨a,ha,rfl⟩ := TraceOf.atom_iff.mp hAtrace
    obtain ⟨esCap,restCap,hCap,hRestCap,rfl⟩ := TraceOf.seq_iff.mp hRestA
    obtain ⟨esB,hBtrace,rfl⟩ := TraceOf.capture_iff.mp hCap
    obtain ⟨b,hB,rfl⟩ := TraceOf.atom_iff.mp hBtrace
    obtain ⟨esC,restC,hCtrace,hRestC,rfl⟩ := TraceOf.seq_iff.mp hRestCap
    obtain ⟨c,hC,rfl⟩ := TraceOf.atom_iff.mp hCtrace
    obtain ⟨esR,esE,hRtrace,hEtrace,rfl⟩ := TraceOf.seq_iff.mp hRestC
    have hrx := TraceOf.reference_iff.mp hRtrace
    obtain ⟨e,hE,rfl⟩ := TraceOf.atom_iff.mp hEtrace
    subst esR
    have hs : s=⟨a++b++c++b++e,b,[],1⟩ := by
      simpa [State.execute,State.step,State.initial,State.appendText,
        List.append_assoc] using hr.symm
    subst s
    exact ⟨a,b,c,e,ha,hB,hC,hE,ho.symm⟩
  · rintro ⟨a,b,c,e,ha,hb,hc,he,rfl⟩
    refine ⟨[.emit a,.openCap,.emit b,.closeCap,.emit c,.recall,.emit e],
      ⟨a++b++c++b++e,b,[],1⟩,?_,?_,rfl,rfl,by change 1≤2; decide⟩
    · exact .seq (.atom A a ha) (.seq (.capture (.atom B b hb))
        (.seq (.atom C c hc) (.seq .reference (.atom E e he))))
    · simp [State.execute,State.step,State.initial,State.appendText,List.append_assoc]

inductive Form (α : Type) where
  | regular : DFA α → Form α
  | once : DFA α → DFA α → DFA α → DFA α → Form α
  | sameValue : FiveDFA α → Form α
  | independent : SevenDFA α → Form α
  | nested1 : SevenDFA α → Form α
  | nested2 : SevenDFA α → Form α

def Form.expr : Form α→Expr α
  | .regular A => .atom A
  | .once A B C E => CompleteNormalization.once A B C E
  | .sameValue P => P.sameValue
  | .independent P => P.independent
  | .nested1 P => P.nested1
  | .nested2 P => P.nested2

/-- Initial-empty recalls disappear; their neighboring regular factors
    are combined by the concrete DFA concatenation constructor. -/
def assemble : Shape→List (DFA α)→Option (Form α)
  | .regular,[A] => some (.regular A)
  | .emptyOnce,[A,B] => some (.regular (cat A B))
  | .emptyTwice,[A,B,C] => some (.regular (cat (cat A B) C))
  | .once,[A,B,C,E] => some (.once A B C E)
  | .sameValue,[A,B,C,D,E] => some (.sameValue ⟨A,B,C,D,E⟩)
  | .emptyInside,[A,B,C,D,E] => some (.once A (cat B C) D E)
  | .emptyBefore,[A,B,C,D,E] => some (.once (cat A B) C D E)
  | .nested2,[A,B,C,D,F,G,H] => some (.nested2 ⟨A,B,C,D,F,G,H⟩)
  | .nested1,[A,B,C,D,F,G,H] => some (.nested1 ⟨A,B,C,D,F,G,H⟩)
  | .independent,[A,B,C,D,F,G,H] => some (.independent ⟨A,B,C,D,F,G,H⟩)
  | _,_ => none

def code : List Control→List (Word α)→Word (MarkedSymbol α)
  | [],[w] => w.map Sum.inl
  | c::cs,w::ws => w.map Sum.inl++(.inr c::code cs ws)
  | _,_ => []

theorem interleaves_code {cs : List Control} {ws : List (Word α)}
    {z : Word (MarkedSymbol α)} (h : Interleaves cs ws z) : z=code cs ws := by
  induction h with
  | last w => rfl
  | more c w h ih => simp only [code,ih]

theorem interleaves_of_length (cs : List Control) (ws : List (Word α))
    (h : ws.length=cs.length+1) : Interleaves cs ws (code cs ws) := by
  induction cs generalizing ws with
  | nil =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      have he : ws=[] := by simpa using h
      subst ws
      exact .last w
  | cons c cs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      exact .more c w (ih ws (by simpa using h))

def events : List Control→List (Word α)→List (Event α)
  | [],[w] => [.emit w]
  | c::cs,w::ws => .emit w::decodeSymbol (.inr c)::events cs ws
  | _,_ => []

theorem interleaves_execute {cs : List Control} {ws : List (Word α)}
    {z : Word (MarkedSymbol α)} (h : Interleaves cs ws z) (s : State α) :
    State.execute s (z.map decodeSymbol)=State.execute s (events cs ws) := by
  induction h generalizing s with
  | last w =>
    rw [decode_literals,execute_characters]
    rfl
  | @more c w cs ws z h ih =>
    simp only [List.map_append,decode_literals,List.map_cons,State.execute_append,
      execute_characters,Option.bind_some]
    change ((s.appendText w).step (decodeSymbol (.inr c))).bind
      (fun t=>State.execute t (z.map decodeSymbol))=
      ((s.appendText w).step (decodeSymbol (.inr c))).bind
        (fun t=>State.execute t (events cs ws))
    exact congrArg (fun f : State α→Option (State α)=>
      ((s.appendText w).step (decodeSymbol (.inr c))).bind f) (funext ih)

def interpreted (cs : List Control) (ws : List (Word α)) (w : Word α) : Prop :=
  ∃ s,State.execute (State.initial []) (events cs ws)=some s ∧
    s.frames=[] ∧ s.output=w ∧ s.uses≤2

theorem codeMatches_iff {cs : List Control} {ws : List (Word α)}
    {z : Word (MarkedSymbol α)} (h : Interleaves cs ws z) (w : Word α) :
    LiveCompiler.CodeMatches z w 2 ↔ interpreted cs ws w := by
  unfold LiveCompiler.CodeMatches interpreted
  rw [interleaves_execute h]

theorem acceptsFactors_length (ds : List (DFA α)) (ws : List (Word α))
    (h : acceptsFactors ds ws) : ws.length=ds.length := by
  induction ds generalizing ws with
  | nil => cases ws <;> simp_all [acceptsFactors]
  | cons d ds ih =>
    cases ws with
    | nil => exact False.elim h
    | cons w ws => simpa using ih ws h.2

def FactorLanguage (s : Shape) (ds : List (DFA α)) (w : Word α) : Prop :=
  ∃ ws z,Interleaves s.controls ws z ∧ acceptsFactors ds ws ∧
    LiveCompiler.CodeMatches z w 2

theorem factorLanguage_iff (s : Shape) (ds : List (DFA α)) (w : Word α)
    (h : ds.length=s.controls.length+1) :
    FactorLanguage s ds w ↔
      ∃ ws,acceptsFactors ds ws ∧ interpreted s.controls ws w := by
  constructor
  · rintro ⟨ws,z,hi,ha,hc⟩
    exact ⟨ws,ha,(codeMatches_iff hi w).mp hc⟩
  · rintro ⟨ws,ha,hc⟩
    have hi := interleaves_of_length s.controls ws ((acceptsFactors_length ds ws ha).trans h)
    exact ⟨ws,code s.controls ws,hi,ha,(codeMatches_iff hi w).mpr hc⟩

theorem factors_nil (P : List (Word α)→Prop) :
    (∃ ws,acceptsFactors ([] : List (DFA α)) ws ∧ P ws) ↔ P [] := by
  constructor
  · rintro ⟨ws,hw,hP⟩
    cases ws with
    | nil => exact hP
    | cons w ws => exact False.elim hw
  · intro hP
    exact ⟨[],True.intro,hP⟩

theorem factors_cons (d : DFA α) (ds : List (DFA α)) (P : List (Word α)→Prop) :
    (∃ ws,acceptsFactors (d::ds) ws ∧ P ws) ↔
      ∃ w,d.accepts w ∧ ∃ ws,acceptsFactors ds ws ∧ P (w::ws) := by
  constructor
  · rintro ⟨ws,hw,hP⟩
    cases ws with
    | nil => exact False.elim hw
    | cons w ws => exact ⟨w,hw.1,ws,hw.2,hP⟩
  · rintro ⟨w,hw,ws,hws,hP⟩
    exact ⟨w::ws,⟨hw,hws⟩,hP⟩

theorem regular_language (A : DFA α) (w : Word α) :
    FactorLanguage .regular [A] w ↔ A.accepts w := by
  rw [factorLanguage_iff _ _ _ (by rfl)]
  simp only [factors_cons,factors_nil]
  simp [interpreted,Shape.controls,events,State.execute,State.step,
    State.initial,State.appendText]

theorem once_language (A B C E : DFA α) (w : Word α) :
    FactorLanguage .once [A,B,C,E] w ↔
      ∃ a b c e,A.accepts a ∧ B.accepts b ∧ C.accepts c ∧ E.accepts e ∧
        w=a++b++c++b++e := by
  rw [factorLanguage_iff _ _ _ (by rfl)]
  simp only [factors_cons,factors_nil]
  simp only [interpreted,Shape.controls,events,decodeSymbol,State.execute,State.step,
    State.initial,State.appendText,List.map_nil,List.map_cons,List.append_nil,
    List.nil_append,Option.bind,Option.some.injEq,exists_eq_left,
    and_true,Nat.reduceLeDiff,List.append_assoc]
  simp only [exists_eq_left',true_and,and_true,Nat.zero_add,Nat.reduceLeDiff]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,e,he,hw⟩
    exact ⟨a,b,c,e,ha,hb,hc,he,hw.symm⟩
  · rintro ⟨a,b,c,e,ha,hb,hc,he,hw⟩
    exact ⟨a,ha,b,hb,c,hc,e,he,hw.symm⟩


theorem emptyOnce_language (A B : DFA α) (w : Word α) :
    FactorLanguage .emptyOnce [A,B] w ↔
      ∃ a b,A.accepts a ∧ B.accepts b ∧
        w=a++b := by
  rw [factorLanguage_iff _ _ _ (by rfl)]
  simp only [factors_cons,factors_nil]
  simp only [interpreted,Shape.controls,events,decodeSymbol,State.execute,State.step,
    State.initial,State.appendText,List.map_nil,List.map_cons,List.append_nil,
    List.nil_append,Option.bind,Option.some.injEq,exists_eq_left,
    and_true,Nat.reduceLeDiff,List.append_assoc]
  simp only [exists_eq_left',true_and,and_true,Nat.zero_add,Nat.reduceLeDiff]
  constructor
  · rintro ⟨a,ha,b,hb,hw⟩
    exact ⟨a,b,ha,hb,hw.symm⟩
  · rintro ⟨a,b,ha,hb,hw⟩
    exact ⟨a,ha,b,hb,hw.symm⟩

theorem emptyTwice_language (A B C : DFA α) (w : Word α) :
    FactorLanguage .emptyTwice [A,B,C] w ↔
      ∃ a b c,A.accepts a ∧ B.accepts b ∧ C.accepts c ∧
        w=a++b++c := by
  rw [factorLanguage_iff _ _ _ (by rfl)]
  simp only [factors_cons,factors_nil]
  simp only [interpreted,Shape.controls,events,decodeSymbol,State.execute,State.step,
    State.initial,State.appendText,List.map_nil,List.map_cons,List.append_nil,
    List.nil_append,Option.bind,Option.some.injEq,exists_eq_left,
    and_true,Nat.reduceLeDiff,List.append_assoc]
  simp only [exists_eq_left',true_and,and_true,Nat.zero_add,Nat.reduceLeDiff]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,hw⟩
    exact ⟨a,b,c,ha,hb,hc,hw.symm⟩
  · rintro ⟨a,b,c,ha,hb,hc,hw⟩
    exact ⟨a,ha,b,hb,c,hc,hw.symm⟩

theorem sameValue_language (A B C D E : DFA α) (w : Word α) :
    FactorLanguage .sameValue [A,B,C,D,E] w ↔
      ∃ a b c d e,A.accepts a ∧ B.accepts b ∧ C.accepts c ∧ D.accepts d ∧ E.accepts e ∧
        w=a++b++c++b++d++b++e := by
  rw [factorLanguage_iff _ _ _ (by rfl)]
  simp only [factors_cons,factors_nil]
  simp only [interpreted,Shape.controls,events,decodeSymbol,State.execute,State.step,
    State.initial,State.appendText,List.map_nil,List.map_cons,List.append_nil,
    List.nil_append,Option.bind,Option.some.injEq,exists_eq_left,
    and_true,Nat.reduceLeDiff,List.append_assoc]
  simp only [exists_eq_left',true_and,and_true,Nat.zero_add,Nat.reduceLeDiff]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,e,he,hw⟩
    exact ⟨a,b,c,d,e,ha,hb,hc,hd,he,hw.symm⟩
  · rintro ⟨a,b,c,d,e,ha,hb,hc,hd,he,hw⟩
    exact ⟨a,ha,b,hb,c,hc,d,hd,e,he,hw.symm⟩

theorem emptyInside_language (A B C D E : DFA α) (w : Word α) :
    FactorLanguage .emptyInside [A,B,C,D,E] w ↔
      ∃ a b c d e,A.accepts a ∧ B.accepts b ∧ C.accepts c ∧ D.accepts d ∧ E.accepts e ∧
        w=a++(b++c)++d++(b++c)++e := by
  rw [factorLanguage_iff _ _ _ (by rfl)]
  simp only [factors_cons,factors_nil]
  simp only [interpreted,Shape.controls,events,decodeSymbol,State.execute,State.step,
    State.initial,State.appendText,List.map_nil,List.map_cons,List.append_nil,
    List.nil_append,Option.bind,Option.some.injEq,exists_eq_left,
    and_true,Nat.reduceLeDiff,List.append_assoc]
  simp only [exists_eq_left',true_and,and_true,Nat.zero_add,Nat.reduceLeDiff]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,e,he,hw⟩
    exact ⟨a,b,c,d,e,ha,hb,hc,hd,he,hw.symm⟩
  · rintro ⟨a,b,c,d,e,ha,hb,hc,hd,he,hw⟩
    exact ⟨a,ha,b,hb,c,hc,d,hd,e,he,hw.symm⟩

theorem emptyBefore_language (A B C D E : DFA α) (w : Word α) :
    FactorLanguage .emptyBefore [A,B,C,D,E] w ↔
      ∃ a b c d e,A.accepts a ∧ B.accepts b ∧ C.accepts c ∧ D.accepts d ∧ E.accepts e ∧
        w=(a++b)++c++d++c++e := by
  rw [factorLanguage_iff _ _ _ (by rfl)]
  simp only [factors_cons,factors_nil]
  simp only [interpreted,Shape.controls,events,decodeSymbol,State.execute,State.step,
    State.initial,State.appendText,List.map_nil,List.map_cons,List.append_nil,
    List.nil_append,Option.bind,Option.some.injEq,exists_eq_left,
    and_true,Nat.reduceLeDiff,List.append_assoc]
  simp only [exists_eq_left',true_and,and_true,Nat.zero_add,Nat.reduceLeDiff]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,e,he,hw⟩
    exact ⟨a,b,c,d,e,ha,hb,hc,hd,he,hw.symm⟩
  · rintro ⟨a,b,c,d,e,ha,hb,hc,hd,he,hw⟩
    exact ⟨a,ha,b,hb,c,hc,d,hd,e,he,hw.symm⟩

theorem nested2_language (A B C D F G H : DFA α) (w : Word α) :
    FactorLanguage .nested2 [A,B,C,D,F,G,H] w ↔
      ∃ a b c d f g h,A.accepts a ∧ B.accepts b ∧ C.accepts c ∧ D.accepts d ∧ F.accepts f ∧ G.accepts g ∧ H.accepts h ∧
        w=a++(b++c++d++c++f)++g++(b++c++d++c++f)++h := by
  rw [factorLanguage_iff _ _ _ (by rfl)]
  simp only [factors_cons,factors_nil]
  simp only [interpreted,Shape.controls,events,decodeSymbol,State.execute,State.step,
    State.initial,State.appendText,List.map_nil,List.map_cons,List.append_nil,
    List.nil_append,Option.bind,Option.some.injEq,exists_eq_left,
    and_true,Nat.reduceLeDiff,List.append_assoc]
  simp only [exists_eq_left',true_and,and_true,Nat.zero_add,Nat.reduceLeDiff]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,f,hf,g,hg,h,hh,hw⟩
    exact ⟨a,b,c,d,f,g,h,ha,hb,hc,hd,hf,hg,hh,hw.symm⟩
  · rintro ⟨a,b,c,d,f,g,h,ha,hb,hc,hd,hf,hg,hh,hw⟩
    exact ⟨a,ha,b,hb,c,hc,d,hd,f,hf,g,hg,h,hh,hw.symm⟩

theorem nested1_language (A B C D F G H : DFA α) (w : Word α) :
    FactorLanguage .nested1 [A,B,C,D,F,G,H] w ↔
      ∃ a b c d f g h,A.accepts a ∧ B.accepts b ∧ C.accepts c ∧ D.accepts d ∧ F.accepts f ∧ G.accepts g ∧ H.accepts h ∧
        w=a++b++c++(d++b++f)++g++(d++b++f)++h := by
  rw [factorLanguage_iff _ _ _ (by rfl)]
  simp only [factors_cons,factors_nil]
  simp only [interpreted,Shape.controls,events,decodeSymbol,State.execute,State.step,
    State.initial,State.appendText,List.map_nil,List.map_cons,List.append_nil,
    List.nil_append,Option.bind,Option.some.injEq,exists_eq_left,
    and_true,Nat.reduceLeDiff,List.append_assoc]
  simp only [exists_eq_left',true_and,and_true,Nat.zero_add,Nat.reduceLeDiff]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,f,hf,g,hg,h,hh,hw⟩
    exact ⟨a,b,c,d,f,g,h,ha,hb,hc,hd,hf,hg,hh,hw.symm⟩
  · rintro ⟨a,b,c,d,f,g,h,ha,hb,hc,hd,hf,hg,hh,hw⟩
    exact ⟨a,ha,b,hb,c,hc,d,hd,f,hf,g,hg,h,hh,hw.symm⟩

theorem independent_language (A B C D F G H : DFA α) (w : Word α) :
    FactorLanguage .independent [A,B,C,D,F,G,H] w ↔
      ∃ a b c d f g h,A.accepts a ∧ B.accepts b ∧ C.accepts c ∧ D.accepts d ∧ F.accepts f ∧ G.accepts g ∧ H.accepts h ∧
        w=a++b++c++b++d++f++g++f++h := by
  rw [factorLanguage_iff _ _ _ (by rfl)]
  simp only [factors_cons,factors_nil]
  simp only [interpreted,Shape.controls,events,decodeSymbol,State.execute,State.step,
    State.initial,State.appendText,List.map_nil,List.map_cons,List.append_nil,
    List.nil_append,Option.bind,Option.some.injEq,exists_eq_left,
    and_true,Nat.reduceLeDiff,List.append_assoc]
  simp only [exists_eq_left',true_and,and_true,Nat.zero_add,Nat.reduceLeDiff]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,d,hd,f,hf,g,hg,h,hh,hw⟩
    exact ⟨a,b,c,d,f,g,h,ha,hb,hc,hd,hf,hg,hh,hw.symm⟩
  · rintro ⟨a,b,c,d,f,g,h,ha,hb,hc,hd,hf,hg,hh,hw⟩
    exact ⟨a,ha,b,hb,c,hc,d,hd,f,hf,g,hg,h,hh,hw.symm⟩

theorem regular_assembly (A : DFA α) (w : Word α) :
    MatchesWithin (Form.regular A).expr w 2 ↔ FactorLanguage .regular [A] w := by
  rw [Form.expr,atom_matches,regular_language]

theorem emptyOnce_assembly (A B : DFA α) (w : Word α) :
    MatchesWithin (Form.regular (cat A B)).expr w 2 ↔
      FactorLanguage .emptyOnce [A,B] w := by
  rw [Form.expr,atom_matches,cat_accepts,emptyOnce_language]
  constructor
  · rintro ⟨a,b,hw,ha,hb⟩
    exact ⟨a,b,ha,hb,hw⟩
  · rintro ⟨a,b,ha,hb,hw⟩
    exact ⟨a,b,hw,ha,hb⟩

theorem emptyTwice_assembly (A B C : DFA α) (w : Word α) :
    MatchesWithin (Form.regular (cat (cat A B) C)).expr w 2 ↔
      FactorLanguage .emptyTwice [A,B,C] w := by
  rw [Form.expr,atom_matches,emptyTwice_language]
  simp only [cat_accepts]
  constructor
  · rintro ⟨u,c,hw,⟨a,b,rfl,ha,hb⟩,hc⟩
    exact ⟨a,b,c,ha,hb,hc,hw⟩
  · rintro ⟨a,b,c,ha,hb,hc,hw⟩
    exact ⟨a++b,c,hw,⟨a,b,rfl,ha,hb⟩,hc⟩

theorem once_assembly (A B C E : DFA α) (w : Word α) :
    MatchesWithin (Form.once A B C E).expr w 2 ↔ FactorLanguage .once [A,B,C,E] w := by
  rw [Form.expr,once_matches,once_language]

theorem sameValue_assembly (A B C D E : DFA α) (w : Word α) :
    MatchesWithin (Form.sameValue ⟨A,B,C,D,E⟩).expr w 2 ↔
      FactorLanguage .sameValue [A,B,C,D,E] w := by
  rw [Form.expr,Witness.same_iff,sameValue_language]

theorem emptyInside_assembly (A B C D E : DFA α) (w : Word α) :
    MatchesWithin (Form.once A (cat B C) D E).expr w 2 ↔
      FactorLanguage .emptyInside [A,B,C,D,E] w := by
  rw [Form.expr,once_matches,emptyInside_language]
  simp only [cat_accepts]
  constructor
  · rintro ⟨a,u,d,e,ha,⟨b,c,rfl,hb,hc⟩,hd,he,hw⟩
    exact ⟨a,b,c,d,e,ha,hb,hc,hd,he,hw⟩
  · rintro ⟨a,b,c,d,e,ha,hb,hc,hd,he,hw⟩
    exact ⟨a,b++c,d,e,ha,⟨b,c,rfl,hb,hc⟩,hd,he,hw⟩

theorem emptyBefore_assembly (A B C D E : DFA α) (w : Word α) :
    MatchesWithin (Form.once (cat A B) C D E).expr w 2 ↔
      FactorLanguage .emptyBefore [A,B,C,D,E] w := by
  rw [Form.expr,once_matches,emptyBefore_language]
  simp only [cat_accepts]
  constructor
  · rintro ⟨u,c,d,e,⟨a,b,rfl,ha,hb⟩,hc,hd,he,hw⟩
    exact ⟨a,b,c,d,e,ha,hb,hc,hd,he,hw⟩
  · rintro ⟨a,b,c,d,e,ha,hb,hc,hd,he,hw⟩
    exact ⟨a++b,c,d,e,⟨a,b,rfl,ha,hb⟩,hc,hd,he,hw⟩

theorem nested2_assembly (A B C D F G H : DFA α) (w : Word α) :
    MatchesWithin (Form.nested2 ⟨A,B,C,D,F,G,H⟩).expr w 2 ↔
      FactorLanguage .nested2 [A,B,C,D,F,G,H] w := by
  rw [Form.expr,Witness.nested2_iff,nested2_language]

theorem nested1_assembly (A B C D F G H : DFA α) (w : Word α) :
    MatchesWithin (Form.nested1 ⟨A,B,C,D,F,G,H⟩).expr w 2 ↔
      FactorLanguage .nested1 [A,B,C,D,F,G,H] w := by
  rw [Form.expr,Witness.nested1_iff,nested1_language]

theorem independent_assembly (A B C D F G H : DFA α) (w : Word α) :
    MatchesWithin (Form.independent ⟨A,B,C,D,F,G,H⟩).expr w 2 ↔
      FactorLanguage .independent [A,B,C,D,F,G,H] w := by
  rw [Form.expr,Witness.independent_iff,independent_language]

private theorem length_cons {X : Type} (xs : List X) (n : Nat)
    (h : xs.length=n+1) : ∃ x ys,xs=x::ys ∧ ys.length=n := by
  cases xs with
  | nil => simp at h
  | cons x xs => exact ⟨x,xs,rfl,by simpa using h⟩


private theorem slots2 {X : Type} (xs : List X) (h : xs.length=2) :
    ∃ a b,xs=[a,b] := by
  obtain ⟨a,tail0,rfl,h0⟩ := length_cons xs 1 h
  obtain ⟨b,rfl⟩ := List.length_eq_one_iff.mp h0
  exact ⟨a,b,rfl⟩

private theorem slots3 {X : Type} (xs : List X) (h : xs.length=3) :
    ∃ a b c,xs=[a,b,c] := by
  obtain ⟨a,tail0,rfl,h0⟩ := length_cons xs 2 h
  obtain ⟨b,tail1,rfl,h1⟩ := length_cons tail0 1 h0
  obtain ⟨c,rfl⟩ := List.length_eq_one_iff.mp h1
  exact ⟨a,b,c,rfl⟩

private theorem slots4 {X : Type} (xs : List X) (h : xs.length=4) :
    ∃ a b c d,xs=[a,b,c,d] := by
  obtain ⟨a,tail0,rfl,h0⟩ := length_cons xs 3 h
  obtain ⟨b,tail1,rfl,h1⟩ := length_cons tail0 2 h0
  obtain ⟨c,tail2,rfl,h2⟩ := length_cons tail1 1 h1
  obtain ⟨d,rfl⟩ := List.length_eq_one_iff.mp h2
  exact ⟨a,b,c,d,rfl⟩

private theorem slots5 {X : Type} (xs : List X) (h : xs.length=5) :
    ∃ a b c d e,xs=[a,b,c,d,e] := by
  obtain ⟨a,tail0,rfl,h0⟩ := length_cons xs 4 h
  obtain ⟨b,tail1,rfl,h1⟩ := length_cons tail0 3 h0
  obtain ⟨c,tail2,rfl,h2⟩ := length_cons tail1 2 h1
  obtain ⟨d,tail3,rfl,h3⟩ := length_cons tail2 1 h2
  obtain ⟨e,rfl⟩ := List.length_eq_one_iff.mp h3
  exact ⟨a,b,c,d,e,rfl⟩

private theorem slots7 {X : Type} (xs : List X) (h : xs.length=7) :
    ∃ a b c d e f g,xs=[a,b,c,d,e,f,g] := by
  obtain ⟨a,tail0,rfl,h0⟩ := length_cons xs 6 h
  obtain ⟨b,tail1,rfl,h1⟩ := length_cons tail0 5 h0
  obtain ⟨c,tail2,rfl,h2⟩ := length_cons tail1 4 h1
  obtain ⟨d,tail3,rfl,h3⟩ := length_cons tail2 3 h2
  obtain ⟨e,tail4,rfl,h4⟩ := length_cons tail3 2 h3
  obtain ⟨f,tail5,rfl,h5⟩ := length_cons tail4 1 h4
  obtain ⟨g,rfl⟩ := List.length_eq_one_iff.mp h5
  exact ⟨a,b,c,d,e,f,g,rfl⟩

/-- Every actual fixed-marker factor family compiles to one of the six
    concrete form constructors, with an exact language equivalence. -/
theorem assemble_spec (s : Shape) (ds : List (DFA α))
    (h : ds.length=s.controls.length+1) :
    ∃ F : Form α,assemble s ds=some F ∧
      ∀ w,MatchesWithin F.expr w 2 ↔ FactorLanguage s ds w := by
  cases s with
  | regular =>
    obtain ⟨A,rfl⟩ := List.length_eq_one_iff.mp h
    exact ⟨Form.regular A,rfl,regular_assembly A⟩
  | emptyOnce =>
    obtain ⟨A,B,rfl⟩ := slots2 ds h
    exact ⟨Form.regular (cat A B),rfl,emptyOnce_assembly A B⟩
  | emptyTwice =>
    obtain ⟨A,B,C,rfl⟩ := slots3 ds h
    exact ⟨Form.regular (cat (cat A B) C),rfl,emptyTwice_assembly A B C⟩
  | once =>
    obtain ⟨A,B,C,E,rfl⟩ := slots4 ds h
    exact ⟨Form.once A B C E,rfl,once_assembly A B C E⟩
  | sameValue =>
    obtain ⟨A,B,C,D,E,rfl⟩ := slots5 ds h
    exact ⟨Form.sameValue ⟨A,B,C,D,E⟩,rfl,sameValue_assembly A B C D E⟩
  | emptyInside =>
    obtain ⟨A,B,C,D,E,rfl⟩ := slots5 ds h
    exact ⟨Form.once A (cat B C) D E,rfl,emptyInside_assembly A B C D E⟩
  | emptyBefore =>
    obtain ⟨A,B,C,D,E,rfl⟩ := slots5 ds h
    exact ⟨Form.once (cat A B) C D E,rfl,emptyBefore_assembly A B C D E⟩
  | nested2 =>
    obtain ⟨A,B,C,D,F,G,H,rfl⟩ := slots7 ds h
    exact ⟨Form.nested2 ⟨A,B,C,D,F,G,H⟩,rfl,nested2_assembly A B C D F G H⟩
  | nested1 =>
    obtain ⟨A,B,C,D,F,G,H,rfl⟩ := slots7 ds h
    exact ⟨Form.nested1 ⟨A,B,C,D,F,G,H⟩,rfl,nested1_assembly A B C D F G H⟩
  | independent =>
    obtain ⟨A,B,C,D,F,G,H,rfl⟩ := slots7 ds h
    exact ⟨Form.independent ⟨A,B,C,D,F,G,H⟩,rfl,independent_assembly A B C D F G H⟩

/-- Pattern-only preprocessing: compile the marked regular language,
    enumerate the ten control shapes and their boundary-state factors,
    and assemble genuine concrete normal-form expressions. -/
def forms (p : Expr α) : List (Form α) :=
  allShapes.flatMap fun s=>
    (families (RegularDFA.sourceDFA p) (RegularDFA.sourceDFA p).initial s.controls).filterMap
      (assemble s)

theorem forms_correct (p : Expr α) (w : Word α) :
    MatchesWithin p w 2 ↔ ∃ F∈forms p,MatchesWithin F.expr w 2 := by
  rw [RegularDFA.source_factorization]
  change (∃ s : Shape,∃ ds∈families (RegularDFA.sourceDFA p)
    (RegularDFA.sourceDFA p).initial s.controls,FactorLanguage s ds w) ↔ _
  constructor
  · rintro ⟨s,ds,hds,hw⟩
    obtain ⟨F,hF,hcorrect⟩ := assemble_spec s ds
      (family_length _ _ s.controls ds hds)
    refine ⟨F,?_,(hcorrect w).mpr hw⟩
    exact List.mem_flatMap.mpr ⟨s,allShapes_complete s,
      List.mem_filterMap.mpr ⟨ds,hds,hF⟩⟩
  · rintro ⟨F,hF,hw⟩
    obtain ⟨s,_,hs⟩ := List.mem_flatMap.mp hF
    obtain ⟨ds,hds,hA⟩ := List.mem_filterMap.mp hs
    obtain ⟨G,hG,hcorrect⟩ := assemble_spec s ds
      (family_length _ _ s.controls ds hds)
    have he : G=F := Option.some.inj (hG.symm.trans hA)
    subst G
    exact ⟨s,ds,hds,(hcorrect w).mp hw⟩

def pieces (p : Expr α) : List (Expr α) := (forms p).map Form.expr

/-- The original normalization contract, now discharged constructively
    for every source expression under the at-most-two-use semantics. -/
theorem normalization (p : Expr α) : Spec.IsNormalization p (pieces p) := by
  intro w
  rw [forms_correct]
  constructor
  · rintro ⟨F,hF,hw⟩
    exact ⟨F.expr,List.mem_map.mpr ⟨F,hF,rfl⟩,hw⟩
  · rintro ⟨q,hq,hw⟩
    obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hq
    exact ⟨F,hF,hw⟩

def IsNormal (q : Expr α) : Prop :=
  (∃ A,q=.atom A) ∨
  (∃ A B C E,q=once A B C E) ∨
  (∃ P : FiveDFA α,q=P.sameValue) ∨
  (∃ P : SevenDFA α,q=P.independent) ∨
  (∃ P : SevenDFA α,q=P.nested1) ∨
  (∃ P : SevenDFA α,q=P.nested2)

theorem form_normal (F : Form α) : IsNormal F.expr := by
  cases F with
  | regular A => exact Or.inl ⟨A,rfl⟩
  | once A B C E => exact Or.inr (Or.inl ⟨A,B,C,E,rfl⟩)
  | sameValue P => exact Or.inr (Or.inr (Or.inl ⟨P,rfl⟩))
  | independent P => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨P,rfl⟩)))
  | nested1 P => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨P,rfl⟩))))
  | nested2 P => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨P,rfl⟩))))

theorem pieces_normal (p : Expr α) (q : Expr α) (h : q∈pieces p) : IsNormal q := by
  obtain ⟨F,_,rfl⟩ := List.mem_map.mp h
  exact form_normal F

end REWB.CompleteNormalization
