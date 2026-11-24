import REWB.NormalForms

/-! Executable reference decisions for the four concrete forms.
    These enumerate splits, not the proposed fast algorithm. -/
namespace REWB.Reference

variable {α β : Type}

def splitAny : List β → (List β → List β → Bool) → Bool
  | [], f => f [] []
  | c :: cs, f => f [] (c :: cs) || splitAny cs (fun l r => f (c :: l) r)

theorem splitAny_iff (w : List β) (f : List β → List β → Bool) :
    splitAny w f = true ↔ ∃ l r, w = l ++ r ∧ f l r = true := by
  induction w generalizing f with
  | nil =>
    constructor
    · intro h
      exact ⟨[], [], rfl, h⟩
    · rintro ⟨l, r, he, hf⟩
      cases l <;> cases r <;> simp_all [splitAny]
  | cons c cs ih =>
    simp only [splitAny, Bool.or_eq_true, ih]
    constructor
    · intro h
      rcases h with hf | ⟨l,r,he,hf⟩
      · exact ⟨[], c :: cs, rfl, hf⟩
      · exact ⟨c :: l, r, congrArg (List.cons c) he, hf⟩
    · rintro ⟨l,r,he,hf⟩
      cases l with
      | nil =>
        have h : c :: cs = r := he
        subst r
        exact Or.inl hf
      | cons x xs =>
        have h : c = x ∧ cs = xs ++ r := by simpa using he
        rcases h with ⟨rfl,h⟩
        exact Or.inr ⟨xs,r,h,hf⟩

def acceptB (d : DFA α) (w : Word α) : Bool :=
  d.final (d.run d.initial w)

theorem acceptB_iff (d : DFA α) (w : Word α) :
    acceptB d w = true ↔ d.accepts w := Iff.rfl

def choose (d : DFA α) (w : Word α)
    (k : Word α → Word α → Bool) : Bool :=
  splitAny w (fun x r => acceptB d x && k x r)

theorem choose_iff (d : DFA α) (w : Word α) (k : Word α → Word α → Bool) :
    choose d w k = true ↔
      ∃ x r, w = x ++ r ∧ d.accepts x ∧ k x r = true := by
  simp only [choose, splitAny_iff, Bool.and_eq_true, acceptB_iff]

def consume (d : DFA α) (w : Word α) (k : Word α → Bool) : Bool :=
  choose d w (fun _ r => k r)

theorem consume_iff (d : DFA α) (w : Word α) (k : Word α → Bool) :
    consume d w k = true ↔
      ∃ x r, w = x ++ r ∧ d.accepts x ∧ k r = true := by
  simp only [consume, choose_iff]

def copy [DecidableEq α] (u w : Word α) (k : Word α → Bool) : Bool :=
  splitAny w (fun v r => decide (v = u) && k r)

theorem copy_iff [DecidableEq α] (u w : Word α) (k : Word α → Bool) :
    copy u w k = true ↔ ∃ r, w = u ++ r ∧ k r = true := by
  simp only [copy, splitAny_iff, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨v,r,hw,rfl,hk⟩
    exact ⟨r,hw,hk⟩
  · rintro ⟨r,hw,hk⟩
    exact ⟨u,r,hw,rfl,hk⟩

def same [DecidableEq α] (p : FiveDFA α) (w : Word α) : Bool :=
  consume p.A w fun r0 =>
  choose p.B r0 fun u r1 =>
  consume p.C r1 fun r2 =>
  copy u r2 fun r3 =>
  consume p.D r3 fun r4 =>
  copy u r4 (acceptB p.E)

theorem same_correct [DecidableEq α] (p : FiveDFA α) (w : Word α) :
    same p w = true ↔ MatchesWithin p.sameValue w 2 := by
  rw [Witness.same_iff]
  simp only [same, consume_iff, choose_iff, copy_iff, acceptB_iff, List.append_assoc]
  constructor
  · rintro ⟨a,r0,h0,ha,u,r1,h1,hu,c,r2,h2,hc,r3,h3,d,r4,h4,hd,e,h5,he⟩
    exact ⟨a,u,c,d,e,ha,hu,hc,hd,he,by rw [h0,h1,h2,h3,h4,h5]⟩
  · rintro ⟨a,u,c,d,e,ha,hu,hc,hd,he,rfl⟩
    exact ⟨a,_,rfl,ha,u,_,rfl,hu,c,_,rfl,hc,_,rfl,d,_,rfl,hd,e,rfl,he⟩

def independent [DecidableEq α] (p : SevenDFA α) (w : Word α) : Bool :=
  consume p.A w fun r0 =>
  choose p.B r0 fun u r1 =>
  consume p.C r1 fun r2 =>
  copy u r2 fun r3 =>
  consume p.D r3 fun r4 =>
  choose p.F r4 fun v r5 =>
  consume p.G r5 fun r6 =>
  copy v r6 (acceptB p.H)

theorem independent_correct [DecidableEq α] (p : SevenDFA α) (w : Word α) :
    independent p w = true ↔ MatchesWithin p.independent w 2 := by
  rw [Witness.independent_iff]
  simp only [independent, consume_iff, choose_iff, copy_iff, acceptB_iff, List.append_assoc]
  constructor
  · rintro ⟨a,r0,h0,ha,u,r1,h1,hu,c,r2,h2,hc,r3,h3,d,r4,h4,hd,
      v,r5,h5,hv,g,r6,h6,hg,h,h7,hh⟩
    exact ⟨a,u,c,d,v,g,h,ha,hu,hc,hd,hv,hg,hh,
      by rw [h0,h1,h2,h3,h4,h5,h6,h7]⟩
  · rintro ⟨a,u,c,d,v,g,h,ha,hu,hc,hd,hv,hg,hh,rfl⟩
    exact ⟨a,_,rfl,ha,u,_,rfl,hu,c,_,rfl,hc,_,rfl,d,_,rfl,hd,
      v,_,rfl,hv,g,_,rfl,hg,h,rfl,hh⟩

def nested1 [DecidableEq α] (p : SevenDFA α) (w : Word α) : Bool :=
  consume p.A w fun r0 =>
  choose p.B r0 fun u r1 =>
  consume p.C r1 fun r2 =>
  splitAny r2 fun v r3 =>
    (consume p.D v fun r4 => copy u r4 (acceptB p.F)) &&
    (consume p.G r3 fun r5 => copy v r5 (acceptB p.H))

theorem nested1_correct [DecidableEq α] (p : SevenDFA α) (w : Word α) :
    nested1 p w = true ↔ MatchesWithin p.nested1 w 2 := by
  rw [Witness.nested1_iff]
  simp only [nested1, consume_iff, choose_iff, splitAny_iff,
    Bool.and_eq_true, copy_iff, acceptB_iff]
  constructor
  · rintro ⟨a,r0,h0,ha,u,r1,h1,hu,c,r2,h2,hc,v,r3,h3,
      ⟨d,r4,h4,hd,f,h5,hf⟩,g,r5,h6,hg,h,h7,hh⟩
    refine ⟨a,u,c,d,f,g,h,ha,hu,hc,hd,hf,hg,hh,?_⟩
    rw [h0,h1,h2,h3,h6,h7,h4,h5] <;> simp only [List.append_assoc]
  · rintro ⟨a,u,c,d,f,g,h,ha,hu,hc,hd,hf,hg,hh,rfl⟩
    let v := d ++ u ++ f
    refine ⟨a,u ++ (c ++ (v ++ (g ++ (v ++ h)))),?_,ha,
      u,c ++ (v ++ (g ++ (v ++ h))),rfl,hu,
      c,v ++ (g ++ (v ++ h)),rfl,hc,
      v,g ++ (v ++ h),rfl,
      ⟨d,u ++ f,?_,hd,f,rfl,hf⟩,g,v ++ h,rfl,hg,h,rfl,hh⟩
    all_goals simp only [v, List.append_assoc]

def nested2 [DecidableEq α] (p : SevenDFA α) (w : Word α) : Bool :=
  consume p.A w fun r0 =>
  splitAny r0 fun v r1 =>
    (consume p.B v fun r2 =>
     choose p.C r2 fun u r3 =>
     consume p.D r3 fun r4 => copy u r4 (acceptB p.F)) &&
    (consume p.G r1 fun r5 => copy v r5 (acceptB p.H))

theorem nested2_correct [DecidableEq α] (p : SevenDFA α) (w : Word α) :
    nested2 p w = true ↔ MatchesWithin p.nested2 w 2 := by
  rw [Witness.nested2_iff]
  simp only [nested2, consume_iff, choose_iff, splitAny_iff,
    Bool.and_eq_true, copy_iff, acceptB_iff]
  constructor
  · rintro ⟨a,r0,h0,ha,v,r1,h1,
      ⟨b,r2,h2,hb,u,r3,h3,hu,d,r4,h4,hd,f,h5,hf⟩,g,r5,h6,hg,h,h7,hh⟩
    refine ⟨a,b,u,d,f,g,h,ha,hb,hu,hd,hf,hg,hh,?_⟩
    rw [h0,h1,h6,h7,h2,h3,h4,h5] <;> simp only [List.append_assoc]
  · rintro ⟨a,b,u,d,f,g,h,ha,hb,hu,hd,hf,hg,hh,rfl⟩
    let v := b ++ u ++ d ++ u ++ f
    refine ⟨a,v ++ (g ++ (v ++ h)),?_,ha,v,g ++ (v ++ h),rfl,
      ⟨b,u ++ (d ++ (u ++ f)),?_,hb,u,d ++ (u ++ f),rfl,hu,
        d,u ++ f,rfl,hd,f,rfl,hf⟩,
      g,v ++ h,rfl,hg,h,rfl,hh⟩
    all_goals simp only [v, List.append_assoc]

end REWB.Reference
