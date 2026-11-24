import REWB.NormalForms

/-! Algebraic reductions independent of any fast suffix-tree data structure. -/
namespace REWB
variable {α : Type}

/-- Exact splitting of the outer context across two identical, disjoint
    regions. G sees y ++ middle ++ x; H sees y ++ suffix. -/
def boundaryLeft (g : DFA α) (q : Fin g.stateCount)
    (middle x : Word α) : Prop :=
  g.final (g.run (g.run q middle) x) = true

def boundaryRight (g h : DFA α) (q : Fin g.stateCount)
    (suffix y : Word α) : Prop :=
  g.run g.initial y = q ∧ h.accepts (y ++ suffix)

theorem outer_context_split (g h : DFA α) (middle suffix x y : Word α) :
    (g.accepts (y ++ middle ++ x) ∧ h.accepts (y ++ suffix)) ↔
      ∃ q : Fin g.stateCount,
        boundaryLeft g q middle x ∧ boundaryRight g h q suffix y := by
  constructor
  · intro hh
    rcases hh with ⟨hg, hh⟩
    refine ⟨g.run g.initial y, ?_, rfl, hh⟩
    simpa [boundaryLeft, DFA.accepts, DFA.run_append_three] using hg
  · intro hh
    rcases hh with ⟨q, hg, heq, hh⟩
    subst q
    exact ⟨by simpa [boundaryLeft, DFA.accepts, DFA.run_append_three] using hg, hh⟩

/-- Fixed region X has the shape x ++ d ++ u ++ f ++ y. The first inner
    occurrence can precede or cross the beginning of X.  This witness
    deliberately retains the entire pre equality. -/
def RegionP1 (p : SevenDFA α) (pre region middle suffix : Word α) : Prop :=
  ∃ a u c x d f y : Word α,
    pre ++ x = a ++ u ++ c ∧ region = x ++ d ++ u ++ f ++ y ∧
    p.A.accepts a ∧ p.B.accepts u ∧ p.C.accepts c ∧
    p.D.accepts d ∧ p.F.accepts f ∧ p.G.accepts (y ++ middle ++ x) ∧
    p.H.accepts (y ++ suffix)

def BoundaryP1 (p : SevenDFA α) (pre region middle suffix : Word α)
    (q : Fin p.G.stateCount) : Prop :=
  ∃ a u c x d f y : Word α,
    pre ++ x = a ++ u ++ c ∧ region = x ++ d ++ u ++ f ++ y ∧
    p.A.accepts a ∧ p.B.accepts u ∧ p.C.accepts c ∧
    p.D.accepts d ∧ p.F.accepts f ∧
    boundaryLeft p.G q middle x ∧ boundaryRight p.G p.H q suffix y

theorem regionP1_iff_boundary (p : SevenDFA α) (pre region middle suffix : Word α) :
    RegionP1 p pre region middle suffix ↔
      ∃ q, BoundaryP1 p pre region middle suffix q := by
  constructor
  · intro hw
    rcases hw with ⟨a,u,c,x,d,f,y,hpre,hreg,ha,hu,hc,hd,hf,hg,hh⟩
    rcases (outer_context_split p.G p.H middle suffix x y).mp ⟨hg,hh⟩ with ⟨q,hl,hr⟩
    exact ⟨q,a,u,c,x,d,f,y,hpre,hreg,ha,hu,hc,hd,hf,hl,hr⟩
  · intro hw
    rcases hw with ⟨q,a,u,c,x,d,f,y,hpre,hreg,ha,hu,hc,hd,hf,hl,hr⟩
    rcases (outer_context_split p.G p.H middle suffix x y).mpr ⟨q,hl,hr⟩ with ⟨hg,hh⟩
    exact ⟨a,u,c,x,d,f,y,hpre,hreg,ha,hu,hc,hd,hf,hg,hh⟩

theorem regionP1_sound (p : SevenDFA α) (pre region middle suffix : Word α)
    (h : RegionP1 p pre region middle suffix) :
    MatchesWithin p.nested1 (pre ++ region ++ middle ++ region ++ suffix) 2 := by
  rcases h with ⟨a,u,c,x,d,f,y,hpre,hreg,ha,hu,hc,hd,hf,hg,hh⟩
  apply (Witness.nested1_iff p _).mpr
  refine ⟨a,u,c,d,f,y ++ middle ++ x,y ++ suffix,ha,hu,hc,hd,hf,hg,hh,?_⟩
  calc
    pre ++ region ++ middle ++ region ++ suffix =
        (pre ++ x) ++ d ++ u ++ f ++ y ++ middle ++ x ++ d ++ u ++ f ++ y ++ suffix := by
      rw [hreg] <;> simp [List.append_assoc]
    _ = _ := by rw [hpre] <;> simp [List.append_assoc]

/-- P2 has its entire one-use subproblem inside the outer region. -/
def RegionP2 (p : SevenDFA α) (pre region middle suffix : Word α) : Prop :=
  ∃ x b u d f y : Word α,
    region = x ++ b ++ u ++ d ++ u ++ f ++ y ∧
    p.A.accepts (pre ++ x) ∧ p.B.accepts b ∧ p.C.accepts u ∧
    p.D.accepts d ∧ p.F.accepts f ∧ p.G.accepts (y ++ middle ++ x) ∧
    p.H.accepts (y ++ suffix)

def BoundaryP2 (p : SevenDFA α) (pre region middle suffix : Word α)
    (q : Fin p.G.stateCount) : Prop :=
  ∃ x b u d f y : Word α,
    region = x ++ b ++ u ++ d ++ u ++ f ++ y ∧
    p.A.accepts (pre ++ x) ∧ p.B.accepts b ∧ p.C.accepts u ∧
    p.D.accepts d ∧ p.F.accepts f ∧
    boundaryLeft p.G q middle x ∧ boundaryRight p.G p.H q suffix y

theorem regionP2_iff_boundary (p : SevenDFA α) (pre region middle suffix : Word α) :
    RegionP2 p pre region middle suffix ↔
      ∃ q, BoundaryP2 p pre region middle suffix q := by
  constructor
  · intro hw
    rcases hw with ⟨x,b,u,d,f,y,hreg,ha,hb,hu,hd,hf,hg,hh⟩
    rcases (outer_context_split p.G p.H middle suffix x y).mp ⟨hg,hh⟩ with ⟨q,hl,hr⟩
    exact ⟨q,x,b,u,d,f,y,hreg,ha,hb,hu,hd,hf,hl,hr⟩
  · intro hw
    rcases hw with ⟨q,x,b,u,d,f,y,hreg,ha,hb,hu,hd,hf,hl,hr⟩
    rcases (outer_context_split p.G p.H middle suffix x y).mpr ⟨q,hl,hr⟩ with ⟨hg,hh⟩
    exact ⟨x,b,u,d,f,y,hreg,ha,hb,hu,hd,hf,hg,hh⟩

theorem regionP2_sound (p : SevenDFA α) (pre region middle suffix : Word α)
    (h : RegionP2 p pre region middle suffix) :
    MatchesWithin p.nested2 (pre ++ region ++ middle ++ region ++ suffix) 2 := by
  rcases h with ⟨x,b,u,d,f,y,hreg,ha,hb,hu,hd,hf,hg,hh⟩
  apply (Witness.nested2_iff p _).mpr
  refine ⟨pre ++ x,b,u,d,f,y ++ middle ++ x,y ++ suffix,ha,hb,hu,hd,hf,hg,hh,?_⟩
  rw [hreg] <;> simp [List.append_assoc]

/-- An arbitrary (noninvertible) DFA transition can be shared for all
    occurrences after shortening an identical capture. -/
theorem shorten_gap (d : DFA α) (q : Fin d.stateCount) (tail gap : Word α) :
    d.run q (tail ++ gap) = d.run (d.run q tail) gap := d.run_append q tail gap

end REWB
