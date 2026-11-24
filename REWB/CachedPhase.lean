import REWB.PeriodicCache

/-! Cached compiler for a fixed run. The caller prepares each regular
    automaton once, then instantiates arbitrary endpoint phases.
    The resulting affine formula is exactly the uncached formula. -/
namespace REWB.CachedPhase
open REWB.Periodic
open REWB.PhaseSolver
open REWB.AffineProjection
variable {α : Type}

def regular (q n : Nat) (d : DFA α) (T : PeriodicCache.Table d)
    (a b : Endpoint) : Formula :=
  both (orderFormula q n a b)
    (match PeriodicCache.descriptor d T q a.phase (tailLen q a b) with
      | none => []
      | some D => descriptorFormula D (countExpr a b))

theorem both_nil_left (F : Formula) : both [] F=[] := rfl

theorem both_nil_right (F : Formula) : both F []=[] := by
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change both Cs []=[]
    exact ih

theorem bound_empty (q n : Nat) (a : Endpoint) (h : ¬a.phase<q) :
    a.bound q n=[] := by
  unfold Endpoint.bound
  have he : ¬(a.phase<q ∧ a.phase≤n) := fun h' => h h'.1
  rw [if_neg he]

theorem tail_lt (q : Nat) (a b : Endpoint)
    (ha : a.phase<q) (hb : b.phase<q) : tailLen q a b<q := by
  unfold tailLen phaseCoord residual
  change (if a.phase≤b.phase then b.phase-a.phase else q+b.phase-a.phase)<q
  split <;> omega

theorem order_empty_left (q n : Nat) (a b : Endpoint) (h : ¬a.phase<q) :
    orderFormula q n a b=[] := by
  unfold orderFormula
  rw [bound_empty q n a h,both_nil_left,both_nil_left]

theorem order_empty_right (q n : Nat) (a b : Endpoint) (h : ¬b.phase<q) :
    orderFormula q n a b=[] := by
  unfold orderFormula
  rw [bound_empty q n b h,both_nil_right,both_nil_left]

theorem regular_eq (q n : Nat) (s : Nat→α) (d : DFA α) (a b : Endpoint) :
    regular q n d (PeriodicCache.build d s q).1 a b=regularFormula q n s d a b := by
  unfold regular regularFormula
  by_cases ha : a.phase<q
  · by_cases hb : b.phase<q
    · rw [PeriodicCache.descriptor_correct d s q a.phase (tailLen q a b) ha
        (Nat.le_of_lt (tail_lt q a b ha hb))]
    · rw [order_empty_right q n a b hb,both_nil_left,both_nil_left]
  · rw [order_empty_left q n a b ha,both_nil_left,both_nil_left]

inductive Prepared (α : Type) where
  | plain : Constraint α → Prepared α
  | regular (d : DFA α) : PeriodicCache.Table d → Endpoint → Endpoint → Prepared α

def Prepared.forget : Prepared α→Constraint α
  | .plain c => c
  | .regular d _ a b => .regular d a b

def Prepared.Good (q : Nat) (s : Nat→α) : Prepared α→Prop
  | .plain _ => True
  | .regular d T _ _ => T=(PeriodicCache.build d s q).1

def Prepared.compile [DecidableEq α] (q n : Nat) (s : Nat→α) : Prepared α→Formula
  | .plain c => c.compile q n s
  | .regular d T a b => regular q n d T a b

theorem Prepared.compile_eq [DecidableEq α] (q n : Nat) (s : Nat→α)
    (c : Prepared α) (h : c.Good q s) :
    c.compile q n s=c.forget.compile q n s := by
  cases c with
  | plain c => rfl
  | regular d T a b =>
    change T=(PeriodicCache.build d s q).1 at h
    subst T
    exact regular_eq q n s d a b

def compile [DecidableEq α] (q n : Nat) (s : Nat→α) :
    List (Prepared α)→Formula
  | [] => [[]]
  | c::cs => both (c.compile q n s) (compile q n s cs)

theorem compile_eq [DecidableEq α] (q n : Nat) (s : Nat→α)
    (cs : List (Prepared α)) (h : ∀ c,c∈cs→c.Good q s) :
    compile q n s cs=compileSystem q n s (cs.map Prepared.forget) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change both (c.compile q n s) (compile q n s cs)=
      both (c.forget.compile q n s) (compileSystem q n s (cs.map Prepared.forget))
    rw [Prepared.compile_eq q n s c (h c (by simp)),
      ih (fun x hx=>h x (by simp [hx]))]

end REWB.CachedPhase

namespace REWB.CachedP2
open REWB.Periodic
open REWB.PhaseSolver
open REWB.AffineProjection
open REWB.CachedPhase
variable {α : Type}

/-- Prepare all seven regular automata once for a run, including the
    external A/H contexts. The phase loop reuses these arrays. -/
structure Shared (P : SevenDFA α) (pre post : Word α) where
  ta : PeriodicCache.Table (contextual P.A pre [])
  tb : PeriodicCache.Table P.B
  tc : PeriodicCache.Table P.C
  td : PeriodicCache.Table P.D
  tf : PeriodicCache.Table P.F
  tg : PeriodicCache.Table P.G
  th : PeriodicCache.Table (contextual P.H [] post)

def prepare (P : SevenDFA α) (s : Nat→α) (q : Nat) (pre post : Word α) :
    Shared P pre post :=
  ⟨(PeriodicCache.build (contextual P.A pre []) s q).1,
    (PeriodicCache.build P.B s q).1,(PeriodicCache.build P.C s q).1,
    (PeriodicCache.build P.D s q).1,(PeriodicCache.build P.F s q).1,
    (PeriodicCache.build P.G s q).1,(PeriodicCache.build (contextual P.H [] post) s q).1⟩

def constraints (P : SevenDFA α) (q n : Nat) (pre post : Word α)
    (I : Shared P pre post) (L : P2Periodic.Layout Endpoint) : List (Prepared α) :=
  [.regular (contextual P.A pre []) I.ta P2Periodic.zeroEndpoint L.p,
   .regular P.B I.tb L.p L.i,
   .regular P.C I.tc L.i L.a,
   .regular P.D I.td L.a L.j,
   .regular P.F I.tf L.t L.e,
   .regular P.G I.tg L.e L.k,
   .regular (contextual P.H [] post) I.th L.f (P2Periodic.endEndpoint q n),
   .plain (.equal L.i L.a L.j L.t),
   .plain (.equal L.p L.e L.k L.f)]

theorem constraints_good (P : SevenDFA α) (s : Nat→α) (q n : Nat)
    (pre post : Word α) (L : P2Periodic.Layout Endpoint) :
    ∀ c,c∈constraints P q n pre post (prepare P s q pre post) L→c.Good q s := by
  intro c hc
  simp only [constraints,List.mem_cons] at hc
  rcases hc with h|h|h|h|h|h|h|h|h|h
  all_goals try (subst c; rfl)
  simp at h

theorem forget_constraints (P : SevenDFA α) (q n : Nat) (pre post : Word α)
    (I : Shared P pre post) (L : P2Periodic.Layout Endpoint) :
    (constraints P q n pre post I L).map Prepared.forget=P2Periodic.constraints P q n pre post L := rfl

def solveAt [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (n q : Nat)
    (pre post : Word α) (I : Shared P pre post) (ph : P2Periodic.Layout Nat) : Bool :=
  solve 8 (CachedPhase.compile q n s (constraints P q n pre post I (P2Periodic.endpoints ph))) []

theorem solveAt_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (n q : Nat)
    (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    solveAt P s n q pre post (prepare P s q pre post) ph =
      P2Periodic.solveAt P s n q pre post ph := by
  unfold solveAt
  rw [CachedPhase.compile_eq _ _ _ _ (constraints_good P s q n pre post _),forget_constraints]
  rfl

def solveFamily [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (n q : Nat)
    (pre post : Word α) : Bool :=
  let I := prepare P s q pre post
  (P2Periodic.choices q).any (fun v=>solveAt P s n q pre post I (P2Periodic.extend q v))

theorem solveFamily_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (n q : Nat)
    (pre post : Word α) :
    solveFamily P s n q pre post=P2Periodic.solveFamily P s n q pre post := by
  unfold solveFamily P2Periodic.solveFamily
  simp only [solveAt_eq]

end REWB.CachedP2
