import REWB.PhaseEqualityCache

/-! The P2 phase loop with materialized equality and exterior contexts.
    The prefix is consumed once and the suffix accepting set is an array,
    rather than a closure that rescans the suffix on every descriptor.
    All phase-dependent character tests use the shared equality cache. -/
namespace REWB.ContextCache
open REWB.Periodic
variable {α : Type}

def countedRun (d : DFA α) (v : Fin d.stateCount) : Word α→Fin d.stateCount×Nat
  | [] => (v,0)
  | c::cs =>
    let rest := countedRun d (d.step v c) cs
    (rest.1,rest.2+1)

theorem countedRun_correct (d : DFA α) (v : Fin d.stateCount) (w : Word α) :
    countedRun d v w=(d.run v w,w.length) := by
  induction w generalizing v with
  | nil => rfl
  | cons c cs ih =>
    change ((countedRun d (d.step v c) cs).1,(countedRun d (d.step v c) cs).2+1)=_
    rw [ih]
    rfl

def suffix (d : DFA α) (post : Word α) : Array Bool×Nat :=
  let r := PeriodicCache.countedMap (fun i=>
    let state := countedRun d (PeriodicCache.state d i) post
    (d.final state.1,state.2)) (List.range d.stateCount)
  (r.1.toArray,r.2)

theorem suffix_lookup (d : DFA α) (post : Word α) (v : Fin d.stateCount) :
    (suffix d post).1[v.val]?=some (d.final (d.run v post)) := by
  unfold suffix
  simp only [List.getElem?_toArray,PeriodicCache.countedMap_values,List.getElem?_map,
    List.getElem?_range,v.isLt,if_true,Option.map,countedRun_correct,PeriodicCache.state_val]

theorem suffix_cost (d : DFA α) (post : Word α) :
    (suffix d post).2=d.stateCount*post.length := by
  unfold suffix
  rw [PeriodicCache.countedMap_cost _ _ post.length]
  · rw [List.length_range]
  · intro i _
    simp only [countedRun_correct]

def prepare (d : DFA α) (pre post : Word α) : DFA α×Nat :=
  let initial := countedRun d d.initial pre
  let finals := suffix d post
  (⟨d.stateCount,initial.1,d.step,fun v=>(finals.1[v.val]?).getD false⟩,
    initial.2+finals.2)

theorem prepare_correct (d : DFA α) (pre post : Word α) :
    (prepare d pre post).1=contextual d pre post := by
  unfold prepare contextual
  rw [countedRun_correct]
  dsimp only
  have h : (fun v : Fin d.stateCount=>((suffix d post).1[v.val]?).getD false)=
      (fun v=>d.final (d.run v post)) := by
    funext v
    rw [suffix_lookup]
    rfl
  rw [h]

theorem prepare_cost (d : DFA α) (pre post : Word α) :
    (prepare d pre post).2=pre.length+d.stateCount*post.length := by
  unfold prepare
  rw [countedRun_correct]
  dsimp only
  rw [suffix_cost]

end REWB.ContextCache

namespace REWB.FullyCachedP2
open REWB.Periodic REWB.PhaseSolver REWB.AffineProjection
variable {α : Type}

structure Shared (P : SevenDFA α) where
  a : DFA α
  h : DFA α
  ta : PeriodicCache.Table a
  tb : PeriodicCache.Table P.B
  tc : PeriodicCache.Table P.C
  td : PeriodicCache.Table P.D
  tf : PeriodicCache.Table P.F
  tg : PeriodicCache.Table P.G
  th : PeriodicCache.Table h
  equality : PhaseEqualityCache.Table

def prepare [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (pre post : Word α) : Shared P :=
  let a := (ContextCache.prepare P.A pre []).1
  let h := (ContextCache.prepare P.H [] post).1
  ⟨a,h,(PeriodicCache.build a s q).1,
    (PeriodicCache.build P.B s q).1,(PeriodicCache.build P.C s q).1,
    (PeriodicCache.build P.D s q).1,(PeriodicCache.build P.F s q).1,
    (PeriodicCache.build P.G s q).1,(PeriodicCache.build h s q).1,
    (PhaseEqualityCache.build s q).1⟩

/-- Counts DFA transitions and alphabet comparisons during preparation.
    It does not count array allocation, arithmetic, or integer projection. -/
def countedPrepare [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (pre post : Word α) : Shared P×Nat :=
  let a := ContextCache.prepare P.A pre []
  let h := ContextCache.prepare P.H [] post
  let ta := PeriodicCache.build a.1 s q
  let tb := PeriodicCache.build P.B s q
  let tc := PeriodicCache.build P.C s q
  let td := PeriodicCache.build P.D s q
  let tf := PeriodicCache.build P.F s q
  let tg := PeriodicCache.build P.G s q
  let th := PeriodicCache.build h.1 s q
  let te := PhaseEqualityCache.build s q
  (⟨a.1,h.1,ta.1,tb.1,tc.1,td.1,tf.1,tg.1,th.1,te.1⟩,
    a.2+h.2+ta.2+tb.2+tc.2+td.2+tf.2+tg.2+th.2+te.2)

theorem countedPrepare_correct [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q : Nat) (pre post : Word α) :
    (countedPrepare P s q pre post).1=prepare P s q pre post := rfl

def stateSum (P : SevenDFA α) : Nat :=
  P.A.stateCount+P.B.stateCount+P.C.stateCount+P.D.stateCount+
    P.F.stateCount+P.G.stateCount+P.H.stateCount

theorem countedPrepare_cost [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q : Nat) (pre post : Word α) :
    (countedPrepare P s q pre post).2=
      pre.length+P.H.stateCount*post.length+q*(stateSum P*q)+q^3 := by
  simp only [countedPrepare,ContextCache.prepare_cost,PeriodicCache.build_cost,
    ContextCache.prepare_correct,contextual,PhaseEqualityCache.build_cost,
    List.length_nil,Nat.mul_zero,Nat.add_zero,Nat.zero_add,stateSum,Nat.add_mul,Nat.mul_add]
  omega

def formula (P : SevenDFA α) (q n : Nat) (I : Shared P)
    (L : P2Periodic.Layout Endpoint) : Formula :=
  both (CachedPhase.regular q n I.a I.ta P2Periodic.zeroEndpoint L.p)
    (both (CachedPhase.regular q n P.B I.tb L.p L.i)
    (both (CachedPhase.regular q n P.C I.tc L.i L.a)
    (both (CachedPhase.regular q n P.D I.td L.a L.j)
    (both (CachedPhase.regular q n P.F I.tf L.t L.e)
    (both (CachedPhase.regular q n P.G I.tg L.e L.k)
    (both (CachedPhase.regular q n I.h I.th L.f (P2Periodic.endEndpoint q n))
    (both (PhaseEqualityCache.equalFormula q n I.equality L.i L.a L.j L.t)
    (both (PhaseEqualityCache.equalFormula q n I.equality L.p L.e L.k L.f) [[]]))))))))

theorem formula_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (L : P2Periodic.Layout Endpoint) :
    formula P q n (prepare P s q pre post) L=
      compileSystem q n s (P2Periodic.constraints P q n pre post L) := by
  simp only [formula,prepare,ContextCache.prepare_correct,CachedPhase.regular_eq,
    PhaseEqualityCache.equalFormula_eq,P2Periodic.constraints,compileSystem,Constraint.compile]

def countedFormula (P : SevenDFA α) (q n : Nat) (I : Shared P)
    (L : P2Periodic.Layout Endpoint) : Formula×Nat :=
  let inner := PhaseEqualityCache.countedFormula q n I.equality L.i L.a L.j L.t
  let outer := PhaseEqualityCache.countedFormula q n I.equality L.p L.e L.k L.f
  (both (CachedPhase.regular q n I.a I.ta P2Periodic.zeroEndpoint L.p)
    (both (CachedPhase.regular q n P.B I.tb L.p L.i)
    (both (CachedPhase.regular q n P.C I.tc L.i L.a)
    (both (CachedPhase.regular q n P.D I.td L.a L.j)
    (both (CachedPhase.regular q n P.F I.tf L.t L.e)
    (both (CachedPhase.regular q n P.G I.tg L.e L.k)
    (both (CachedPhase.regular q n I.h I.th L.f (P2Periodic.endEndpoint q n))
    (both inner.1 (both outer.1 [[]])))))))),inner.2+outer.2)

theorem countedFormula_correct (P : SevenDFA α) (q n : Nat) (I : Shared P)
    (L : P2Periodic.Layout Endpoint) :
    (countedFormula P q n I L).1=formula P q n I L := by
  simp only [countedFormula,PhaseEqualityCache.countedFormula_correct,formula]

theorem countedFormula_cost (P : SevenDFA α) (q n : Nat) (I : Shared P)
    (L : P2Periodic.Layout Endpoint) :
    (countedFormula P q n I L).2≤6 := by
  have h1 := PhaseEqualityCache.countedFormula_cost q n I.equality L.i L.a L.j L.t
  have h2 := PhaseEqualityCache.countedFormula_cost q n I.equality L.p L.e L.k L.f
  change (PhaseEqualityCache.countedFormula q n I.equality L.i L.a L.j L.t).2+
    (PhaseEqualityCache.countedFormula q n I.equality L.p L.e L.k L.f).2≤6
  omega

def solveAt (P : SevenDFA α) (n q : Nat) (I : Shared P)
    (ph : P2Periodic.Layout Nat) : Bool :=
  solve 8 (formula P q n I (P2Periodic.endpoints ph)) []

theorem solveAt_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    solveAt P n q (prepare P s q pre post) ph=
      P2Periodic.solveAt P s n q pre post ph := by
  unfold solveAt
  rw [formula_eq]
  rfl

def countedSolveAt (P : SevenDFA α) (n q : Nat) (I : Shared P)
    (ph : P2Periodic.Layout Nat) : Bool×Nat :=
  let f := countedFormula P q n I (P2Periodic.endpoints ph)
  (solve 8 f.1 [],f.2)

theorem countedSolveAt_correct (P : SevenDFA α) (n q : Nat) (I : Shared P)
    (ph : P2Periodic.Layout Nat) :
    (countedSolveAt P n q I ph).1=solveAt P n q I ph := by
  simp only [countedSolveAt,countedFormula_correct,solveAt]

theorem countedSolveAt_cost (P : SevenDFA α) (n q : Nat) (I : Shared P)
    (ph : P2Periodic.Layout Nat) :
    (countedSolveAt P n q I ph).2≤6 := countedFormula_cost P q n I (P2Periodic.endpoints ph)

def solveFamily [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (pre post : Word α) : Bool :=
  let I := prepare P s q pre post
  (P2Periodic.choices q).any (fun v=>solveAt P n q I (P2Periodic.extend q v))

theorem solveFamily_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (pre post : Word α) :
    solveFamily P s n q pre post=P2Periodic.solveFamily P s n q pre post := by
  unfold solveFamily P2Periodic.solveFamily
  simp only [solveAt_eq]

theorem countedMap_bound {X Y : Type} (f : X→Y×Nat) (xs : List X) (bound : Nat)
    (h : ∀ x,x∈xs→(f x).2≤bound) :
    (PeriodicCache.countedMap f xs).2≤xs.length*bound := by
  induction xs with
  | nil => simp [PeriodicCache.countedMap]
  | cons x xs ih =>
    change (f x).2+(PeriodicCache.countedMap f xs).2≤(xs.length+1)*bound
    rw [Nat.add_mul,Nat.one_mul]
    have hh := h x (by simp)
    have ht := ih (fun y hy=>h y (by simp [hy]))
    omega

/-- Evaluates all q^5 phases and returns the number of equality-cache
    reads actually made. Descriptor and projection work is not this count. -/
def countedPhases (P : SevenDFA α) (n q : Nat) (I : Shared P) : Bool×Nat :=
  let results := PeriodicCache.countedMap
    (fun v=>countedSolveAt P n q I (P2Periodic.extend q v)) (P2Periodic.choices q)
  (results.1.any id,results.2)

theorem countedPhases_correct (P : SevenDFA α) (n q : Nat) (I : Shared P) :
    (countedPhases P n q I).1=
      (P2Periodic.choices q).any (fun v=>solveAt P n q I (P2Periodic.extend q v)) := by
  simp only [countedPhases,PeriodicCache.countedMap_values,List.any_map,
    Function.comp_def,countedSolveAt_correct,id_eq]

theorem countedPhases_cost (P : SevenDFA α) (n q : Nat) (I : Shared P) :
    (countedPhases P n q I).2≤6*q^5 := by
  have h := countedMap_bound
    (fun v=>countedSolveAt P n q I (P2Periodic.extend q v)) (P2Periodic.choices q) 6
    (fun v _=>countedSolveAt_cost P n q I (P2Periodic.extend q v))
  rw [P2Periodic.choices_length,Nat.mul_comm _ 6] at h
  exact h

def countedSolveFamily [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (pre post : Word α) : Bool×Nat :=
  let I := prepare P s q pre post
  countedPhases P n q I

theorem countedSolveFamily_correct [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (pre post : Word α) :
    (countedSolveFamily P s n q pre post).1=solveFamily P s n q pre post :=
  countedPhases_correct P n q _

theorem countedSolveFamily_cost [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (pre post : Word α) :
    (countedSolveFamily P s n q pre post).2≤6*q^5 := countedPhases_cost P n q _

theorem solveFamily_sound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (h : LeastPeriod s n q) (pre post : Word α)
    (hs : solveFamily P s n q pre post=true) :
    MatchesWithin P.nested2 (pre++segment s 0 n++post) 2 := by
  rw [solveFamily_eq] at hs
  exact P2Periodic.solveFamily_sound P s n q h pre post hs

theorem solveFamily_complete_long [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (h : LeastPeriod s n q) (pre post : Word α) (x : P2Periodic.Layout Nat)
    (hw : P2Periodic.Witness P s n pre post x) (hlong : q≤x.e-x.p) :
    solveFamily P s n q pre post=true := by
  rw [solveFamily_eq]
  exact P2Periodic.solveFamily_complete_long P s n q h pre post x hw hlong

end REWB.FullyCachedP2
