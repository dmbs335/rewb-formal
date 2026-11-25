import REWB.PeriodicConstructionFormula
import REWB.CountedCachedP1
import REWB.CountedCachedP2

/-! The actual cached P1/P2 initial formulas, including every finite
descriptor and DNF product. Their concrete budgets depend only on the
fixed DFA state counts. Numeric endpoint literals affect the output
formula but cannot increase the construction loops. -/
namespace REWB.PeriodicConstruction.Formula
open REWB.PeriodicConstruction REWB.AffineProjection REWB.PhaseSolver
variable {α : Type}

theorem covers_mono (r : Result AffineProjection.Formula) (a b : Budget)
    (h : Covers r a) (hB : a.branches≤b.branches) (hA : a.atoms≤b.atoms)
    (hW : a.work≤b.work) : Covers r b :=
  ⟨⟨Nat.le_trans h.1.1 hB,fun C hc=>Nat.le_trans (h.1.2 C hc) hA⟩,Nat.le_trans h.2 hW⟩

def equalityCore (q : Nat) (T : PhaseEqualityCache.Table) (a b c d : Endpoint) :
    Result AffineProjection.Formula :=
  if tailLen q a b=tailLen q c d then
    if a.phase=c.phase then charge (eq (countExpr a b) (countExpr c d)) 13
    else
      let test:=PhaseEqualityCache.countedLookup T a.phase c.phase (tailLen q a b)
      if test.1.getD false then
        charge (join (eq (countExpr a b) (.lit 0)) (eq (countExpr c d) (.lit 0))) (test.2+15)
      else ([],test.2+8)
  else ([],9)

def coreBudget : Budget := (eqBudget.join eqBudget).charge 18

theorem equalityCore_value (q : Nat) (T : PhaseEqualityCache.Table) (a b c d : Endpoint) :
    (equalityCore q T a b c d).1=PhaseEqualityCache.equalityCore q T a b c d := by
  simp only [equalityCore,PhaseEqualityCache.equalityCore,charge,eq_value,join_value,
    PhaseEqualityCache.countedLookup_correct,PhaseEqualityCache.equalAt]
  split <;> (try split) <;> (try split) <;> rfl

theorem equalityCore_covers (q : Nat) (T : PhaseEqualityCache.Table) (a b c d : Endpoint) :
    Covers (equalityCore q T a b c d) coreBudget := by
  unfold equalityCore
  split
  · split
    · exact covers_mono _ _ _ (charge_covers _ _ _ (eq_covers _ _))
        (by decide) (by decide) (by decide)
    · dsimp only
      have ht:=PhaseEqualityCache.countedLookup_cost T a.phase c.phase (tailLen q a b)
      split
      · apply covers_mono _ _ _ (charge_covers _ _ _
          (join_covers _ _ _ _ (eq_covers _ _) (eq_covers _ _)))
        · exact Nat.le_refl _
        · exact Nat.le_refl _
        · change (eqBudget.join eqBudget).work+(_+15)≤(eqBudget.join eqBudget).work+18
          omega
      · refine ⟨⟨by simp,by simp⟩,?_⟩
        change (PhaseEqualityCache.countedLookup _ _ _ _).2+8≤_
        have hh : 11≤coreBudget.work := by decide
        omega
  · simp [Covers,Shape,coreBudget,eqBudget,leBudget,Budget.join,Budget.charge]

def equal (q n : Nat) (T : PhaseEqualityCache.Table) (a b c d : Endpoint) :
    Result AffineProjection.Formula :=
  join (join (order q n a b) (order q n c d))
    (join (order q n a c) (equalityCore q T a b c d))

def equalBudget : Budget := (orderBudget.join orderBudget).join (orderBudget.join coreBudget)

theorem equal_value (q n : Nat) (T : PhaseEqualityCache.Table) (a b c d : Endpoint) :
    (equal q n T a b c d).1=PhaseEqualityCache.equalFormula q n T a b c d := by
  simp only [equal,join_value,order_value,equalityCore_value,PhaseEqualityCache.equalFormula]

theorem equal_covers (q n : Nat) (T : PhaseEqualityCache.Table) (a b c d : Endpoint) :
    Covers (equal q n T a b c d) equalBudget :=
  join_covers _ _ _ _ (join_covers _ _ _ _ (order_covers _ _ _ _) (order_covers _ _ _ _))
    (join_covers _ _ _ _ (order_covers _ _ _ _) (equalityCore_covers _ _ _ _ _ _))

def system : List (Result AffineProjection.Formula)→Result AffineProjection.Formula
  | [] => ([[]],1)
  | F::Fs => charge (join F (system Fs)) 2

def systemBudget : List Budget→Budget
  | [] => ⟨1,0,1⟩
  | b::bs => (b.join (systemBudget bs)).charge 2

inductive CoversList : List (Result AffineProjection.Formula)→List Budget→Prop
  | nil : CoversList [] []
  | cons : Covers F b→CoversList Fs bs→CoversList (F::Fs) (b::bs)

theorem system_covers (Fs : List (Result AffineProjection.Formula)) (bs : List Budget)
    (h : CoversList Fs bs) : Covers (system Fs) (systemBudget bs) := by
  induction h with
  | nil => simp [system,systemBudget,Covers,Shape]
  | cons hf hs ih => exact charge_covers _ _ _ (join_covers _ _ _ _ hf ih)

def p2 (P : SevenDFA α) (q n : Nat) (I : FullyCachedP2.Shared P)
    (L : P2Periodic.Layout Endpoint) : Result AffineProjection.Formula :=
  charge (system [regular q n I.a I.ta P2Periodic.zeroEndpoint L.p,
    regular q n P.B I.tb L.p L.i,regular q n P.C I.tc L.i L.a,
    regular q n P.D I.td L.a L.j,regular q n P.F I.tf L.t L.e,
    regular q n P.G I.tg L.e L.k,
    regular q n I.h I.th L.f (P2Periodic.endEndpoint q n),
    equal q n I.equality L.i L.a L.j L.t,equal q n I.equality L.p L.e L.k L.f]) 32

def p2Budget (P : SevenDFA α) (a h : Nat) : Budget :=
  (systemBudget [regularBudget a,regularBudget P.B.stateCount,regularBudget P.C.stateCount,
    regularBudget P.D.stateCount,regularBudget P.F.stateCount,regularBudget P.G.stateCount,
    regularBudget h,equalBudget,equalBudget]).charge 32

theorem p2_value (P : SevenDFA α) (q n : Nat) (I : FullyCachedP2.Shared P)
    (L : P2Periodic.Layout Endpoint) :
    (p2 P q n I L).1=FullyCachedP2.formula P q n I L := by
  simp only [p2,system,charge,join_value,regular_value,equal_value,FullyCachedP2.formula]

theorem p2_covers (P : SevenDFA α) (q n : Nat) (I : FullyCachedP2.Shared P)
    (L : P2Periodic.Layout Endpoint) : Covers (p2 P q n I L)
      (p2Budget P I.a.stateCount I.h.stateCount) := by
  apply charge_covers
  apply system_covers
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (equal_covers _ _ _ _ _ _ _) ?_
  refine CoversList.cons (equal_covers _ _ _ _ _ _ _) ?_
  exact CoversList.nil

def targetSystem (P : SevenDFA α) (n q p : Nat) (I : FullyCachedP2.Shared P)
    (L : P1Target.Layout Endpoint) : Result AffineProjection.Formula :=
  charge (system [regular q n P.D I.td (P1Target.fixed q p) L.j,
    regular q n P.B I.tb L.j L.t,regular q n P.F I.tf L.t L.e,
    regular q n P.G I.tg L.e L.k,
    regular q n I.h I.th L.f (P2Periodic.endEndpoint q n),
    equal q n I.equality (P1Target.fixed q p) L.e L.k L.f]) 25

def targetSystemBudget (P : SevenDFA α) (h : Nat) : Budget :=
  (systemBudget [regularBudget P.D.stateCount,regularBudget P.B.stateCount,
    regularBudget P.F.stateCount,regularBudget P.G.stateCount,regularBudget h,equalBudget]).charge 25

theorem targetSystem_value (P : SevenDFA α) (n q p : Nat) (I : FullyCachedP2.Shared P)
    (L : P1Target.Layout Endpoint) :
    (targetSystem P n q p I L).1=CachedP1.targetSystem P n q p I L := by
  simp only [targetSystem,system,charge,join_value,regular_value,equal_value,CachedP1.targetSystem]

theorem targetSystem_covers (P : SevenDFA α) (n q p : Nat) (I : FullyCachedP2.Shared P)
    (L : P1Target.Layout Endpoint) :
    Covers (targetSystem P n q p I L) (targetSystemBudget P I.h.stateCount) := by
  apply charge_covers
  apply system_covers
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (regular_covers _ _ _ _ _ _) ?_
  refine CoversList.cons (equal_covers _ _ _ _ _ _ _) ?_
  exact CoversList.nil

def target (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : Result AffineProjection.Formula :=
  let L:=P1Target.endpoints ph
  if tailLen q L.j L.t=rho then
    charge (join (targetSystem P n q p I L) (eq (countExpr L.j L.t) (.var 5))) 20
  else ([],12)

def targetBudget (P : SevenDFA α) (h : Nat) : Budget :=
  ((targetSystemBudget P h).join eqBudget).charge 20

theorem target_value (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) :
    (target P n q p rho I ph).1=CachedP1.targetFormula P n q p rho I ph := by
  simp only [target,CachedP1.targetFormula,charge,join_value,targetSystem_value,eq_value]
  split <;> rfl

theorem target_covers (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : Covers (target P n q p rho I ph) (targetBudget P I.h.stateCount) := by
  unfold target
  dsimp only
  split
  · exact charge_covers _ _ _ (join_covers _ _ _ _ (targetSystem_covers _ _ _ _ _ _) (eq_covers _ _))
  · refine ⟨⟨by simp,by simp⟩,?_⟩
    change 12≤(_ : Budget).work
    simp only [targetBudget,Budget.charge]
    omega

def source (P : SevenDFA α) (n q a phase rho : Nat) (I : FullyCachedP2.Shared P) :
    Result AffineProjection.Formula :=
  let l:=P1Source.start q a phase
  let r:=P2Periodic.endEndpoint q a
  if tailLen q l r=rho then charge
    (join (regular q n I.a I.ta P2Periodic.zeroEndpoint l) (order q n l r)) 16
  else ([],10)

def sourceBudget (a : Nat) : Budget := (regularBudget a |>.join orderBudget).charge 16

theorem source_value (P : SevenDFA α) (n q a phase rho : Nat) (I : FullyCachedP2.Shared P) :
    (source P n q a phase rho I).1=CachedP1.source P n q a phase rho I := by
  simp only [source,CachedP1.source,charge,join_value,regular_value,order_value]
  split <;> rfl

theorem source_covers (P : SevenDFA α) (n q a phase rho : Nat) (I : FullyCachedP2.Shared P) :
    Covers (source P n q a phase rho I) (sourceBudget I.a.stateCount) := by
  unfold source
  dsimp only
  split
  · exact charge_covers _ _ _ (join_covers _ _ _ _ (regular_covers _ _ _ _ _ _) (order_covers _ _ _ _))
  · refine ⟨⟨by simp,by simp⟩,?_⟩
    change 10≤(_ : Budget).work
    simp only [sourceBudget,Budget.charge]
    omega

def projectTarget (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : Result AffineProjection.Formula :=
  let F:=target P n q p rho I ph
  let out:=CountedProjection.project 5 F.1
  (out.1,F.2+out.2+1)

theorem projectTarget_value (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) :
    (projectTarget P n q p rho I ph).1=(CountedCachedP1.project P n q p rho I ph).formula := by
  simp only [projectTarget,CountedProjection.project_value,target_value,
    CountedCachedP1.project_value,CachedP1.projection]

theorem projectTarget_work (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat)
    (h : UniformProjection.Covered (CachedP1.targetFormula P n q p rho I ph)
      (UniformPhaseBounds.p1TargetFamily P)) :
    (projectTarget P n q p rho I ph).2≤
      (targetBudget P I.h.stateCount).work+CountedCachedP1.targetSteps P+1 := by
  have hc:=(target_covers P n q p rho I ph).2
  have hp:=CountedCachedP1.project_uniform_steps 5 _ _ h
  unfold projectTarget
  dsimp only
  rw [target_value]
  exact Nat.add_le_add_right (Nat.add_le_add hc hp) 1

def solveP2 (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (ph : P2Periodic.Layout Nat) : Result Bool :=
  let F:=p2 P q n I (P2Periodic.endpoints ph)
  let out:=CountedProjection.search [] 8 F.1
  (out.1,F.2+out.2+20)

theorem solveP2_value (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (ph : P2Periodic.Layout Nat) :
    (solveP2 P n q I ph).1=(CountedCachedP2.solveAt P n q I ph).accepted := by
  simp only [solveP2,p2_value,CountedCachedP2.solveAt,FullyCachedP2.countedFormula_correct]

theorem solveP2_work (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (ph : P2Periodic.Layout Nat)
    (h : UniformProjection.Covered (FullyCachedP2.formula P q n I (P2Periodic.endpoints ph))
      (UniformPhaseBounds.p2Family P)) :
    (solveP2 P n q I ph).2≤(p2Budget P I.a.stateCount I.h.stateCount).work+
      CountedProjection.p2Steps P+20 := by
  have hc:=(p2_covers P q n I (P2Periodic.endpoints ph)).2
  have hp:=CountedProjection.p2_search_steps P _ h
  unfold solveP2
  dsimp only
  rw [p2_value]
  exact Nat.add_le_add_right (Nat.add_le_add hc hp) 20

end REWB.PeriodicConstruction.Formula
