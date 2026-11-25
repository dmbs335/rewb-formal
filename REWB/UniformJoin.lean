import REWB.UniformPhaseBounds
import REWB.OfflineJoin

/-! Actual fixed-pattern constants for chronological P1 batches.
    Source events do not inspect a target-specific C gap: the gap-free
    source compiler describes only the earlier capture, and OfflineJoin
    checks C between the source end and the target start.

    Event generation and collision-free word-key construction remain
    separate obligations. The counters below count interval tests, event
    visits and text visits, not sorting comparisons or machine steps. -/
namespace REWB.UniformJoin
open REWB.AffineProjection REWB.PhaseSolver REWB.Periodic
open REWB.UniformProjection REWB.UniformPhaseBounds
variable {α : Type}

def anyWord : DFA α := ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>true⟩

def withoutGap (P : SevenDFA α) : SevenDFA α :=
  ⟨P.A,P.B,anyWord,P.D,P.F,P.G,P.H⟩

def localSource (P : SevenDFA α) (s : Nat→α) (n q a phase rho : Nat)
    (pre : Word α) : Formula :=
  if tailLen q (P1Source.start q a phase) (P2Periodic.endEndpoint q a)=rho then
    both (regularFormula q n s (contextual P.A pre []) P2Periodic.zeroEndpoint
      (P1Source.start q a phase))
      (orderFormula q n (P1Source.start q a phase) (P2Periodic.endEndpoint q a))
  else []

theorem localSource_eq (P : SevenDFA α) (s : Nat→α) (n q a phase rho : Nat)
    (pre : Word α) :
    localSource P s n q a phase rho pre=
      P1Source.formula (withoutGap P) s n q a phase rho pre [] := by
  simp only [localSource,P1Source.formula,withoutGap,anyWord,DFA.run,Bool.and_true,
    decide_eq_true_eq]

theorem localSource_good (P : SevenDFA α) (s : Nat→α) (n q a phase rho : Nat)
    (pre : Word α) (h : Period s n q) :
    FormulaGood (localSource P s n q a phase rho pre) := by
  rw [localSource_eq]
  exact P1Source.formula_good (withoutGap P) s n q a phase rho pre [] h

theorem localSource_covered (P : SevenDFA α) (s : Nat→α) (n q a phase rho : Nat)
    (pre : Word α) :
    Covered (localSource P s n q a phase rho pre) (p1SourceFamily P) := by
  rw [localSource_eq]
  exact p1_source_covered (withoutGap P) s n q a phase rho pre []

theorem localSource_correct (P : SevenDFA α) (s : Nat→α) (n q a phase rho m : Nat)
    (pre : Word α) (h : Period s n q) (hq : 0<q) :
    decideFormula (localSource P s n q a phase rho pre) [(m:Int)]=true ↔
      let l := P1Source.start q a phase
      let r := P2Periodic.endEndpoint q a
      l.valid q n [(m:Int)] ∧ r.valid q n [(m:Int)] ∧ l.pos q [(m:Int)]≤a ∧
      tailLen q l r=rho ∧
      P.A.accepts (pre++P2Periodic.factor s 0 (l.pos q [(m:Int)])) := by
  rw [localSource_eq,P1Source.formula_correct _ _ _ _ _ _ _ _ _ _ h hq]
  simp only [withoutGap,anyWord,DFA.accepts,DFA.run,and_true]

/-- The earlier capture is described without knowing the later target
    or scanning the C-gap between them. -/
theorem localSource_word (P : SevenDFA α) (s : Nat→α) (n q a phase rho m : Nat)
    (pre : Word α) (h : Period s n q) (hq : 0<q)
    (hs : decideFormula (localSource P s n q a phase rho pre) [(m:Int)]=true) :
    ∃ pref,pre++segment s 0 a=
      pref++P1Target.keyWord (segment s phase q) rho m ∧ P.A.accepts pref := by
  obtain ⟨hl,hr,ho,ht,hA⟩ :=
    (localSource_correct P s n q a phase rho m pre h hq).mp hs
  let l := P1Source.start q a phase
  let env := [(m:Int)]
  have han : a≤n := by
    have hh := hr.2.2
    rwa [P2Periodic.end_pos] at hh
  have horder : l.pos q env≤(P2Periodic.endEndpoint q a).pos q env := by
    rwa [P2Periodic.end_pos]
  have hcount := P1Source.source_count q n a phase m hq hl han ho
  have he := P1Target.key_factor s q n h l (P2Periodic.endEndpoint q a) env hl hr horder
    hq m rho hcount ht
  rw [P2Periodic.end_pos] at he
  change P2Periodic.factor s (l.pos q env) a=P1Target.keyWord (segment s phase q) rho m at he
  refine ⟨pre++P2Periodic.factor s 0 (l.pos q env),?_,hA⟩
  change pre++P2Periodic.factor s 0 a=_
  rw [P2Periodic.factor_split s 0 (l.pos q env) a (Nat.zero_le _) ho,he,List.append_assoc]

theorem localSource_with_gap (P : SevenDFA α) (s : Nat→α) (n q a phase rho m : Nat)
    (pre gap : Word α) (h : Period s n q) (hq : 0<q)
    (hs : decideFormula (localSource P s n q a phase rho pre) [(m:Int)]=true)
    (hc : P.C.accepts gap) :
    P1Target.SourceOK P (pre++segment s 0 a++gap)
      (P1Target.keyWord (segment s phase q) rho m) := by
  obtain ⟨pref,he,hA⟩ := localSource_word P s n q a phase rho m pre h hq hs
  exact ⟨pref,gap,by rw [he],hA,hc⟩

structure SourceData (α : Type) where
  text : Nat→α
  n : Nat
  q : Nat
  endPos : Nat
  phase : Nat
  rho : Nat
  pre : Word α
  position : Nat
  key : Nat

structure TargetData (α : Type) where
  text : Nat→α
  n : Nat
  q : Nat
  outerStart : Nat
  rho : Nat
  post : Word α
  phases : P1Target.Layout Nat
  position : Nat
  key : Nat

def sourceEntry (P : SevenDFA α) (x : SourceData α) : TimedJoin.TimedEntry :=
  ⟨x.position,⟨x.key,localSource P x.text x.n x.q x.endPos x.phase x.rho x.pre⟩⟩

def targetEntry [DecidableEq α] (P : SevenDFA α) (x : TargetData α) : TimedJoin.TimedEntry :=
  ⟨x.position,⟨x.key,P1Target.projection P x.text x.n x.q x.outerStart x.rho x.post x.phases⟩⟩

def sources (P : SevenDFA α) (xs : List (SourceData α)) : List TimedJoin.TimedEntry :=
  xs.map (sourceEntry P)

def targets [DecidableEq α] (P : SevenDFA α) (xs : List (TargetData α)) : List TimedJoin.TimedEntry :=
  xs.map (targetEntry P)

theorem sources_good (P : SevenDFA α) (xs : List (SourceData α))
    (h : ∀ x,x∈xs→Period x.text x.n x.q) :
    TimedJoin.Good (p1Modulus P) (sources P xs) := by
  intro e he
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
  exact compatible_multiple _ _ _
    (projection_compatible 0 _ _ (localSource_covered P x.text x.n x.q x.endPos x.phase x.rho x.pre)
      (localSource_good P x.text x.n x.q x.endPos x.phase x.rho x.pre (h x hx)))
    (Nat.dvd_mul_right _ _)

theorem targets_good [DecidableEq α] (P : SevenDFA α) (xs : List (TargetData α))
    (h : ∀ x,x∈xs→LeastPeriod x.text x.n x.q) :
    TimedJoin.Good (p1Modulus P) (targets P xs) := by
  intro e he
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
  exact p1_target_compatible P x.text x.n x.q x.outerStart x.rho x.post x.phases (h x hx)

theorem sources_weight (P : SevenDFA α) (xs : List (SourceData α)) :
    TimedJoin.weight (sources P xs)≤p1SourceBudget P*xs.length := by
  induction xs with
  | nil => simp [sources,TimedJoin.weight]
  | cons x xs ih =>
    have hx := projection_branches 0 _ _
      (localSource_covered P x.text x.n x.q x.endPos x.phase x.rho x.pre)
    change (localSource P x.text x.n x.q x.endPos x.phase x.rho x.pre).length≤p1SourceBudget P at hx
    change (localSource P x.text x.n x.q x.endPos x.phase x.rho x.pre).length+
      TimedJoin.weight (sources P xs)≤p1SourceBudget P*(xs.length+1)
    rw [Nat.mul_add,Nat.mul_one]
    omega

theorem targets_weight [DecidableEq α] (P : SevenDFA α) (xs : List (TargetData α)) :
    TimedJoin.weight (targets P xs)≤p1TargetBudget P*xs.length := by
  induction xs with
  | nil => simp [targets,TimedJoin.weight]
  | cons x xs ih =>
    have hx := p1_target_branches P x.text x.n x.q x.outerStart x.rho x.post x.phases
    change (P1Target.projection P x.text x.n x.q x.outerStart x.rho x.post x.phases).length+
      TimedJoin.weight (targets P xs)≤p1TargetBudget P*(xs.length+1)
    rw [Nat.mul_add,Nat.mul_one]
    omega

def run [DecidableEq α] (P : SevenDFA α) (N : Nat) (w : Word α)
    (xs : List (SourceData α)) (ys : List (TargetData α)) : OfflineJoin.Result :=
  OfflineJoin.run P.C (p1Modulus P) N w (sources P xs) (targets P ys)

/-- The existing exact chronological join now has a pattern-only
    modulus, automatically justified for actual generated formulas. -/
theorem run_correct [DecidableEq α] (P : SevenDFA α) (N : Nat) (w : Word α)
    (xs : List (SourceData α)) (ys : List (TargetData α))
    (hS : ∀ x,x∈xs→Period x.text x.n x.q)
    (hT : ∀ y,y∈ys→LeastPeriod y.text y.n y.q)
    (hX : ∀ x,x∈xs→x.position≤w.length)
    (hY : ∀ y,y∈ys→y.position≤w.length) :
    (run P N w xs ys).answer=true ↔
      TimedJoin.Match P.C w N (sources P xs) (targets P ys) := by
  apply OfflineJoin.run_correct P.C (p1Modulus P) N w _ _
    (p1Modulus_pos P) (sources_good P xs hS) (targets_good P ys hT)
  · intro e he
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
    exact hX x hx
  · intro e he
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp he
    exact hY y hy

/-- A fixed constant per event at each chronological recursion level.
    Neither the run period q nor any exponent bound N occurs in that
    constant. Sorting and bit complexity are not counted here. -/
theorem run_counts [DecidableEq α] (P : SevenDFA α) (N : Nat) (w : Word α)
    (xs : List (SourceData α)) (ys : List (TargetData α)) :
    (run P N w xs ys).tests≤(DyadicIndex.heightFor w.length+1)*
      (p1Modulus P*(p1SourceBudget P*xs.length+P.C.stateCount*(p1TargetBudget P*ys.length))) ∧
    (run P N w xs ys).eventVisits≤(DyadicIndex.heightFor w.length+1)*(xs.length+ys.length) ∧
    (run P N w xs ys).textVisits≤(DyadicIndex.heightFor w.length+1)*w.length := by
  have h := OfflineJoin.solve_cost P.C (p1Modulus P) N (DyadicIndex.heightFor w.length)
    w (sources P xs) (targets P ys)
  refine ⟨Nat.le_trans h.1 ?_,?_,h.2.2.1⟩
  · apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add (sources_weight P xs)
      (Nat.mul_le_mul_left P.C.stateCount (targets_weight P ys))
  · simpa only [sources,targets,List.length_map] using h.2.1

end REWB.UniformJoin
