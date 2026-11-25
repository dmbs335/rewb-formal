import REWB.CodeInterpretation

/-! Exact control-shape classification after backward liveness pruning.

The classification starts from an arbitrary source expression and its
actual plan. It does not assume that selected supplier intervals are
laminar, or that every reference has a preceding capture. The ten shapes
include initial-empty-register references and captures around such a
reference. Regular DFA factor extraction is a separate compiler step.
-/
namespace REWB.ControlShapes
variable {α : Type}

/-- Backward state: current register liveness and unmatched closing
    capture markers. A retained capture must have a live outgoing value. -/
abbrev CheckState := Bool × Nat

def step : Control → CheckState → Option CheckState
  | .recall, (_,d) => some (true,d)
  | .closeCap, (true,d) => some (false,d+1)
  | .closeCap, (false,_) => none
  | .openCap, (b,d+1) => some (b,d)
  | .openCap, (_,0) => none

/-- Read the control word backwards, matching the order of `Plan.prune`. -/
def check : List Control → CheckState → Option CheckState
  | [],s => some s
  | c::cs,s => (check cs s).bind (step c)

theorem check_append (xs ys : List Control) (s : CheckState) :
    check (xs++ys) s=(check ys s).bind (check xs) := by
  induction xs with
  | nil => simp [check]
  | cons c cs ih =>
    simp only [List.cons_append,check,ih]
    cases check ys s <;> rfl

/-- Every actual liveness-pruned plan passes the checker, in arbitrary
    enclosing depth and with either requested outgoing liveness bit. -/
theorem prune_check (p : Plan α) (live : Bool) (depth : Nat) :
    check (p.prune live).2.skeleton (live,depth)=
      some ((p.prune live).1,depth) := by
  induction p generalizing live depth with
  | nil => rfl
  | literal w => rfl
  | recall => rfl
  | seq p q hp hq =>
    change check ((p.prune (q.prune live).1).2.skeleton++
      (q.prune live).2.skeleton) (live,depth)=_
    rw [check_append,hq]
    exact hp (q.prune live).1 depth
  | cap p hp =>
    cases live
    · exact hp false depth
    · change check ([.openCap]++(p.prune false).2.skeleton++[.closeCap])
        (true,depth)=some ((p.prune false).1,depth)
      rw [check_append]
      change check ([.openCap]++(p.prune false).2.skeleton) (false,depth+1)=_
      rw [check_append,hp]
      rfl

def recalls : List Control → Nat
  | [] => 0
  | .recall::cs => 1+recalls cs
  | _::cs => recalls cs

theorem recalls_append (xs ys : List Control) :
    recalls (xs++ys)=recalls xs+recalls ys := by
  induction xs with
  | nil => simp [recalls]
  | cons c cs ih => cases c <;> simp [recalls,ih,Nat.add_assoc]

theorem skeleton_recalls (p : Plan α) : recalls p.skeleton=p.refs := by
  induction p with
  | nil => rfl
  | literal w => rfl
  | recall => rfl
  | seq p q hp hq => simp only [Plan.skeleton,Plan.refs,recalls_append,hp,hq]
  | cap p hp => simp [Plan.skeleton,Plan.refs,recalls_append,recalls,hp]

/-- All live, balanced shapes with at most two recalls. The three
    initial-empty cases are retained explicitly rather than discarded. -/
inductive Shape where
  | regular
  | emptyOnce
  | emptyTwice
  | once
  | sameValue
  | emptyInside
  | emptyBefore
  | nested2
  | nested1
  | independent
  deriving Repr, DecidableEq

def Shape.controls : Shape → List Control
  | .regular => []
  | .emptyOnce => [.recall]
  | .emptyTwice => [.recall,.recall]
  | .once => [.openCap,.closeCap,.recall]
  | .sameValue => [.openCap,.closeCap,.recall,.recall]
  | .emptyInside => [.openCap,.recall,.closeCap,.recall]
  | .emptyBefore => [.recall,.openCap,.closeCap,.recall]
  | .nested2 => [.openCap,.openCap,.closeCap,.recall,.closeCap,.recall]
  | .nested1 => [.openCap,.closeCap,.openCap,.recall,.closeCap,.recall]
  | .independent => [.openCap,.closeCap,.recall,.openCap,.closeCap,.recall]

def Shape.liveIn : Shape → Bool
  | .emptyOnce | .emptyTwice | .emptyInside | .emptyBefore => true
  | _ => false

def allShapes : List Shape :=
  [.regular,.emptyOnce,.emptyTwice,.once,.sameValue,.emptyInside,
    .emptyBefore,.nested2,.nested1,.independent]

theorem allShapes_complete (s : Shape) : s∈allShapes := by
  cases s <;> decide

theorem shape_check (s : Shape) :
    check s.controls (false,0)=some (s.liveIn,0) := by
  cases s <;> rfl

theorem shape_length (s : Shape) : s.controls.length≤6 := by
  cases s <;> decide

theorem shape_recalls (s : Shape) : recalls s.controls≤2 := by
  cases s <;> decide

def admissible (cs : List Control) : Bool :=
  decide (recalls cs≤2) &&
    ((check cs (false,0)=some (false,0)) ||
      (check cs (false,0)=some (true,0)))

/-- This is a small kernel-reduced finite classification (1,093 words),
    not a native-decide certificate or a bound assumed of the language. -/
theorem finite_classification :
    ((skeletons 6).filter admissible).all
      (fun cs=>(allShapes.map Shape.controls).contains cs)=true := by
  decide

theorem classify (cs : List Control) (hsize : cs.length≤6)
    (href : recalls cs≤2) (live : Bool)
    (hcheck : check cs (false,0)=some (live,0)) :
    ∃ s : Shape,cs=s.controls ∧ live=s.liveIn := by
  have had : admissible cs=true := by
    cases live <;> simp [admissible,href,hcheck]
  have hmem := List.mem_filter.mpr ⟨skeletons_complete 6 cs hsize,had⟩
  have hall := List.all_eq_true.mp finite_classification cs hmem
  have hsh : cs∈allShapes.map Shape.controls := by simpa using hall
  obtain ⟨s,_,hs⟩ := List.mem_map.mp hsh
  refine ⟨s,hs.symm,?_⟩
  rw [← hs,shape_check] at hcheck
  exact (Prod.mk.inj (Option.some.inj hcheck)).1.symm

theorem pruned_classification (p : Plan α) (h : p.refs≤2) :
    ∃ s : Shape,(p.prune false).2.skeleton=s.controls ∧
      (p.prune false).1=s.liveIn := by
  apply classify _ _ _ (p.prune false).1 (prune_check p false 0)
  · rw [Plan.skeleton_length,Plan.prune_refs]
    have hc := p.prune_no_more_caps
    omega
  · rw [skeleton_recalls,Plan.prune_refs]
    exact h

/-- Exact ten-way shape partition of the source expression's matching
    language. No supplier-interval or already-normalized-expression
    hypothesis occurs in either direction. -/
theorem matches_iff_shapes (p : Expr α) (w : Word α) :
    MatchesWithin p w 2 ↔
      ∃ s : Shape,∃ q : Plan α,PrunedOf p s.liveIn false q ∧
        q.skeleton=s.controls ∧ (q.eval []).1=w := by
  rw [matches_iff_plan]
  constructor
  · rintro ⟨x,hx,hr,hw⟩
    obtain ⟨s,hsk,hlive⟩ := pruned_classification x hr
    refine ⟨s,(x.prune false).2,⟨x,hx,?_⟩,hsk,?_⟩
    · rw [← hlive]
    · exact (x.prune_eval false [] [] (fun _=>rfl)).1.symm.trans hw
  · rintro ⟨s,q,⟨x,hx,hpr⟩,hsk,hw⟩
    have hq : (x.prune false).2=q := congrArg Prod.snd hpr
    have hr : x.refs≤2 := by
      rw [← x.prune_refs false,hq,← skeleton_recalls q,hsk]
      exact shape_recalls s
    exact ⟨x,hx,hr,by
      have he := (x.prune_eval false [] [] (fun _=>rfl)).1
      rw [hq] at he
      exact he.trans hw⟩

/-- Connect the exact shape classification directly to the verified
    regular marked-code compiler and its operational interpretation. -/
theorem matches_iff_shaped_codes (p : Expr α) (w : Word α) :
    MatchesWithin p w 2 ↔
      ∃ s : Shape,∃ z : Word (MarkedSymbol α),
        LiveCompiler.denote (LiveCompiler.compiled p) z ∧
        z.filterMap controlOf=s.controls ∧ LiveCompiler.CodeMatches z w 2 := by
  constructor
  · intro h
    obtain ⟨s,q,hq,hsk,hw⟩ := (matches_iff_shapes p w).mp h
    obtain ⟨x,hx,hpr⟩ := hq
    have hlive : (x.prune false).1=s.liveIn := congrArg Prod.fst hpr
    have hplan : (x.prune false).2=q := congrArg Prod.snd hpr
    refine ⟨s,q.code,(LiveCompiler.compiled_correct p q.code).mpr ?_,?_,?_⟩
    · exact ⟨s.liveIn,x,hx,hlive,by rw [hplan]⟩
    · rw [Plan.code_controls,hsk]
    · apply (LiveCompiler.codeMatches_plan q w 2).mpr
      refine ⟨?_,hw⟩
      rw [← skeleton_recalls q,hsk]
      exact shape_recalls s
  · rintro ⟨s,z,hz,hsk,hm⟩
    apply (LiveCompiler.match_compiled p w 2).mpr
    refine ⟨z,hz,hm,?_⟩
    rw [hsk]
    exact shape_length s

end REWB.ControlShapes
