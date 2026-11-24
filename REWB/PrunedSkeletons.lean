import REWB.LiveCapture

/-! Tie the concrete liveness transformation to the original expression,
    not merely to an arbitrary plan that happens to emit the same word.
    The finite control skeleton has at most 3k markers for k references.
    Regularity of the factor languages is a further compiler obligation. -/
namespace REWB
variable {α : Type}

inductive PlanOf : Expr α → Plan α → Prop where
  | atom (d : DFA α) (w : Word α) : d.accepts w → PlanOf (.atom d) (.literal w)
  | seq {p q : Expr α} {x y : Plan α} :
      PlanOf p x → PlanOf q y → PlanOf (p ⋙ q) (.seq x y)
  | altLeft {p q : Expr α} {x : Plan α} :
      PlanOf p x → PlanOf (.alt p q) x
  | altRight {p q : Expr α} {y : Plan α} :
      PlanOf q y → PlanOf (.alt p q) y
  | starNil (p : Expr α) : PlanOf (.star p) .nil
  | starCons {p : Expr α} {x y : Plan α} :
      PlanOf p x → PlanOf (.star p) y → PlanOf (.star p) (.seq x y)
  | capture {p : Expr α} {x : Plan α} :
      PlanOf p x → PlanOf (.capture p) (.cap x)
  | reference : PlanOf (.reference : Expr α) .recall

namespace PlanOf

theorem trace {p : Expr α} {q : Plan α} (h : PlanOf p q) :
    TraceOf p q.events := by
  induction h with
  | atom d w hw => exact .atom d w hw
  | seq hp hq ihp ihq => exact .seq ihp ihq
  | altLeft hp ih => exact .altLeft ih
  | altRight hp ih => exact .altRight ih
  | starNil p => exact .starNil p
  | starCons hp hq ihp ihq => exact .starCons ihp ihq
  | capture hp ih => exact .capture ih
  | reference => exact .reference

theorem fromTrace {p : Expr α} {es : List (Event α)} (h : TraceOf p es) :
    ∃ q, PlanOf p q ∧ q.events=es := by
  induction h with
  | atom d w hw => exact ⟨.literal w,.atom d w hw,rfl⟩
  | seq hp hq ihp ihq =>
    obtain ⟨x,hx,rfl⟩ := ihp
    obtain ⟨y,hy,rfl⟩ := ihq
    exact ⟨.seq x y,.seq hx hy,rfl⟩
  | altLeft hp ih =>
    obtain ⟨x,hx,rfl⟩ := ih
    exact ⟨x,.altLeft hx,rfl⟩
  | altRight hp ih =>
    obtain ⟨x,hx,rfl⟩ := ih
    exact ⟨x,.altRight hx,rfl⟩
  | starNil p => exact ⟨.nil,.starNil p,rfl⟩
  | starCons hp hq ihp ihq =>
    obtain ⟨x,hx,rfl⟩ := ihp
    obtain ⟨y,hy,rfl⟩ := ihq
    exact ⟨.seq x y,.starCons hx hy,rfl⟩
  | capture hp ih =>
    obtain ⟨x,hx,rfl⟩ := ih
    exact ⟨.cap x,.capture hx,rfl⟩
  | reference => exact ⟨.recall,.reference,rfl⟩

end PlanOf

theorem matches_iff_plan (p : Expr α) (w : Word α) (k : Nat) :
    MatchesWithin p w k ↔
      ∃ q, PlanOf p q ∧ q.refs≤k ∧ (q.eval []).1=w := by
  constructor
  · rintro ⟨es,s,ht,hr,hb,ho,hk⟩
    obtain ⟨q,hq,rfl⟩ := PlanOf.fromTrace ht
    rw [Plan.execute_events] at hr
    simp only [Option.some.injEq] at hr
    subst s
    exact ⟨q,hq,by simpa [State.initial,State.appendText] using hk,
      by simpa [State.initial,State.appendText] using ho⟩
  · rintro ⟨q,hq,hk,hw⟩
    refine ⟨q.events,_,hq.trace,q.execute_events (State.initial []),?_,?_,?_⟩
    · simp [State.initial,State.appendText]
    · simpa [State.initial,State.appendText] using hw
    · simpa [State.initial,State.appendText] using hk

/-- Exact pruning relation from a source expression, with no weakening
    of its accepted language. The output plan can have fewer captures. -/
def PrunedOf (p : Expr α) (liveIn liveOut : Bool) (q : Plan α) : Prop :=
  ∃ x, PlanOf p x ∧ x.prune liveOut=(liveIn,q)

theorem matches_iff_pruned (p : Expr α) (w : Word α) (k : Nat) :
    MatchesWithin p w k ↔
      ∃ live q, PrunedOf p live false q ∧ q.refs≤k ∧ q.caps≤k ∧ (q.eval []).1=w := by
  rw [matches_iff_plan]
  constructor
  · rintro ⟨x,hx,hr,hw⟩
    refine ⟨(x.prune false).1,(x.prune false).2,⟨x,hx,by cases x.prune false; rfl⟩,?_,?_,?_⟩
    · rw [Plan.prune_refs]
      exact hr
    · exact Nat.le_trans x.prune_no_more_caps hr
    · exact (x.prune_eval false [] [] (fun _=>rfl)).1.symm.trans hw
  · rintro ⟨live,q,⟨x,hx,hp⟩,hr,hc,hw⟩
    have he : (x.prune false).2=q := congrArg Prod.snd hp
    have href := x.prune_refs false
    rw [he] at href
    refine ⟨x,hx,by rwa [← href],?_⟩
    have heval := (x.prune_eval false [] [] (fun _=>rfl)).1
    rw [he] at heval
    exact heval.trans hw

inductive Control where
  | openCap | closeCap | recall
  deriving Repr, DecidableEq

namespace Plan

def skeleton : Plan α → List Control
  | .nil => []
  | .literal _ => []
  | .recall => [.recall]
  | .seq p q => skeleton p++skeleton q
  | .cap p => [.openCap]++skeleton p++[.closeCap]

theorem skeleton_length (q : Plan α) :
    q.skeleton.length=2*q.caps+q.refs := by
  induction q with
  | nil => rfl
  | literal w => rfl
  | recall => rfl
  | seq p q hp hq =>
    simp only [skeleton,caps,refs,List.length_append,hp,hq,Nat.mul_add]
    omega
  | cap p hp =>
    simp only [skeleton,caps,refs,List.length_append,List.length_cons,List.length_nil,hp,Nat.mul_add]
    omega

end Plan

/-- Explicit finite enumeration of possible control skeletons, without
    any enumeration of the arbitrary text inside their regular regions. -/
def skeletons : Nat → List (List Control)
  | 0 => [[]]
  | k+1 =>
    [] :: ((skeletons k).map (Control.openCap::·) ++
      (skeletons k).map (Control.closeCap::·) ++
      (skeletons k).map (Control.recall::·))

theorem skeletons_complete (k : Nat) (xs : List Control) (h : xs.length≤k) :
    xs∈skeletons k := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [skeletons]
    | cons x xs => simp at h
  | succ k ih =>
    cases xs with
    | nil => simp [skeletons]
    | cons x xs =>
      have hh : xs.length≤k := by simp only [List.length_cons] at h; omega
      have hm := ih xs hh
      change x::xs ∈ [] :: ((skeletons k).map (Control.openCap::·) ++
        (skeletons k).map (Control.closeCap::·) ++
        (skeletons k).map (Control.recall::·))
      apply List.mem_cons.mpr
      apply Or.inr
      cases x
      · simp [hm]
      · simp [hm]
      · simp [hm]

/-- At most two recalls imply at most six control markers. This theorem
    gives an exact finite skeleton partition of the original language.
    It does not yet prove the languages of the intervening factors regular. -/
theorem matches_iff_skeletons (p : Expr α) (w : Word α) (k : Nat) :
    MatchesWithin p w k ↔
      ∃ sk ∈ skeletons (3*k), ∃ live q, PrunedOf p live false q ∧
        q.refs≤k ∧ q.caps≤k ∧ q.skeleton=sk ∧ (q.eval []).1=w := by
  rw [matches_iff_pruned]
  constructor
  · rintro ⟨live,q,hq,hr,hc,hw⟩
    have h : q.skeleton.length≤3*k := by rw [Plan.skeleton_length]; omega
    exact ⟨q.skeleton,skeletons_complete _ _ h,live,q,hq,hr,hc,rfl,hw⟩
  · rintro ⟨sk,hsk,live,q,hq,hr,hc,he,hw⟩
    exact ⟨live,q,hq,hr,hc,hw⟩

end REWB
