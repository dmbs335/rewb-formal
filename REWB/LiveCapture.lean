import REWB.BlockMatcher

/-! A concrete derivation plan records the selected regular words, choices
    and capture scopes. Backward liveness removes every capture whose final
    assignment is not observed by a later recall. This is a per-derivation
    reduction, not yet a finite union of fixed DFA normal forms. -/
namespace REWB

inductive Plan (α : Type) where
  | nil : Plan α
  | literal : Word α → Plan α
  | recall : Plan α
  | seq : Plan α → Plan α → Plan α
  | cap : Plan α → Plan α
  deriving Repr

namespace Plan
variable {α : Type}

def events : Plan α → List (Event α)
  | .nil => []
  | .literal w => [.emit w]
  | .recall => [.recall]
  | .seq p q => events p ++ events q
  | .cap p => [.openCap] ++ events p ++ [.closeCap]

def refs : Plan α → Nat
  | .nil => 0
  | .literal _ => 0
  | .recall => 1
  | .seq p q => refs p + refs q
  | .cap p => refs p

def caps : Plan α → Nat
  | .nil => 0
  | .literal _ => 0
  | .recall => 0
  | .seq p q => caps p + caps q
  | .cap p => caps p + 1

/-- Evaluate the output and the last closed register relative to an
    arbitrary incoming register. Open captures are accounted for by
    concatenation, since each capture receives all output of its body. -/
def eval : Plan α → Word α → Word α × Word α
  | .nil, r => ([],r)
  | .literal w, r => (w,r)
  | .recall, r => (r,r)
  | .seq p q, r =>
    let a := eval p r
    let b := eval q a.2
    (a.1 ++ b.1,b.2)
  | .cap p, r =>
    let a := eval p r
    (a.1,a.1)

theorem refs_events (p : Plan α) : Event.refCount p.events=p.refs := by
  induction p with
  | nil => rfl
  | literal w => rfl
  | recall => rfl
  | seq p q hp hq =>
    simp only [events,refs,Event.refCount_append,hp,hq]
  | cap p hp =>
    simp [events,refs,Event.refCount_append,Event.refCount,Event.refCost,hp]

private theorem map_append_frames (fs : List (Word α)) (u v : Word α) :
    (fs.map (fun f=>f++u)).map (fun f=>f++v) =
      fs.map (fun f=>f++(u++v)) := by
  simp only [List.map_map,Function.comp_def,List.append_assoc]

/-- The plan evaluator agrees with the operational execution from any
    state, not just the initial state. This also proves preservation of
    all enclosing capture frames. -/
theorem execute_events (p : Plan α) (s : State α) :
    State.execute s p.events =
      some { s.appendText (p.eval s.stored).1 with
        stored := (p.eval s.stored).2, uses := s.uses+p.refs } := by
  induction p generalizing s with
  | nil => simp [events,eval,refs,State.execute,State.appendText]
  | literal w =>
    simp [events,eval,refs,State.execute,State.step,State.appendText]
  | recall => rfl
  | seq p q hp hq =>
    rw [events,State.execute_append,hp]
    simp only [Option.bind]
    rw [hq]
    simp only [eval,refs,State.appendText,map_append_frames,List.append_assoc,Nat.add_assoc]
  | cap p hp =>
    change State.execute { s with frames := []::s.frames } (p.events ++ [.closeCap])=_
    rw [State.execute_append,hp]
    simp [State.execute,State.step,State.appendText,eval,refs]

/-- liveOut asks whether the final register will be observed by the
    continuation. The first projection is the incoming register liveness.
    A capture always kills the body's outgoing register at its own close. -/
def prune : Plan α → Bool → Bool × Plan α
  | .nil, live => (live,.nil)
  | .literal w, live => (live,.literal w)
  | .recall, _ => (true,.recall)
  | .seq p q, live =>
    let b := prune q live
    let a := prune p b.1
    (a.1,.seq a.2 b.2)
  | .cap p, live =>
    let a := prune p false
    (a.1,if live then .cap a.2 else a.2)

/-- The transformed plan emits the same word. Its outgoing register is
    required to agree only if the continuation needs it. Inputs can differ
    exactly when neither computation observes the incoming register. -/
theorem prune_eval (p : Plan α) (live : Bool) (r s : Word α)
    (h : (p.prune live).1=true → r=s) :
    (p.eval r).1=((p.prune live).2.eval s).1 ∧
      (live=true → (p.eval r).2=((p.prune live).2.eval s).2) := by
  induction p generalizing live r s with
  | nil => exact ⟨rfl,h⟩
  | literal w => exact ⟨rfl,h⟩
  | recall =>
    have he := h rfl
    subst s
    exact ⟨rfl,fun _=>rfl⟩
  | seq p q hp hq =>
    let b := q.prune live
    let a := p.prune b.1
    have ha := hp b.1 r s (show a.1=true → r=s from h)
    have hb := hq live (p.eval r).2 (a.2.eval s).2 ha.2
    change (p.eval r).1 ++ (q.eval (p.eval r).2).1 =
      (a.2.eval s).1 ++ (b.2.eval (a.2.eval s).2).1 ∧
        (live=true → (q.eval (p.eval r).2).2=(b.2.eval (a.2.eval s).2).2)
    exact ⟨by rw [ha.1,hb.1],hb.2⟩
  | cap p hp =>
    have ha := hp false r s (show (p.prune false).1=true → r=s from h)
    cases live
    · change (p.eval r).1=((p.prune false).2.eval s).1 ∧
        (false=true → (p.eval r).1=((p.prune false).2.eval s).2)
      exact ⟨ha.1,by intro hh; contradiction⟩
    · change (p.eval r).1=((p.prune false).2.eval s).1 ∧
        (true=true → (p.eval r).1=((p.prune false).2.eval s).1)
      exact ⟨ha.1,fun _=>ha.1⟩

theorem prune_refs (p : Plan α) (live : Bool) :
    (p.prune live).2.refs=p.refs := by
  induction p generalizing live with
  | nil => rfl
  | literal w => rfl
  | recall => rfl
  | seq p q hp hq =>
    change (p.prune (q.prune live).1).2.refs+(q.prune live).2.refs=p.refs+q.refs
    rw [hp,hq]
  | cap p hp =>
    cases live <;> simpa only [prune,if_true,if_false,Bool.false_eq_true,refs] using hp false

def credit (b : Bool) : Nat := if b then 1 else 0

/-- A retained capture spends one unit of outgoing liveness. A recall
    supplies at most one unit of incoming liveness. Across sequential
    composition the intermediate credit cancels exactly. -/
theorem prune_budget (p : Plan α) (live : Bool) :
    (p.prune live).2.caps+credit (p.prune live).1 ≤ p.refs+credit live := by
  induction p generalizing live with
  | nil => exact Nat.le_refl _
  | literal w =>
    change 0+credit live≤0+credit live
    exact Nat.le_refl _
  | recall =>
    cases live <;> simp [prune,caps,refs,credit]
  | seq p q hp hq =>
    have ha := hp (q.prune live).1
    have hb := hq live
    change (p.prune (q.prune live).1).2.caps+(q.prune live).2.caps+
      credit (p.prune (q.prune live).1).1 ≤ p.refs+q.refs+credit live
    omega
  | cap p hp =>
    have hh := hp false
    cases live
    · change (p.prune false).2.caps+credit (p.prune false).1≤p.refs+0
      exact hh
    · change (p.prune false).2.caps+1+credit (p.prune false).1≤p.refs+1
      change (p.prune false).2.caps+credit (p.prune false).1≤p.refs+0 at hh
      omega

theorem prune_no_more_caps (p : Plan α) :
    (p.prune false).2.caps≤p.refs := by
  have h := prune_budget p false
  change (p.prune false).2.caps+credit (p.prune false).1≤p.refs+0 at h
  omega

end Plan

namespace TraceOf
variable {α : Type}

/-- Resolve a derivation into a plan, erasing alternative and star syntax
    but keeping their chosen finite execution structure. -/
theorem exists_plan {p : Expr α} {es : List (Event α)} (h : TraceOf p es) :
    ∃ q : Plan α, q.events=es := by
  induction h with
  | atom d w ha => exact ⟨.literal w,rfl⟩
  | seq hp hq ihp ihq =>
    obtain ⟨p,rfl⟩ := ihp
    obtain ⟨q,rfl⟩ := ihq
    exact ⟨.seq p q,rfl⟩
  | altLeft hp ih => exact ih
  | altRight hq ih => exact ih
  | starNil p =>
    exact ⟨.nil,rfl⟩
  | starCons hp hq ihp ihq =>
    obtain ⟨p,rfl⟩ := ihp
    obtain ⟨q,rfl⟩ := ihq
    exact ⟨.seq p q,rfl⟩
  | capture hp ih =>
    obtain ⟨p,rfl⟩ := ih
    exact ⟨.cap p,rfl⟩
  | reference => exact ⟨.recall,rfl⟩

end TraceOf

/-- Every bounded-use successful trace has an equivalent concrete plan
    with at most k captures and k recalls. This is only the per-trace
    direction: it is not a compiler generating regular factor languages. -/
theorem exists_pruned_plan {α : Type} (p : Expr α) (w : Word α) (k : Nat)
    (h : MatchesWithin p w k) :
    ∃ q : Plan α, q.refs≤k ∧ q.caps≤k ∧ (q.eval []).1=w := by
  rcases h with ⟨es,st,ht,hr,hb,ho,hk⟩
  obtain ⟨q,he⟩ := ht.exists_plan
  have hu := State.execute_uses es (State.initial []) st hr
  rw [← he,Plan.refs_events] at hu
  have hu' : st.uses=q.refs := by simpa [State.initial] using hu
  have hq : q.refs≤k := by rwa [← hu']
  rw [← he,Plan.execute_events] at hr
  have hw : (q.eval []).1=w := by
    simp only [Option.some.injEq] at hr
    rw [← hr] at ho
    simpa [State.initial,State.appendText] using ho
  refine ⟨(q.prune false).2,?_,Nat.le_trans q.prune_no_more_caps hq,?_⟩
  · rw [Plan.prune_refs]
    exact hq
  · exact (q.prune_eval false [] [] (fun _=>rfl)).1.symm.trans hw

end REWB
