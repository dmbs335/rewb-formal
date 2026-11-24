import REWB.Semantics

/-! Basic invariants for arbitrary expressions, including star and unused
    captures. These are prerequisites for the supplier-selection compiler. -/
namespace REWB
variable {α : Type}

namespace TraceOf

/-- Any syntactically generated trace executes and restores the original
    stack depth, even when there were already open captures. -/
theorem executes_balanced {p : Expr α} {es : List (Event α)}
    (h : TraceOf p es) (s : State α) :
    ∃ t, State.execute s es = some t ∧ t.frames.length = s.frames.length := by
  induction h generalizing s with
  | atom d w ha =>
    exact ⟨s.appendText w,rfl,by simp [State.appendText]⟩
  | seq hp hq ihp ihq =>
    obtain ⟨t,ht,hlen⟩ := ihp s
    obtain ⟨u,hu,hlen'⟩ := ihq t
    exact ⟨u,by simp [State.execute_append, ht, hu],
      hlen'.trans hlen⟩
  | altLeft hp ih => exact ih s
  | altRight hq ih => exact ih s
  | starNil p => exact ⟨s,rfl,rfl⟩
  | starCons hp hq ihp ihq =>
    obtain ⟨t,ht,hlen⟩ := ihp s
    obtain ⟨u,hu,hlen'⟩ := ihq t
    exact ⟨u,by simp [State.execute_append, ht, hu],
      hlen'.trans hlen⟩
  | capture hp ih =>
    let entered : State α := { s with frames := [] :: s.frames }
    have hopen : State.execute s [.openCap] = some entered := rfl
    obtain ⟨t,ht,hlen⟩ := ih entered
    cases hf : t.frames with
    | nil => simp [entered, hf] at hlen
    | cons f fs =>
      let exited : State α := { t with stored := f, frames := fs }
      have hclose : State.execute t [.closeCap] = some exited := by
        simp [State.execute, State.step, hf, exited]
      refine ⟨exited, ?_, ?_⟩
      · change State.execute entered (_ ++ [.closeCap]) = some exited
        rw [State.execute_append]
        simp only [List.nil_append, ht, Option.bind]
        exact hclose
      · have hh : fs.length + 1 = s.frames.length + 1 := by
          simpa [entered, hf] using hlen
        change fs.length = s.frames.length
        omega
  | reference =>
    exact ⟨{ s.appendText s.stored with uses := s.uses + 1 }, rfl,
      by simp [State.appendText]⟩

theorem executes_from_empty {p : Expr α} {es : List (Event α)}
    (h : TraceOf p es) :
    ∃ t, State.execute (State.initial []) es = some t ∧ t.frames = [] := by
  obtain ⟨t,ht,hlen⟩ := h.executes_balanced (State.initial [])
  have hz : t.frames.length = 0 := by simpa [State.initial] using hlen
  refine ⟨t,ht,?_⟩
  cases hf : t.frames with
  | nil => rfl
  | cons f fs => simp [hf] at hz

end TraceOf

/-- The dynamic-use promise can be expressed on generated event traces.
    This is not yet a finite automaton compiler for those traces. -/
theorem isKUse_iff_traceCount (p : Expr α) (k : Nat) :
    IsKUse p k ↔ ∀ es, TraceOf p es → Event.refCount es ≤ k := by
  constructor
  · intro hk es ht
    obtain ⟨t,hr,hb⟩ := ht.executes_from_empty
    have hc := hk es t ht hr hb
    have hu := State.execute_uses es (State.initial []) t hr
    simp [State.initial] at hu
    omega
  · intro hk es t ht hr hb
    have hc := hk es ht
    have hu := State.execute_uses es (State.initial []) t hr
    simp [State.initial] at hu
    omega

namespace Event

def literalText : List (Event α) → Word α
  | [] => []
  | .emit w :: es => w ++ literalText es
  | _ :: es => literalText es

theorem zeroCons {e : Event α} {es : List (Event α)}
    (h : refCount (e :: es) = 0) :
    e.refCost = 0 ∧ refCount es = 0 := by
  simp only [refCount] at h
  omega

end Event

namespace State

/-- If a successful trace has no recalls, all capture bookkeeping can be
    erased when considering its emitted text. -/
theorem output_without_recall (es : List (Event α)) (s t : State α)
    (h : execute s es = some t) (hz : Event.refCount es = 0) :
    t.output = s.output ++ Event.literalText es := by
  induction es generalizing s with
  | nil =>
    simp only [execute, Option.some.injEq] at h
    subst t
    simp [Event.literalText]
  | cons e es ih =>
    obtain ⟨he,hes⟩ := Event.zeroCons hz
    cases hs : s.step e with
    | none => simp [execute, hs] at h
    | some mid =>
      have hr : execute mid es = some t := by simpa [execute, hs] using h
      have hi := ih mid hr hes
      cases e with
      | emit w =>
        have hm : s.appendText w = mid := by simpa [step] using hs
        subst mid
        simpa [Event.literalText, appendText, List.append_assoc] using hi
      | openCap =>
        have hm : { s with frames := [] :: s.frames } = mid := by
          simpa [step] using hs
        subst mid
        simpa [Event.literalText] using hi
      | closeCap =>
        cases hf : s.frames with
        | nil => simp [step, hf] at hs
        | cons f fs =>
          have hm : { s with stored := f, frames := fs } = mid := by
            simpa [step, hf] using hs
          subst mid
          simpa [Event.literalText] using hi
      | recall => simp [Event.refCost] at he

end State
end REWB
