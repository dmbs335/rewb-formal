import REWB.LiveCompiler

/-! Interpretation of regular trace codes. Literal words are split into
    individual characters, while the retained control markers keep their
    original last-closed-capture semantics. -/
namespace REWB
variable {α : Type}

def decodeSymbol : MarkedSymbol α → Event α
  | .inl c => .emit [c]
  | .inr .openCap => .openCap
  | .inr .closeCap => .closeCap
  | .inr .recall => .recall

def controlOf : MarkedSymbol α → Option Control
  | .inl _ => none
  | .inr c => some c

theorem appendText_append (s : State α) (x y : Word α) :
    (s.appendText x).appendText y=s.appendText (x++y) := by
  cases s
  simp only [State.appendText,List.append_assoc,List.map_map,Function.comp_def]

theorem execute_characters (w : Word α) (s : State α) :
    State.execute s (w.map (fun c=>Event.emit [c]))=some (s.appendText w) := by
  induction w generalizing s with
  | nil =>
    cases s
    simp [State.execute,State.appendText]
  | cons c cs ih =>
    change State.execute (s.appendText [c]) (cs.map (fun c=>Event.emit [c]))=_
    rw [ih,appendText_append]
    rfl

theorem decode_literals (w : Word α) :
    (w.map (Sum.inl : α→MarkedSymbol α)).map decodeSymbol=w.map (fun c=>Event.emit [c]) := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
    change Event.emit [c]::(cs.map (Sum.inl : α→MarkedSymbol α)).map decodeSymbol =
      Event.emit [c]::cs.map (fun c=>Event.emit [c])
    rw [ih]

namespace Plan

theorem code_exec (q : Plan α) (s : State α) :
    State.execute s (q.code.map decodeSymbol)=State.execute s q.events := by
  induction q generalizing s with
  | nil => rfl
  | literal w =>
    rw [code,decode_literals,execute_characters]
    rfl
  | recall => rfl
  | seq p q hp hq =>
    simp only [code,events,List.map_append,State.execute_append,hp,hq]
  | cap p hp =>
    simp only [code,events,List.map_append,List.map_cons,List.map_nil,decodeSymbol,
      State.execute_append,hp]

private theorem filter_literals (w : Word α) :
    (w.map (Sum.inl : α→MarkedSymbol α)).filterMap controlOf=[] := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
    change (cs.map (Sum.inl : α→MarkedSymbol α)).filterMap controlOf=[]
    exact ih

theorem code_controls (q : Plan α) :
    q.code.filterMap controlOf=q.skeleton := by
  induction q with
  | nil => rfl
  | literal w => exact filter_literals w
  | recall => rfl
  | seq p q hp hq =>
    simp only [code,skeleton,List.filterMap_append,hp,hq]
  | cap p hp =>
    simp only [code,skeleton,List.filterMap_append,List.filterMap_cons,controlOf,
      List.filterMap_nil,hp]

end Plan

namespace LiveCompiler

def CodeMatches (z : Word (MarkedSymbol α)) (w : Word α) (k : Nat) : Prop :=
  ∃ s, State.execute (State.initial []) (z.map decodeSymbol)=some s ∧
    s.frames=[] ∧ s.output=w ∧ s.uses≤k

theorem codeMatches_plan (q : Plan α) (w : Word α) (k : Nat) :
    CodeMatches q.code w k ↔ q.refs≤k ∧ (q.eval []).1=w := by
  unfold CodeMatches
  rw [Plan.code_exec,Plan.execute_events]
  constructor
  · rintro ⟨s,hs,hb,ho,hk⟩
    simp only [Option.some.injEq] at hs
    subst s
    exact ⟨by simpa [State.initial,State.appendText] using hk,
      by simpa [State.initial,State.appendText] using ho⟩
  · rintro ⟨hk,hw⟩
    refine ⟨_,rfl,?_,?_,?_⟩
    · simp [State.initial,State.appendText]
    · simpa [State.initial,State.appendText] using hw
    · simpa [State.initial,State.appendText] using hk

/-- A regular language of trace codes, followed by the original register
    interpreter, is exactly the bounded-use matching language. The control
    budget is part of the witness, not a restriction on the original
    number of syntactic captures. -/
theorem match_compiled (p : Expr α) (w : Word α) (k : Nat) :
    MatchesWithin p w k ↔
      ∃ z, denote (compiled p) z ∧ CodeMatches z w k ∧
        (z.filterMap controlOf).length≤3*k := by
  rw [matches_iff_plan]
  constructor
  · rintro ⟨x,hx,hr,hw⟩
    let q := (x.prune false).2
    have href : q.refs≤k := by change (x.prune false).2.refs≤k; rwa [Plan.prune_refs]
    have hcap : q.caps≤k := Nat.le_trans x.prune_no_more_caps hr
    have heval : (q.eval []).1=w := (x.prune_eval false [] [] (fun _=>rfl)).1.symm.trans hw
    refine ⟨q.code,(compiled_correct p q.code).mpr
      ⟨(x.prune false).1,x,hx,rfl,rfl⟩,
      (codeMatches_plan q w k).mpr ⟨href,heval⟩,?_⟩
    rw [Plan.code_controls,Plan.skeleton_length]
    omega
  · rintro ⟨z,hz,hm,hc⟩
    obtain ⟨a,x,hx,ha,hcode⟩ := (compiled_correct p z).mp hz
    rw [← hcode,codeMatches_plan] at hm
    have hr := hm.1
    rw [Plan.prune_refs] at hr
    exact ⟨x,hx,hr,(x.prune_eval false [] [] (fun _=>rfl)).1.trans hm.2⟩

end LiveCompiler
end REWB
