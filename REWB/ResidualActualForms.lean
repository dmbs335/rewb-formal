import REWB.ResidualActualDispatch
import REWB.CompleteNormalization

/-! Two concrete fixed-pattern reductions. The epsilon language is a
constructed finite automaton. Same-value and one-reference cases execute
the actual nested dispatchers, including the empty captured word. -/
namespace REWB.ResidualActual
variable {σ : Nat}

def epsilon : DFA (Fin σ) :=
  (RegularDFA.epsilon : RegularDFA.Machine (Fin σ)).toDFA

theorem epsilon_accepts (w : Word (Fin σ)) : (epsilon : DFA (Fin σ)).accepts w ↔ w=[] := by
  rw [epsilon,RegularDFA.Machine.toDFA_correct,RegularDFA.epsilon_correct]

def samePattern (P : FiveDFA (Fin σ)) : SevenDFA (Fin σ) :=
  ⟨P.A,P.B,P.C,epsilon,epsilon,P.D,P.E⟩

theorem samePattern_correct (P : FiveDFA (Fin σ)) (w : Word (Fin σ)) :
    MatchesWithin (samePattern P).nested1 w 2 ↔ MatchesWithin P.sameValue w 2 := by
  rw [Witness.nested1_iff,Witness.same_iff]
  simp only [samePattern,epsilon_accepts]
  constructor
  · rintro ⟨a,u,c,d,f,g,h,ha,hu,hc,hd,hf,hg,hh,hw⟩
    subst d
    subst f
    exact ⟨a,u,c,g,h,ha,hu,hc,hg,hh,by simpa only [List.nil_append,List.append_nil] using hw⟩
  · rintro ⟨a,u,c,g,h,ha,hu,hc,hg,hh,hw⟩
    exact ⟨a,u,c,[],[],g,h,ha,hu,hc,rfl,rfl,hg,hh,by simpa only [List.nil_append,List.append_nil] using hw⟩

def oncePattern (A B C E : DFA (Fin σ)) : SevenDFA (Fin σ) :=
  ⟨A,B,epsilon,epsilon,epsilon,C,E⟩

theorem oncePattern_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) :
    MatchesWithin (oncePattern A B C E).nested2 w 2 ↔
      MatchesWithin (CompleteNormalization.once A B C E) w 2 := by
  rw [Witness.nested2_iff,CompleteNormalization.once_matches]
  simp only [oncePattern,epsilon_accepts]
  constructor
  · rintro ⟨a,b,u,d,f,g,h,ha,hb,hu,hd,hf,hg,hh,hw⟩
    subst u
    subst d
    subst f
    exact ⟨a,b,g,h,ha,hb,hg,hh,by simpa only [List.append_nil] using hw⟩
  · rintro ⟨a,b,g,h,ha,hb,hg,hh,hw⟩
    exact ⟨a,b,[],[],[],g,h,ha,hb,rfl,rfl,rfl,hg,hh,by simpa only [List.append_nil] using hw⟩

def same (P : FiveDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : P1.Execution :=
  P1.auto (samePattern P) text fallback

theorem same_correct (P : FiveDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (same P text fallback).answer=true ↔ MatchesWithin P.sameValue text.toList 2 :=
  (P1.auto_correct (samePattern P) text fallback).trans (samePattern_correct P text.toList)

def once (A B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : P2.Execution :=
  P2.auto (oncePattern A B C E) text fallback

theorem once_correct (A B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (once A B C E text fallback).answer=true ↔
      MatchesWithin (CompleteNormalization.once A B C E) text.toList 2 :=
  (P2.auto_correct (oncePattern A B C E) text fallback).trans (oncePattern_correct A B C E text.toList)

end REWB.ResidualActual
