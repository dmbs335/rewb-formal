import REWB.P1Cubic
namespace ShortSourceRegression
open REWB REWB.Periodic REWB.RunGeometry

def one (c : Fin 2) : DFA (Fin 2) :=
  ⟨3,⟨0,by decide⟩,
    fun q a=>if q.val=0 ∧ a=c then ⟨1,by decide⟩ else ⟨2,by decide⟩,
    fun q=>decide (q.val=1)⟩

def eps : DFA (Fin 2) :=
  ⟨2,⟨0,by decide⟩,fun _ _=>⟨1,by decide⟩,fun q=>decide (q.val=0)⟩

def P : SevenDFA (Fin 2) := ⟨one 1,one 0,one 1,eps,one 0,eps,eps⟩
def text : Array (Fin 2) := #[1,0,1,0,0,0,0]
def f (i : Nat) : Fin 2 := text[i]?.getD 0
def R : Bounds := ⟨3,7,1⟩

theorem run_mem : R∈SmallPeriodRuns.cubic f 7 1 := by decide

def witness : P1ShortBranch.ShortWitness P f 7 R :=
  ⟨0,⟨0,1,2,2,4⟩,1,by unfold P1Target.Witness DFA.accepts; decide,by decide,by decide,
    by decide,by decide,by unfold DFA.accepts; decide,by unfold DFA.accepts; decide⟩

example : (P1ShortBranch.solve P f 7 1).answer=true :=
  P1ShortBranch.solve_complete P f 7 1 R
    ((SmallPeriodRuns.cubic_mem f 7 1 R).mp run_mem).1 (by decide) (by decide) witness

example : MatchesWithin P.nested1 (segment f 0 7) 2 :=
  P1ShortBranch.solve_sound P f 7 1
    (P1ShortBranch.solve_complete P f 7 1 R
      ((SmallPeriodRuns.cubic_mem f 7 1 R).mp run_mem).1 (by decide) (by decide) witness)

end ShortSourceRegression
