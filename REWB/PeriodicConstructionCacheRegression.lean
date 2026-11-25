import REWB.PeriodicConstructionCacheCost

/-! Small kernel regressions include zero-period construction overhead,
noninjective transitions, equality at the final prefix, and empty contexts. -/
namespace REWB.PeriodicConstruction.Cache.Regression

def universal : DFA Bool :=
  ⟨1,0,fun _ _=>0,fun _=>true⟩

def seen : DFA Bool :=
  ⟨2,0,fun v x=>if x then 1 else v,fun v=>decide (v=1)⟩

def last : DFA Bool :=
  ⟨2,0,fun _ x=>if x then 1 else 0,fun v=>decide (v=1)⟩

def parity : DFA Bool :=
  ⟨2,0,fun v x=>if x then (if v=0 then 1 else 0) else v,fun v=>decide (v=0)⟩

def read (text : Array Bool) (i : Nat) : Bool := text[i]?.getD false

def all : SevenDFA Bool :=
  ⟨universal,universal,universal,universal,universal,universal,universal⟩

def mixed : SevenDFA Bool :=
  ⟨seen,last,parity,seen,universal,last,parity⟩

theorem zero_transitions (d : DFA α) (s : Nat→α) :
    transitions d s 0=((#[],0),6) := rfl

theorem zero_equality [DecidableEq α] (s : Nat→α) :
    equality s 0=((#[],0),6) := rfl

theorem zero_preparation [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (I : BoundaryContexts.Index P) (lo hi : Nat) :
    (prepareAt P s 0 I lo hi).2=72 := by
  rw [prepareAt_work]
  simp [prepareAtCost,transitionsCost,equalityCost]

theorem noninjective_row :
    PeriodicCache.lookup seen (transitions seen (read #[false,true,false]) 3).1.1
      0 3 0=some 1 := by decide

theorem final_prefix_comparison :
    PhaseEqualityCache.lookup (equality (read #[true,false,true,false]) 3).1.1
      0 2 2=some true ∧
    PhaseEqualityCache.lookup (equality (read #[true,false,true,false]) 3).1.1
      0 2 3=some false := by decide

theorem empty_contexts :
    (contexts mixed []).1.2=3 ∧
    (contexts mixed []).1.1.prefixes.size=1 ∧
    (contexts mixed []).1.1.suffixes.size=1 := by decide

end REWB.PeriodicConstruction.Cache.Regression
