import REWB.MaskedPeriodicContexts
import REWB.MaskedPeriodicGeometry

/-! One complete arithmetic-family query at a supplied source phase.
    The cut index and immutable-mask array are shared prepared inputs.
    Whole-period/fragment maps come from actual range queries; the common
    modulus is computed once by `preparePattern`. The external tail map
    is likewise shared across the run. This closes the local three-case
    compiler, not periodic-run discovery or the global masked index.
-/
namespace REWB.MaskedPeriodic
open REWB.MaskedFiniteAction.Maps REWB.MaskedCut REWB.MaskedCut.DFAIndex REWB.Spec
variable {α : Type}

def joinAnswers (a b : MaskedProgression.Answer) : MaskedProgression.Answer :=
  ⟨a.answer || b.answer,a.slots+b.slots,a.arithmetic+b.arithmetic+1⟩

def phaseQuery (b c e : DFA α) (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (idx : Index.Tree (jointEnum b c e)) (tail : Map e.stateCount)
    (start eta q N : Nat) (counts : Array Nat) (base s : Nat) : IndexedAnswer :=
  let maps := contexts b c e idx start eta q tail
  match maps.period,maps.after with
  | some period,some after =>
    let zero := queryBranch (fromTuple b c e period (wordTuple b c e [] [] []) after)
      .zero N counts base q s prepared.K
    let interior := queryInterior b c e idx start q period after N counts base s prepared.K
    let ending := queryEnding b c e idx start eta q period tail N counts base s prepared.K
    ⟨joinAnswers zero (joinAnswers interior.result ending.result),
      maps.products+interior.products+ending.products,maps.visits+interior.visits+ending.visits⟩
  | _,_ => ⟨⟨false,0,1⟩,maps.products,maps.visits⟩

def PhaseWitness (b c e : DFA α) (w tail : Word α) (start eta q N : Nat)
    (mask : Array Bool) (base len s : Nat) : Prop :=
  (∃ a k,WordFamily b c e (slice w start (start+q)) [] [] []
    (slice w start (start+eta)++tail) .zero N a k ∧ Marked mask base len q s k) ∨
  (∃ rho a k,0<rho ∧ rho<q ∧
    WordFamily b c e (slice w start (start+q)) (slice w start (start+rho))
      (slice w (start+rho) (start+q)) (slice w (start+rho) (start+q))
      (slice w start (start+eta)++tail) .interior N a k ∧ Marked mask base len q s k) ∨
  (∃ rho a k,0<rho ∧ rho≤eta ∧
    WordFamily b c e (slice w start (start+q)) (slice w start (start+rho))
      (slice w (start+rho) (start+q)) (slice w (start+rho) (start+eta))
      tail .ending N a k ∧ Marked mask base len q s k)

theorem phaseQuery_correct (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w tail : Word α) (start eta q N : Nat) (mask : Array Bool) (base len s : Nat)
    (hq : 0<q) (he : eta<q) (hn : start+q≤w.length) :
    (phaseQuery b c e prepared (DFAIndex.build b c e w).1 (wordMap e tail) start eta q N
      (MaskedProgression.build mask base len (prepared.K*q)).counts base s).result.answer=true ↔
        PhaseWitness b c e w tail start eta q N mask base len s := by
  have hm := contexts_value b c e w tail start eta q (Nat.le_of_lt he) hn
  simp only [phaseQuery]
  rw [hm.1,hm.2]
  simp only [joinAnswers,Bool.or_eq_true,prepared.exact]
  rw [queryBranch_correct _ _ _ _ _ _ _ _ hq,
    queryInterior_correct b c e w (slice w start (start+eta)++tail) start q N
      mask base len s hq hn,
    queryEnding_correct b c e w tail start eta q N mask base len s hq (Nat.le_of_lt he) hn]
  simp only [fromTuple_words,PhaseWitness,Marked]

end REWB.MaskedPeriodic
