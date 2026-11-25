import REWB.MaskedTraversalPositiveCoverage
import REWB.MaskedTraversalAggregateCollect

/-! Executor-facing coverage invariants. Exhaustion is derived for an
actual Collect transaction and persists when later source reports extend
the deletion history. Whole-plan exhaustion then gives exact original
matching semantics. The plan executor still has to establish this
invariant from its concrete repair and Collect calls; it is not a supplied
runtime query or answer oracle. -/
namespace REWB.MaskedTraversalPositiveCoverage
open REWB.Spec REWB.MaskedCluster REWB.MaskedProgression REWB.MaskedTraversalDriver
open REWB.MaskedTraversalEdge REWB.MaskedTraversalComplete REWB.MaskedRunDiscovery
open REWB.MaskedTraversalAggregate REWB.MaskedTraversalAggregate.Cells REWB.MaskedFiniteAction
variable {α : Type} {σ h : Nat}

def BandExhausted (B C E : DFA α) (w : Word α) (source target : Array Bool)
    (capacity : Nat) (removed : List Nat) (b : Band h) : Prop :=
  ∀p,¬BandGood B C E w b.snapshot capacity b.lo b.hi source removed target p

def Exhausted (B C E : DFA α) (w : Word α) (source target : Array Bool)
    (capacity : Nat) (removed : List Nat) (plan : MaskedTraversalDriver.Plan h) : Prop :=
  ∀b,plan.HasBand b→BandExhausted B C E w source target capacity removed b

theorem currentBit_antitone (source : Array Bool) (removed later : List Nat)
    (included : ∀p,p∈removed→p∈later) (p : Nat)
    (live : Mutable.Batch.currentBit source later p=true) : Mutable.Batch.currentBit source removed p=true := by
  have hs:=(Bool.and_eq_true_iff.mp live).1
  have hn : p∉later := of_decide_eq_true (Bool.and_eq_true_iff.mp live).2
  exact Bool.and_eq_true_iff.mpr ⟨hs,decide_eq_true (fun hp=>hn (included p hp))⟩

theorem bandGood_antitone (B C E : DFA α) (w : Word α)
    (partition : MaskedClusterLeaders.State h) (capacity lo hi : Nat) (source target : Array Bool)
    (removed later : List Nat) (included : ∀p,p∈removed→p∈later) (p : Nat)
    (good : BandGood B C E w partition capacity lo hi source later target p) :
    BandGood B C E w partition capacity lo hi source removed target p :=
  ⟨currentBit_antitone source removed later included p good.1,good.2⟩

theorem BandExhausted.mono {B C E : DFA α} {w : Word α} {source target : Array Bool}
    {capacity : Nat} {removed later : List Nat} {b : Band h}
    (done : BandExhausted B C E w source target capacity removed b)
    (included : ∀p,p∈removed→p∈later) : BandExhausted B C E w source target capacity later b := by
  intro p good
  exact done p (bandGood_antitone B C E w b.snapshot capacity b.lo b.hi source target removed later included p good)

theorem Exhausted.mono {B C E : DFA α} {w : Word α} {source target : Array Bool}
    {capacity : Nat} {removed later : List Nat} {plan : MaskedTraversalDriver.Plan h}
    (done : Exhausted B C E w source target capacity removed plan)
    (included : ∀p,p∈removed→p∈later) : Exhausted B C E w source target capacity later plan := by
  intro b hb
  exact (done b hb).mono included

theorem exhausted_node (B C E : DFA α) (w : Word α) (source target : Array Bool)
    (capacity : Nat) (removed : List Nat) (left right : MaskedTraversalDriver.Plan h) (merged : MaskedTraversalFrontier.Merged h)
    (step : Step h)
    (hl : Exhausted B C E w source target capacity removed left)
    (hr : Exhausted B C E w source target capacity removed right)
    (hs : ∀b,b∈step.lowered.edge.path.bands→BandExhausted B C E w source target capacity removed b) :
    Exhausted B C E w source target capacity removed (.node left right merged step) := by
  intro b hb
  rcases hb with hb|hb|hb
  · exact hs b hb
  · exact hl b hb
  · exact hr b hb

theorem collect_history_includes (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (b : Band h) (capacity : Nat) (tree : BankTree C E h)
    (base old : Nat) (answers : MaskedTraversalAnswers.State) (p : Nat) (hp : p∈answers.history) :
    p∈(Collect.run B C E cut env st b.snapshot capacity tree base b.lo b.hi old answers).answers.history := by
  rw [Collect.run_history]
  exact List.mem_append.mpr (Or.inr hp)

theorem collect_exhausts (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (b : Band h) (capacity base old : Nat) (anchors : Array (Option Nat)) (source : Array Bool)
    (tree : BankTree C E h) (answers : MaskedTraversalAnswers.State) (w : Word α) (fallback : α)
    (geometry : ∀L,b.lo≤L→L≤b.hi→BandGeometry w fallback b.snapshot capacity base old L anchors)
    (hm : Maintained env b.snapshot capacity old w.length anchors source answers.history st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : b.lo≤b.hi) :
    BandExhausted B C E w source env.target capacity
      (Collect.run B C E (Cut.build B C E w) env st b.snapshot capacity tree base b.lo b.hi old answers).answers.history b := by
  intro p
  rw [Collect.run_history]
  exact Reporting.run_exhausts B C E env st b.snapshot capacity base old b.lo b.hi anchors source answers.history tree
    w fallback geometry hm hc he hlength p

theorem collect_preserves (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (b : Band h) (capacity : Nat) (tree : BankTree C E h)
    (base old : Nat) (answers : MaskedTraversalAnswers.State) (w : Word α) (source : Array Bool) (plan : MaskedTraversalDriver.Plan h)
    (done : Exhausted B C E w source env.target capacity answers.history plan) :
    Exhausted B C E w source env.target capacity
      (Collect.run B C E cut env st b.snapshot capacity tree base b.lo b.hi old answers).answers.history plan :=
  done.mono (collect_history_includes B C E cut env st b capacity tree base old answers)

theorem exhausted_no_live (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K h capacity : Nat) (hcap : capacity=2^h) (hn : text.size<2^h)
    (removed : List Nat)
    (history : ∀p,p∈(MaskedTraversalInitial.start B C E text fallback source target K).answers.history→p∈removed)
    (done : Exhausted B C E text.toList source target capacity removed
      (MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan)
    (p : Nat) (matched : maskedStart B C E text.toList (readMask target) p) :
    Mutable.Batch.currentBit source removed p=false := by
  cases live : Mutable.Batch.currentBit source removed p with
  | false=>rfl
  | true=>
    obtain ⟨L,b,_,selected,_,good,_⟩:=surviving_band B C E text fallback source target K removed history h capacity hcap hn p live matched
    exact False.elim (done b selected.1 p good)

theorem answers_correct (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K h capacity : Nat) (hcap : capacity=2^h) (hn : text.size<2^h)
    (answers : MaskedTraversalAnswers.State)
    (valid : MaskedTraversalAnswers.Valid text.size
      (fun p=>readMask source p=true ∧ maskedStart B C E text.toList (readMask target) p) answers)
    (history : ∀p,p∈(MaskedTraversalInitial.start B C E text fallback source target K).answers.history→p∈answers.history)
    (done : Exhausted B C E text.toList source target capacity answers.history
      (MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan) (p : Nat) :
    readMask answers.bits p=true ↔ readMask source p=true ∧ maskedStart B C E text.toList (readMask target) p := by
  constructor
  · intro hit
    exact (valid.sound p ((valid.represented p).mpr hit)).2
  · rintro ⟨sourceBit,matched⟩
    apply (valid.represented p).mp
    by_cases hp : p∈answers.history
    · exact hp
    · have live : Mutable.Batch.currentBit source answers.history p=true :=
        Bool.and_eq_true_iff.mpr ⟨sourceBit,decide_eq_true hp⟩
      have gone:=exhausted_no_live B C E text fallback source target K h capacity hcap hn answers.history history done p matched
      rw [live] at gone
      cases gone

end REWB.MaskedTraversalPositiveCoverage
