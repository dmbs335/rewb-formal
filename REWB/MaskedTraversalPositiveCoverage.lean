import REWB.MaskedTraversalPositiveCoverageGeometry
import REWB.MaskedTraversalInitial

/-! Whole-input positive coverage by the actual suffix driver. A source
still live after the real empty/periodic initialization has a distinct-
owner witness in one unique emitted source/length band. The representative
and complete snapshot geometry are recovered from that actual band.

This is a coverage theorem for the executor's real plan, not an oracle
claim that its bank repairs or reports have already been run. -/
namespace REWB.MaskedTraversalPositiveCoverage
open REWB.Spec REWB.MaskedCluster REWB.MaskedProgression REWB.MaskedTraversalDriver
open REWB.MaskedTraversalEdge REWB.BoundaryTrie REWB.MaskedRunDiscovery
variable {σ h : Nat}

theorem current_unhandled (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (removed : List Nat)
    (history : ∀p,p∈(MaskedTraversalInitial.start B C E text fallback source target K).answers.history→p∈removed)
    (p : Nat) (live : Mutable.Batch.currentBit source removed p=true) :
    readMask source p=true ∧ ¬MaskedTraversalInitial.Handled B C E text fallback target p := by
  have hs:=(Bool.and_eq_true_iff.mp live).1
  have hn : p∉removed := of_decide_eq_true (Bool.and_eq_true_iff.mp live).2
  refine ⟨hs,?_⟩
  intro handled
  exact hn (history p ((MaskedTraversalInitial.start_history B C E text fallback source target K p).mpr ⟨hs,handled⟩))

theorem current_positive (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (removed : List Nat)
    (history : ∀p,p∈(MaskedTraversalInitial.start B C E text fallback source target K).answers.history→p∈removed)
    (p : Nat) (live : Mutable.Batch.currentBit source removed p=true)
    (matched : maskedStart B C E text.toList (readMask target) p) :
    MaskedEmpty.PositiveWitness B C E text.toList target p := by
  have hu:=current_unhandled B C E text fallback source target K removed history p live
  exact ((MaskedEmpty.maskedStart_partition B C E text.toList target p).mp matched).resolve_left
    (fun empty=>hu.2 (Or.inl empty))

theorem current_not_periodic (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (removed : List Nat)
    (history : ∀p,p∈(MaskedTraversalInitial.start B C E text fallback source target K).answers.history→p∈removed)
    (p : Nat) (live : Mutable.Batch.currentBit source removed p=true) :
    readMask (MaskedPeriodic.Batch.solve B C E text fallback source target).output.hits p=false := by
  have hu:=current_unhandled B C E text fallback source target K removed history p live
  cases he : readMask (MaskedPeriodic.Batch.solve B C E text fallback source target).output.hits p with
  | false=>rfl
  | true=>
    exact False.elim (hu.2 (Or.inr ((MaskedPeriodic.Batch.solve_correct B C E text fallback source target p).mp he).2))

theorem surviving_band (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (removed : List Nat)
    (history : ∀p,p∈(MaskedTraversalInitial.start B C E text fallback source target K).answers.history→p∈removed)
    (h capacity : Nat) (hcap : capacity=2^h) (hn : text.size<2^h)
    (p : Nat) (live : Mutable.Batch.currentBit source removed p=true)
    (matched : maskedStart B C E text.toList (readMask target) p) :
    ∃L : Nat,∃b : Band h,0<L ∧
      ((MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b ∧ BandCovers b p L) ∧
      Metadata text fallback capacity b ∧
      MaskedTraversalComplete.BandGood B C E text.toList b.snapshot capacity b.lo b.hi source removed target p ∧
      ∀c,((MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan.HasBand c ∧ BandCovers c p L)→c=b := by
  obtain ⟨a,j,t,hpa,haj,hjt,htn,marked,copy,hB,hC,hE⟩:=
    current_positive B C E text fallback source target K removed history p live matched
  obtain ⟨hL,ha,ht⟩:=MaskedTraversalPeriodicCoverage.original_length text.toList p a j t hpa haj hjt htn copy
  have hpBound : p<text.size+1 := by simp only [Array.length_toList] at htn; omega
  have hlen : a-p≤text.size-p := by simp only [Array.length_toList] at htn; omega
  obtain ⟨b,selected,unique⟩:=suffix_exactly_once text fallback h hn ⟨p,hpBound⟩ (a-p) hL hlen
  have metadata:=band_metadata text fallback h capacity hcap hn b selected.1 p selected.2.2.2
  have periodic:=current_not_periodic B C E text fallback source target K removed history p live
  have split:=MaskedTraversalPeriodicCoverage.original_partition B C E text fallback source target removed b.snapshot
    capacity (representative b) b.lo b.hi p a j t
    (metadata.invariant hcap (a-p) selected.2.1 selected.2.2.1) hcap
    (metadata.complete (a-p) selected.2.1 selected.2.2.1) selected.2.1 selected.2.2.1 live selected.2.2.2
    hpa haj hjt (by simpa only [Array.length_toList] using htn) marked copy hB hC
    (by simpa only [Array.length_toList] using hE)
  have good : MaskedTraversalComplete.BandGood B C E text.toList b.snapshot capacity b.lo b.hi source removed target p := by
    rcases split with reported|good
    · rw [periodic] at reported; cases reported
    · exact good
  exact ⟨a-p,b,hL,selected,metadata,good,unique⟩

theorem band_good_sound (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (removed : List Nat) (h capacity : Nat) (hcap : capacity=2^h) (hn : text.size<2^h)
    (b : Band h) (hb : (MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b)
    (p : Nat) (good : MaskedTraversalComplete.BandGood B C E text.toList b.snapshot capacity b.lo b.hi source removed target p) :
    readMask source p=true ∧ maskedStart B C E text.toList (readMask target) p := by
  obtain ⟨live,hp,L,hlo,hhi,j,hj,marked,_,nonoverlap,bound,hB,hC,hE⟩:=good
  have metadata:=band_metadata text fallback h capacity hcap hn b hb p hp
  have copy:=MaskedTraversalPeriodicCoverage.class_copy text fallback (representative b) L _
    (metadata.complete L hlo hhi) p j hp hj
  exact ⟨(Bool.and_eq_true_iff.mp live).1,p+L,j,j+L,by omega,nonoverlap,by omega,bound,marked,copy,hB,hC,hE⟩

theorem initial_partition (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K h capacity : Nat) (hcap : capacity=2^h) (hn : text.size<2^h) (p : Nat) :
    (readMask source p=true ∧ maskedStart B C E text.toList (readMask target) p) ↔
      readMask (MaskedTraversalInitial.start B C E text fallback source target K).answers.bits p=true ∨
        ∃b : Band h,(MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b ∧
          MaskedTraversalComplete.BandGood B C E text.toList b.snapshot capacity b.lo b.hi source
            (MaskedTraversalInitial.start B C E text fallback source target K).answers.history target p := by
  constructor
  · intro matched
    rcases (MaskedTraversalInitial.start_partition B C E text fallback source target K p).mp matched with initial|remaining
    · exact Or.inl initial
    · have live : Mutable.Batch.currentBit source
          (MaskedTraversalInitial.start B C E text fallback source target K).answers.history p=true :=
        Bool.and_eq_true_iff.mpr ⟨remaining.1.1,decide_eq_true remaining.1.2⟩
      obtain ⟨L,b,_,selected,_,good,_⟩:=surviving_band B C E text fallback source target K _ (fun _ hp=>hp)
        h capacity hcap hn p live matched.2
      exact Or.inr ⟨b,selected.1,good⟩
  · rintro (initial|⟨b,hb,good⟩)
    · have hh:=(MaskedTraversalInitial.start_read B C E text fallback source target K p).mp initial
      exact ⟨hh.1,MaskedTraversalInitial.handled_sound B C E text fallback target p hh.2⟩
    · exact band_good_sound B C E text fallback source target _ h capacity hcap hn b hb p good

end REWB.MaskedTraversalPositiveCoverage
