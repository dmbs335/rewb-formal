import REWB.MaskedTraversalPositiveCoverage

namespace REWB.MaskedTraversalPositiveCoverage.Regression
open REWB.Spec REWB.MaskedProgression REWB.MaskedRunDiscovery REWB.MaskedTraversalDriver

abbrev all : DFA (Fin 1) := ⟨1,0,fun _ _=>0,fun _=>true⟩
abbrev odd : DFA (Fin 1) := ⟨2,0,fun q _=>if q==0 then 1 else 0,fun q=>q==1⟩
abbrev eps : DFA (Fin 1) := ⟨2,0,fun _ _=>1,fun q=>q==0⟩
def text : Array (Fin 1) := #[0,0]
def source : Array Bool := #[true,false,false]
def target : Array Bool := #[false,true,false]

theorem cross_initial_empty :
    (MaskedTraversalInitial.start odd all all text 0 source target 1).answers.history=[] := by
  have none : ∀p,p∉(MaskedTraversalInitial.start odd all all text 0 source target 1).answers.history := by
    intro p hp
    have hh:=(MaskedTraversalInitial.start_history odd all all text 0 source target 1 p).mp hp
    rcases hh.2 with empty|⟨R,valid,_,L,k,hL,hgap,hend,_⟩
    · have bad : false=true := empty.1
      cases bad
    · have positive:=valid.2.2.2.1.1
      have bound : R.hi≤2 := valid.2.1
      omega
  cases he : (MaskedTraversalInitial.start odd all all text 0 source target 1).answers.history with
  | nil=>rfl
  | cons p ps=>exact False.elim (none p (by rw [he]; exact List.mem_cons_self))

theorem cross_original : maskedStart odd all all text.toList (readMask target) 0 :=
  ⟨1,1,2,by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl⟩

theorem actual_remaining_band :
    ∃L : Nat,∃b : MaskedTraversalEdge.Band 2,0<L ∧
      ((MaskedTraversalDriver.run 2 (prepareSuffixes text 0).trie.tree).plan.HasBand b ∧ BandCovers b 0 L) ∧
      Metadata text 0 4 b ∧
      MaskedTraversalComplete.BandGood odd all all text.toList b.snapshot 4 b.lo b.hi source [] target 0 ∧
      ∀c,((MaskedTraversalDriver.run 2 (prepareSuffixes text 0).trie.tree).plan.HasBand c ∧ BandCovers c 0 L)→c=b := by
  apply surviving_band odd all all text 0 source target 1 []
    (fun _ hp=>by rw [cross_initial_empty] at hp; exact hp) 2 4 (by decide) (by decide) 0 rfl
  exact cross_original

theorem actual_initial_partition :
    (readMask source 0=true ∧ maskedStart odd all all text.toList (readMask target) 0) ↔
      readMask (MaskedTraversalInitial.start odd all all text 0 source target 1).answers.bits 0=true ∨
        ∃b : MaskedTraversalEdge.Band 2,
          (MaskedTraversalDriver.run 2 (prepareSuffixes text 0).trie.tree).plan.HasBand b ∧
          MaskedTraversalComplete.BandGood odd all all text.toList b.snapshot 4 b.lo b.hi source
            (MaskedTraversalInitial.start odd all all text 0 source target 1).answers.history target 0 :=
  initial_partition odd all all text 0 source target 1 2 4 (by decide) (by decide) 0

def terminal : Array Bool := #[false,false,true]

theorem terminal_empty_reported :
    readMask (MaskedTraversalInitial.start eps eps eps text 0 terminal terminal 1).answers.bits 2=true := by decide

theorem terminal_has_no_positive_band (b : MaskedTraversalEdge.Band 2)
    (hb : (MaskedTraversalDriver.run 2 (prepareSuffixes text 0).trie.tree).plan.HasBand b)
    (member : 2∈b.snapshot.occurrences.entries) : False := by
  have meta:=band_metadata text 0 2 4 (by decide) (by decide) b hb 2 member
  have bound:=((meta.complete b.hi meta.valid.bounds (Nat.le_refl _) 2).mp member).1
  have positive:=meta.positive
  have order:=meta.valid.bounds
  have n : text.size=2 := rfl
  rw [n] at bound
  omega

end REWB.MaskedTraversalPositiveCoverage.Regression
