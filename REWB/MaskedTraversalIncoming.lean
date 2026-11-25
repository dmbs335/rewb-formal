import REWB.MaskedTraversalRetainedTransitions
import REWB.MaskedTraversalContextCorrect

/-! Structural incoming-cursor locality. An actual current predecessor
outside the sparse reset set has an unchanged full descriptor, whose
`next` field determines the old predecessor too. A missing predecessor
is preserved because occurrences only grow and an actual minimum leader
exists below every occurrence. Only cursor/enabled data is compared:
the measured query work can change when the persistent tree shape changes.

The generic transport lemmas below are instantiated for the executed
insert, threshold and heavy-merge operations in the companion module.
-/
namespace REWB.MaskedTraversalIncoming
open REWB.MaskedOrdered REWB.MaskedClusterDescriptor REWB.MaskedTraversalBankReady
open REWB.MaskedTraversalContext REWB.MaskedTraversalNeighbor
variable {α : Type} {h : Nat}

theorem previous_unmarked (s : MaskedClusterLeaders.State h) (capacity L first p : Nat)
    (keys : List Nat) (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (hm : first∈s.leaders.entries) (hp : (Tree.pred s.leaders capacity first).1=some p)
    (hn : first∉(successors s.leaders capacity keys (MaskedTraversalDirty.empty h)).keys.tree.entries) :
    p∉keys := by
  have hs:=successors_spec s.leaders capacity keys (MaskedTraversalDirty.empty h)
    hi.leadGood hi.leadFits hc (MaskedOrdered.State.empty_valid h)
  have hpred:=Tree.pred_correct s.leaders capacity first hi.leadGood hi.leadFits hc
  rw [hp] at hpred
  intro hkey
  apply hn
  apply (hs.2.1 first).mpr
  exact Or.inl ⟨p,hkey,hpred.1,pred_next s.leaders capacity first p hi.leadGood hi.leadFits hc hm hp⟩

theorem predecessor_preserved (before after : MaskedClusterLeaders.State h)
    (capacity old fresh first : Nat) (keys : List Nat)
    (hb : MaskedClusterLeaders.Invariant old before) (ha : MaskedClusterLeaders.Invariant fresh after)
    (hc : capacity=2^h)
    (hocc : ∀p,p∈before.occurrences.entries→p∈after.occurrences.entries)
    (hdesc : ∀p,p∉keys→(describeLeader after capacity p).1=(describeLeader before capacity p).1)
    (hm : first∈after.leaders.entries)
    (hn : first∉(successors after.leaders capacity keys (MaskedTraversalDirty.empty h)).keys.tree.entries) :
    (Tree.pred after.leaders capacity first).1=(Tree.pred before.leaders capacity first).1 := by
  have hpred:=Tree.pred_correct after.leaders capacity first ha.leadGood ha.leadFits hc
  cases hp : (Tree.pred after.leaders capacity first).1 with
  | none =>
    rw [hp] at hpred
    symm
    apply pred_unique before.leaders.entries first _ none
      (Tree.pred_correct before.leaders capacity first hb.leadGood hb.leadFits hc)
    intro p hpl
    have hpo:=hocc p ((hb.represented p).mp hpl).1
    obtain ⟨q,hql,hqp⟩:=leader_before after fresh p ha hpo
    have hq:=hpred q hql
    omega
  | some p =>
    rw [hp] at hpred
    have hnot:=previous_unmarked after capacity fresh first p keys ha hc hm hp hn
    obtain ⟨d,hd,hfirst,hs⟩:=describeLeader_exists after capacity fresh p ha hc hpred.1
    have hold : (describeLeader before capacity p).1=some d := (hdesc p hnot).symm.trans hd
    have hsold:=(describeLeader_sound before capacity old p hb hc d hold).2
    have hnxt:=pred_next after.leaders capacity first p ha.leadGood ha.leadFits hc hm hp
    have hdnext : d.next=some first := by
      have he:=succ_unique after.leaders.entries p _ d.next
        (Tree.succ_correct after.leaders capacity p ha.leadGood ha.leadFits hc)
        (by simpa only [hfirst] using hs.nextSpec)
      exact he.symm.trans hnxt
    have hnext:=hsold.nextSpec
    rw [hfirst,hdnext] at hnext
    symm
    apply pred_unique before.leaders.entries first _ (some p)
      (Tree.pred_correct before.leaders capacity first hb.leadGood hb.leadFits hc)
    refine ⟨by simpa only [hfirst] using hsold.firstLeader,hnext.2.1,?_⟩
    intro q hql hqf
    by_cases hqp : q≤p
    · exact hqp
    · have hh:=hnext.2.2 q hql (by omega)
      omega

theorem incoming_transport (before after : MaskedClusterLeaders.State h)
    (capacity old fresh first : Nat) (anchors : Array (Option Nat)) (keys : List Nat)
    (hb : MaskedClusterLeaders.Invariant old before) (ha : MaskedClusterLeaders.Invariant fresh after)
    (hc : capacity=2^h)
    (hocc : ∀p,p∈before.occurrences.entries→p∈after.occurrences.entries)
    (hdesc : ∀p,p∉keys→(describeLeader after capacity p).1=(describeLeader before capacity p).1)
    (hanchor : ∀p,p∉keys→∀d,(describeLeader after capacity p).1=some d→
      readAnchor anchors p fresh=readAnchor anchors p old)
    (hm : first∈after.leaders.entries)
    (hn : first∉(successors after.leaders capacity keys (MaskedTraversalDirty.empty h)).keys.tree.entries) :
    (incoming after capacity first fresh anchors).cursor=(incoming before capacity first old anchors).cursor ∧
    (incoming after capacity first fresh anchors).enabled=(incoming before capacity first old anchors).enabled := by
  have hprev:=predecessor_preserved before after capacity old fresh first keys hb ha hc hocc hdesc hm hn
  cases hp : (Tree.pred after.leaders capacity first).1 with
  | none =>
    have hold:=hprev.symm.trans hp
    simp only [incoming,hp,hold]
    constructor <;> trivial
  | some p =>
    have hold:=hprev.symm.trans hp
    have hnot:=previous_unmarked after capacity fresh first p keys ha hc hm hp hn
    have hdeq:=hdesc p hnot
    cases hd : (describeLeader after capacity p).1 with
    | none =>
      have hdb:=hdeq.symm.trans hd
      simp only [incoming,hp,hold,hd,hdb]
      constructor <;> trivial
    | some d =>
      have hdb:=hdeq.symm.trans hd
      have he:=hanchor p hnot d hd
      simp only [incoming,hp,hold,hd,hdb,he]
      constructor <;> trivial

/-- The real populated retained slot removes the current-length default
from the predecessor read, including at a shortening transition. -/
theorem retained_transport (before after : MaskedClusterLeaders.State h)
    (capacity n old fresh first : Nat) (f : Nat→α) (anchors : Array (Option Nat)) (keys : List Nat)
    (hb : MaskedClusterLeaders.Invariant old before) (ha : MaskedClusterLeaders.Invariant fresh after)
    (hc : capacity=2^h)
    (hocc : ∀p,p∈before.occurrences.entries→p∈after.occurrences.entries)
    (hdesc : ∀p,p∉keys→(describeLeader after capacity p).1=(describeLeader before capacity p).1)
    (hown : MaskedTraversalRetained.Away after capacity f n fresh anchors keys)
    (hm : first∈after.leaders.entries)
    (hn : first∉(successors after.leaders capacity keys (MaskedTraversalDirty.empty h)).keys.tree.entries) :
    (incoming after capacity first fresh anchors).cursor=(incoming before capacity first old anchors).cursor ∧
    (incoming after capacity first fresh anchors).enabled=(incoming before capacity first old anchors).enabled := by
  apply incoming_transport before after capacity old fresh first anchors keys hb ha hc hocc hdesc _ hm hn
  intro p hnot d hd
  obtain ⟨H,hH,_⟩:=hown p hnot d hd
  simp only [readAnchor,hH,Option.getD_some]

end REWB.MaskedTraversalIncoming
