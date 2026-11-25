import REWB.MaskedTraversalNeighborInsert
import REWB.MaskedTraversalDirtyEvents

/-! Actual live threshold batches preserve the entire descriptor outside
their generated dirty neighborhoods. Occurrences stay fixed; shortening
only adds leaders, and every new leader is the endpoint of a validated
live record already returned by the queue. No supplied affected-set or
unmarked-descriptor assumption appears in the resulting theorem.
-/
namespace REWB.MaskedTraversalNeighbor
open REWB.MaskedOrdered REWB.MaskedClusterDescriptor
variable {h : Nat}

theorem describe_additions_away (before after : MaskedClusterLeaders.State h)
    (capacity old fresh x : Nat) (targets : Nat→Prop)
    (hb : MaskedClusterLeaders.Invariant old before) (ha : MaskedClusterLeaders.Invariant fresh after)
    (hc : capacity=2^h) (ho : after.occurrences=before.occurrences)
    (hkeep : ∀p,p∈before.leaders.entries→p∈after.leaders.entries)
    (hnew : ∀p,p∈after.leaders.entries→p∈before.leaders.entries ∨ targets p)
    (hn : ∀p,targets p→x≠p ∧ x∉(MaskedTraversalDirty.around before.leaders capacity p).keys) :
    (describeLeader after capacity x).1=(describeLeader before capacity x).1 := by
  by_cases hx : x∈before.leaders.entries
  · obtain ⟨d,hd,hfirst,hs⟩:=describeLeader_exists before capacity old x hb hc hx
    subst x
    have hnext : Tree.SuccSpec after.leaders.entries d.first d.next := by
      cases he : d.next with
      | none =>
        have hsnext:=hs.nextSpec
        rw [he] at hsnext
        intro r hr
        rcases hnew r hr with hold|htarget
        · exact hsnext r hold
        · by_cases hrf : r≤d.first
          · exact hrf
          · obtain ⟨a,b,ham,_,hfa,_,_⟩:=around_left before.leaders capacity r d.first
              hb.leadGood hb.leadFits hc hx (by omega) (hn r htarget).2
            have hh:=hsnext a ham
            omega
      | some q =>
        have hsnext:=hs.nextSpec
        rw [he] at hsnext
        refine ⟨hkeep q hsnext.1,hsnext.2.1,?_⟩
        intro r hr hfr
        rcases hnew r hr with hold|htarget
        · exact hsnext.2.2 r hold hfr
        · by_cases hqr : q≤r
          · exact hqr
          · obtain ⟨a,b,ham,_,hfa,hab,hbr⟩:=around_left before.leaders capacity r d.first
              hb.leadGood hb.leadFits hc hx (by omega) (hn r htarget).2
            have hqa:=hsnext.2.2 a ham hfa
            omega
    have hs' : Sound after capacity d :=
      ⟨hkeep d.first hs.firstLeader,by simpa only [ho] using hs.firstMember,
        by simpa only [ho] using hs.lastMember,hs.first_le_last,hnext,
        by simpa only [ho] using hs.lastSpec,by simpa only [ho] using hs.materialized⟩
    rw [describe_of_sound after capacity fresh ha hc d hs',hd]
  · have hxa : x∉after.leaders.entries := by
      intro hm
      rcases hnew x hm with hold|htarget
      · exact hx hold
      · exact (hn x htarget).1 rfl
    have hbefore : (Tree.contains before.leaders capacity x).1=false := by
      cases he : (Tree.contains before.leaders capacity x).1 with
      | false => rfl
      | true => exact False.elim (hx ((Tree.contains_correct before.leaders capacity x hb.leadFits hc).mp he))
    have hafter : (Tree.contains after.leaders capacity x).1=false := by
      cases he : (Tree.contains after.leaders capacity x).1 with
      | false => rfl
      | true => exact False.elim (hxa ((Tree.contains_correct after.leaders capacity x ha.leadFits hc).mp he))
    simp only [describeLeader,hbefore,hafter,Bool.false_eq_true,if_false]

theorem shorten_describe_away (capacity old fresh x : Nat) (s : MaskedClusterLeaders.State h)
    (hi : MaskedClusterLeaders.Invariant old s) (hf : MaskedClusterLeaders.Future old s)
    (hc : capacity=2^h) (hle : fresh≤old)
    (hn : ∀e,e∈(MaskedClusterLeaders.shorten capacity fresh s).live→
      x∉(MaskedTraversalDirty.prepareChange s.leaders
        (MaskedClusterLeaders.shorten capacity fresh s).state.leaders capacity e.value.edge.2).keys) :
    (describeLeader (MaskedClusterLeaders.shorten capacity fresh s).state capacity x).1=
      (describeLeader s capacity x).1 := by
  have ha:=MaskedClusterLeaders.shorten_invariant capacity old fresh s hi hf hc hle
  apply describe_additions_away s (MaskedClusterLeaders.shorten capacity fresh s).state capacity old fresh x
    (MaskedClusterLeaders.Targets (MaskedClusterLeaders.shorten capacity fresh s).live) hi ha hc rfl
  · intro p hp
    apply (ha.represented p).mpr
    exact MaskedClusterLeaders.leader_shorten _ old fresh p hle ((hi.represented p).mp hp)
  · intro p hp
    by_cases hold : p∈s.leaders.entries
    · exact Or.inl hold
    · have hnew : MaskedClusterLeaders.Leader s.occurrences.entries fresh p := (ha.represented p).mp hp
      have hnot : ¬MaskedClusterLeaders.Leader s.occurrences.entries old p := by
        intro hh
        exact hold ((hi.represented p).mpr hh)
      obtain ⟨e,he,hep,_⟩:=MaskedClusterLeaders.changed_leader_record capacity old fresh p s hi hf hc hnew hnot
      exact Or.inr ⟨e,he,hep⟩
  · intro p hp
    obtain ⟨e,he,hep⟩:=hp
    have hnone:=hn e he
    rw [hep] at hnone
    refine ⟨?_,?_⟩
    · intro heq
      apply hnone
      exact List.mem_cons.mpr (Or.inl heq)
    · intro hm
      apply hnone
      exact List.mem_cons_of_mem p (List.mem_append_left _ hm)

theorem crossing_describe_unmarked (capacity old fresh x : Nat) (s : MaskedClusterLeaders.State h)
    (out : MaskedTraversalDirty.Marked h) (hv : out.keys.Valid)
    (hi : MaskedClusterLeaders.Invariant old s) (hf : MaskedClusterLeaders.Future old s)
    (hc : capacity=2^h) (hle : fresh≤old)
    (hn : x∉(MaskedTraversalDirty.crossing s (MaskedClusterLeaders.shorten capacity fresh s) capacity out).keys.tree.entries) :
    (describeLeader (MaskedClusterLeaders.shorten capacity fresh s).state capacity x).1=
      (describeLeader s capacity x).1 := by
  have ha:=MaskedClusterLeaders.shorten_invariant capacity old fresh s hi hf hc hle
  have hb:=MaskedClusterLeaders.live_bound capacity old fresh s hi hc
  have hs:=MaskedTraversalDirty.live_spec s.leaders (MaskedClusterLeaders.shorten capacity fresh s).state.leaders capacity
    (MaskedClusterLeaders.shorten capacity fresh s).live out hv hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc
    (fun e he=>by have hh:=hb e he; omega)
  apply shorten_describe_away capacity old fresh x s hi hf hc hle
  intro e he hx
  apply hn
  apply (hs.2.1 x).mpr
  exact Or.inl ⟨e,he,hx⟩

end REWB.MaskedTraversalNeighbor
