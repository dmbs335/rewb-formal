import REWB.MaskedTraversalNeighbor

/-! Structural descriptor locality for an actual occurrence insertion.
The descriptor itself is an executable query over the current trees.
Outside the inserted position and the old queried leader neighborhood,
that complete query result is unchanged. No completeness/AP hypothesis
is needed, so the result also applies to partial equal-depth imports.
-/
namespace REWB.MaskedTraversalNeighbor
open REWB.MaskedOrdered REWB.MaskedClusterDescriptor
variable {h : Nat}

theorem succ_eq_above (before after : Tree h) (capacity p x : Nat)
    (bg : before.Good) (bf : before.Fits 0) (ag : after.Good) (af : after.Fits 0)
    (hc : capacity=2^h) (ha : Adds before.entries after.entries p) (hp : p≤x) :
    (Tree.succ after capacity x).1=(Tree.succ before capacity x).1 :=
  succ_unique after.entries x _ _ (Tree.succ_correct after capacity x ag af hc)
    (succ_add_above _ _ p x _ ha hp (Tree.succ_correct before capacity x bg bf hc))

theorem pred_eq_below (before after : Tree h) (capacity p x : Nat)
    (bg : before.Good) (bf : before.Fits 0) (ag : after.Good) (af : after.Fits 0)
    (hc : capacity=2^h) (ha : Adds before.entries after.entries p) (hp : x≤p) :
    (Tree.pred after capacity x).1=(Tree.pred before capacity x).1 :=
  pred_unique after.entries x _ _ (Tree.pred_correct after capacity x ag af hc)
    (pred_add_below _ _ p x _ ha hp (Tree.pred_correct before capacity x bg bf hc))

theorem succ_eq_witness (before after : Tree h) (capacity p x witness : Nat)
    (bg : before.Good) (bf : before.Fits 0) (ag : after.Good) (af : after.Fits 0)
    (hc : capacity=2^h) (ha : Adds before.entries after.entries p)
    (hw : witness∈before.entries) (hxw : x<witness) (hwp : witness≤p) :
    (Tree.succ after capacity x).1=(Tree.succ before capacity x).1 := by
  have hs:=Tree.succ_correct before capacity x bg bf hc
  cases he : (Tree.succ before capacity x).1 with
  | none => rw [he] at hs; have hh:=hs witness hw; omega
  | some q =>
    rw [he] at hs
    have hq:=hs.2.2 witness hw hxw
    exact succ_unique after.entries x _ (some q) (Tree.succ_correct after capacity x ag af hc)
      (succ_add_below _ _ p x q ha (by omega) hs)

theorem pred_eq_witness (before after : Tree h) (capacity p x witness : Nat)
    (bg : before.Good) (bf : before.Fits 0) (ag : after.Good) (af : after.Fits 0)
    (hc : capacity=2^h) (ha : Adds before.entries after.entries p)
    (hw : witness∈before.entries) (hwx : witness<x) (hpw : p≤witness) :
    (Tree.pred after capacity x).1=(Tree.pred before capacity x).1 := by
  have hs:=Tree.pred_correct before capacity x bg bf hc
  cases he : (Tree.pred before capacity x).1 with
  | none => rw [he] at hs; have hh:=hs witness hw; omega
  | some q =>
    rw [he] at hs
    have hq:=hs.2.2 witness hw hwx
    exact pred_unique after.entries x _ (some q) (Tree.pred_correct after capacity x ag af hc)
      (pred_add_above _ _ p x q ha (by omega) hs)

theorem finish_below (before after : Tree h) (capacity p first last next witness : Nat)
    (bg : before.Good) (bf : before.Fits 0) (ag : after.Good) (af : after.Fits 0)
    (hc : capacity=2^h) (ha : Adds before.entries after.entries p)
    (hn : next∈before.entries) (hw : witness∈before.entries)
    (hfn : first<next) (hlp : last≤p) (hnw : next<witness) (hwp : witness≤p) :
    (finish after capacity first last (some next)).1=(finish before capacity first last (some next)).1 := by
  have hs:=succ_eq_witness before after capacity p first next bg bf ag af hc ha hn hfn (by omega)
  have hp:=pred_eq_below before after capacity p last bg bf ag af hc ha hlp
  have hf:=succ_eq_witness before after capacity p next witness bg bf ag af hc ha hw hnw hwp
  simp only [finish,hs,hp,hf]

theorem finish_above (before after : Tree h) (capacity p first last : Nat) (next : Option Nat)
    (bg : before.Good) (bf : before.Fits 0) (ag : after.Good) (af : after.Fits 0)
    (hc : capacity=2^h) (ha : Adds before.entries after.entries p)
    (hm : first∈before.entries) (hp : p≤first) (hn : ∀q,next=some q→first<q) :
    (finish after capacity first last next).1=(finish before capacity first last next).1 := by
  have hs:=succ_eq_above before after capacity p first bg bf ag af hc ha hp
  by_cases hfl : first<last
  · have hpred:=pred_eq_witness before after capacity p last first bg bf ag af hc ha hm hfl hp
    cases next with
    | none => simp only [finish,hs,hpred]
    | some q =>
      have hq:=hn q rfl
      have hfollow:=succ_eq_above before after capacity p q bg bf ag af hc ha (by omega)
      simp only [finish,hs,hpred,hfollow]
  · cases next with
    | none => simp only [finish,hfl,if_false]
    | some q =>
      have hq:=hn q rfl
      have hfollow:=succ_eq_above before after capacity p q bg bf ag af hc ha (by omega)
      simp only [finish,hfl,if_false,hfollow]

theorem describe_insert_away (before after : MaskedClusterLeaders.State h) (capacity L p x : Nat)
    (hb : MaskedClusterLeaders.Invariant L before) (ha : MaskedClusterLeaders.Invariant L after)
    (hc : capacity=2^h) (hm : Adds before.occurrences.entries after.occurrences.entries p)
    (hxp : x≠p) (hn : x∉(MaskedTraversalDirty.around before.leaders capacity p).keys) :
    (describeLeader after capacity x).1=(describeLeader before capacity x).1 := by
  by_cases hx : x∈before.leaders.entries
  · obtain ⟨d,hd,hfirst,hs⟩:=describeLeader_exists before capacity L x hb hc hx
    subst x
    have hnew : Sound after capacity d := by
      by_cases hpx : p<d.first
      · obtain ⟨a,hal,hpa,hax⟩:=around_right before.leaders capacity p d.first hb.leadGood hb.leadFits hc hx hpx hn
        have hao:=((hb.represented a).mp hal).1
        have hlead : d.first∈after.leaders.entries :=
          (ha.represented d.first).mpr ((leader_after _ _ p a L d.first hm hao hpa hax).mpr
            ((hb.represented d.first).mp hx))
        have hnext : Tree.SuccSpec after.leaders.entries d.first d.next := by
          apply succ_spec_congr before.leaders.entries after.leaders.entries d.first d.next _ hs.nextSpec
          intro r hr
          exact (ha.represented r).trans ((leader_after _ _ p a L r hm hao hpa (by omega)).trans
            (hb.represented r).symm)
        have hlast : match d.next with
            | none => Tree.MaxSpec after.occurrences.entries (some d.last)
            | some q => Tree.PredSpec after.occurrences.entries q (some d.last) := by
          have hpl : p≤d.last := by have hh:=hs.first_le_last; omega
          cases hn' : d.next with
          | none => exact max_add_below _ _ p d.last hm hpl (by simpa only [hn'] using hs.lastSpec)
          | some q => exact pred_add_above _ _ p q d.last hm hpl (by simpa only [hn'] using hs.lastSpec)
        have hfinish:=finish_above before.occurrences after.occurrences capacity p d.first d.last d.next
          hb.occGood hb.occFits ha.occGood ha.occFits hc hm hs.firstMember (by omega) (by
            intro q hq
            have hh:=hs.nextSpec
            rw [hq] at hh
            exact hh.2.1)
        exact ⟨hlead,hm.old hs.firstMember,hm.old hs.lastMember,hs.first_le_last,hnext,hlast,
          hs.materialized.trans hfinish.symm⟩
      · have hfp : d.first<p := by omega
        obtain ⟨a,b,hal,hbl,hfa,hab,hbp⟩:=around_left before.leaders capacity p d.first
          hb.leadGood hb.leadFits hc hx (by omega) hn
        have hlead : d.first∈after.leaders.entries :=
          (ha.represented d.first).mpr ((leader_below _ _ p L d.first hm hfp).mpr
            ((hb.represented d.first).mp hx))
        cases hnext : d.next with
        | none =>
          have hsnext:=hs.nextSpec
          rw [hnext] at hsnext
          have hh:=hsnext a hal
          omega
        | some q =>
          have hsnext:=hs.nextSpec
          rw [hnext] at hsnext
          have hqa:=hsnext.2.2 a hal hfa
          have hqp : q<p := by omega
          have hnext' : Tree.SuccSpec after.leaders.entries d.first d.next := by
            rw [hnext]
            apply succ_spec_bounded before.leaders.entries after.leaders.entries d.first q p _ hsnext hqp
            intro r hr
            exact (ha.represented r).trans ((leader_below _ _ p L r hm hr).trans (hb.represented r).symm)
          have hslast : Tree.PredSpec before.occurrences.entries q (some d.last) := by
            simpa only [hnext] using hs.lastSpec
          have hlast : match d.next with
              | none => Tree.MaxSpec after.occurrences.entries (some d.last)
              | some y => Tree.PredSpec after.occurrences.entries y (some d.last) := by
            rw [hnext]
            exact pred_add_below _ _ p q (some d.last) hm (by omega) hslast
          have hqmem:=((hb.represented q).mp hsnext.1).1
          have hbmem:=((hb.represented b).mp hbl).1
          have hfinish:=finish_below before.occurrences after.occurrences capacity p d.first d.last q b
            hb.occGood hb.occFits ha.occGood ha.occFits hc hm hqmem hbmem hsnext.2.1
            (by have hh:=hslast.2.1; omega) (by omega) hbp
          rw [←hnext] at hfinish
          exact ⟨hlead,hm.old hs.firstMember,hm.old hs.lastMember,hs.first_le_last,hnext',hlast,
            hs.materialized.trans hfinish.symm⟩
    rw [describe_of_sound after capacity L ha hc d hnew,hd]
  · have hxa : x∉after.leaders.entries := by
      intro hnew
      exact hx ((hb.represented x).mpr (leader_old _ _ p L x hm hxp ((ha.represented x).mp hnew)))
    have hbefore : (Tree.contains before.leaders capacity x).1=false := by
      cases he : (Tree.contains before.leaders capacity x).1 with
      | false => rfl
      | true => exact False.elim (hx ((Tree.contains_correct before.leaders capacity x hb.leadFits hc).mp he))
    have hafter : (Tree.contains after.leaders capacity x).1=false := by
      cases he : (Tree.contains after.leaders capacity x).1 with
      | false => rfl
      | true => exact False.elim (hxa ((Tree.contains_correct after.leaders capacity x ha.leadFits hc).mp he))
    simp only [describeLeader,hbefore,hafter,Bool.false_eq_true,if_false]

theorem add_describe_away (before : MaskedClusterLeaders.State h) (capacity L p x : Nat)
    (hi : MaskedClusterLeaders.Invariant L before) (hc : capacity=2^h) (hp : p<capacity)
    (hn : x∉(MaskedTraversalDirty.prepareChange before.leaders
      (MaskedClusterLeaders.add capacity L p before).state.leaders capacity p).keys) :
    (describeLeader (MaskedClusterLeaders.add capacity L p before).state capacity x).1=
      (describeLeader before capacity x).1 := by
  have hxp : x≠p := by
    intro he
    apply hn
    simp only [MaskedTraversalDirty.prepareChange,List.mem_cons]
    exact Or.inl he
  have hn' : x∉(MaskedTraversalDirty.around before.leaders capacity p).keys := by
    intro hh
    apply hn
    exact List.mem_cons_of_mem p (List.mem_append_left _ hh)
  apply describe_insert_away before (MaskedClusterLeaders.add capacity L p before).state capacity L p x hi
    (MaskedClusterLeaders.add_invariant capacity L p before hi hc hp) hc _ hxp hn'
  intro y
  change y∈(MaskedOrdered.insert before.occurrences capacity p).tree.entries↔_
  exact MaskedOrdered.insert_mem before.occurrences capacity p y hi.occFits hc (by omega)

end REWB.MaskedTraversalNeighbor
