import REWB.MaskedTraversalBankReadyCorrect

/-! The actual predecessor/descriptor/anchor reader satisfies the incoming
cursor bound required by the bank compiler.  Retained anchor bounds are
an explicit maintained invariant; the reset case is derived from the
complete occurrence class, not from a supplied cursor or neighbor oracle. -/
namespace REWB.MaskedTraversalBankReady
open REWB.MaskedClusterDescriptor REWB.MaskedOrdered REWB.MaskedRunDiscovery
variable {α : Type} {h : Nat}

def AnchorBounds (partition : MaskedClusterLeaders.State h) (capacity n L : Nat)
    (anchors : Array (Option Nat)) : Prop :=
  ∀first d,(describeLeader partition capacity first).1=some d →
    d.last+readAnchor anchors first L≤n ∧
    ∀p,d.following=some p → d.last+readAnchor anchors first L≤p

theorem anchorBounds_reset (partition : MaskedClusterLeaders.State h) (capacity n base L : Nat)
    (f : Nat→α) (anchors : Array (Option Nat))
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : Complete f n base L partition.occurrences.entries) (hL : 0<L)
    (ha : ∀first,first∈partition.leaders.entries → readAnchor anchors first L=L) :
    AnchorBounds partition capacity n L anchors := by
  intro first d hd
  have hs:=describeLeader_sound partition capacity L first hi hc d hd
  have hg:=describeLeader_geometry partition capacity L first hi hc d hd f n base hfull hL
  have hm : first∈partition.leaders.entries := by rw [←hs.1]; exact hs.2.firstLeader
  rw [ha first hm]
  exact ⟨hg.anchor.lastBound,hg.anchor.followingSafe⟩

theorem previous_next (partition : MaskedClusterLeaders.State h) (capacity L first p : Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfirst : first∈partition.leaders.entries)
    (hp : (Tree.pred partition.leaders capacity first).1=some p)
    (previous : Descriptor) (hd : (describeLeader partition capacity p).1=some previous) :
    previous.next=some first := by
  have hpred:=Tree.pred_correct partition.leaders capacity first hi.leadGood hi.leadFits hc
  rw [hp] at hpred
  have hs:=describeLeader_sound partition capacity L p hi hc previous hd
  have hnext:=hs.2.nextSpec
  rw [hs.1] at hnext
  apply succ_unique partition.leaders.entries p previous.next (some first) hnext
  refine ⟨hfirst,hpred.2.1,?_⟩
  intro x hx hpx
  by_cases hfx : first≤x
  · exact hfx
  · have he:=hpred.2.2 x hx (by omega)
    omega

private theorem adjacent_succ (partition : MaskedClusterLeaders.State h) (capacity L a b : Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (ha : Adjacent partition.occurrences.entries a b) :
    (Tree.succ partition.occurrences capacity a).1=some b := by
  apply succ_unique partition.occurrences.entries a _ (some b)
    (Tree.succ_correct partition.occurrences capacity a hi.occGood hi.occFits hc)
  refine ⟨ha.2.1,ha.2.2.1,?_⟩
  intro x hx hax
  by_cases hbx : b≤x
  · exact hbx
  · exact False.elim (ha.2.2.2 x hx hax (by omega))

theorem incoming_bound (partition : MaskedClusterLeaders.State h) (capacity n base L first : Nat)
    (f : Nat→α) (anchors : Array (Option Nat))
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : Complete f n base L partition.occurrences.entries) (hL : 0<L)
    (hb : AnchorBounds partition capacity n L anchors) (d : Descriptor)
    (hd : (describeLeader partition capacity first).1=some d)
    (hen : (incoming partition capacity first L anchors).enabled=true) :
    d.first<(incoming partition capacity first L anchors).cursor ∧
      (incoming partition capacity first L anchors).cursor≤
        (if d.repetitions=0 then d.nextAt n else d.first+d.period) := by
  have hs:=describeLeader_sound partition capacity L first hi hc d hd
  have hg:=describeLeader_geometry partition capacity L first hi hc d hd f n base hfull hL
  have hm : first∈partition.leaders.entries := by rw [←hs.1]; exact hs.2.firstLeader
  cases hp : (Tree.pred partition.leaders capacity first).1 with
  | none => simp only [incoming,hp,Bool.false_eq_true] at hen
  | some p =>
    cases hpd : (describeLeader partition capacity p).1 with
    | none => simp only [incoming,hp,hpd,Bool.false_eq_true] at hen
    | some previous =>
      have hpSound:=(describeLeader_sound partition capacity L p hi hc previous hpd).2
      have hnext:=previous_next partition capacity L first p hi hc hm hp previous hpd
      have hfollow : previous.following=(Tree.succ partition.occurrences capacity first).1 := by
        rw [hpSound.following_eq partition capacity previous,hnext]
      have hanchor:=hb p previous hpd
      have hpos : first<previous.last+readAnchor anchors p L := by
        simpa only [incoming,hp,hpd,decide_eq_true_eq] using hen
      simp only [incoming,hp,hpd]
      refine ⟨by rw [hs.1]; exact hpos,?_⟩
      by_cases hpoint : d.repetitions=0
      · rw [if_pos hpoint]
        have hfl:=hg.point hpoint |>.1
        cases hn : d.next with
        | none => simpa only [Descriptor.nextAt,hn,Option.getD_none] using hanchor.1
        | some next =>
          have hadj:=(hs.2.next_adjacency partition capacity L hi d next hn).1
          rw [←hfl,hs.1] at hadj
          have hsucc:=adjacent_succ partition capacity L first next hi hc hadj
          have hprev : previous.following=some next := hfollow.trans hsucc
          simpa only [Descriptor.nextAt,hn,Option.getD_some] using hanchor.2 next hprev
      · rw [if_neg hpoint]
        have hrep : 0<d.repetitions := by omega
        have hprod:=Nat.mul_pos hrep hg.period_pos
        have hlt : d.first<d.last := by have he:=hg.endpoint; omega
        obtain ⟨u,hu,hadj,_⟩:=hs.2.first_successor partition capacity L hi hc d hlt
        have hperiod : d.period=u-d.first := by
          rw [hs.2.period_eq partition capacity d]
          simp only [hlt,if_true,hu,Option.getD_some]
        have huq : u=d.first+d.period := by have hlt':=hadj.2.2.1; omega
        have hsucc : (Tree.succ partition.occurrences capacity first).1=some u := by
          simpa only [hs.1] using hu
        have hprev : previous.following=some u := hfollow.trans hsucc
        have hle:=hanchor.2 u hprev
        omega

end REWB.MaskedTraversalBankReady
