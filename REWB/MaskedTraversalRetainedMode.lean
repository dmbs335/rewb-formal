import REWB.MaskedTraversalRetained
import REWB.MaskedTraversalEdgeCorrect

/-! No missing overlap reset: if the last/next boundary changes overlap
side, its actual queued live overlap record marks the cluster's first.
Within an emitted band, Future/Clean instead proves every represented
length retains the same side, without scanning those lengths.
-/
namespace REWB.MaskedTraversalRetained
open REWB.MaskedOrdered REWB.MaskedClusterDescriptor REWB.MaskedRunDiscovery REWB.MaskedEventBudget
variable {α : Type} {h : Nat}

theorem next_marks_first (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (next : Nat) (hn : d.next=some next) :
    d.first∈(MaskedTraversalDirty.around s.leaders capacity next).keys := by
  have hs:=hd.nextSpec
  rw [hn] at hs
  have hp : (Tree.pred s.leaders capacity next).1=some d.first := by
    apply pred_unique s.leaders.entries next _ (some d.first)
      (Tree.pred_correct s.leaders capacity next hi.leadGood hi.leadFits hc)
    refine ⟨hd.firstLeader,hs.2.1,?_⟩
    intro r hr hrn
    by_cases hrf : r≤d.first
    · exact hrf
    · have hh:=hs.2.2 r hr (by omega)
      omega
  have hp' : (Tree.pred s.leaders capacity (next+1)).1=some next := by
    apply pred_unique s.leaders.entries (next+1) _ (some next)
      (Tree.pred_correct s.leaders capacity (next+1) hi.leadGood hi.leadFits hc)
    exact ⟨hs.1,by omega,fun r _ hr=>Nat.lt_succ_iff.mp hr⟩
  simp only [MaskedTraversalDirty.Around.keys,MaskedTraversalDirty.around,hp',
    MaskedTraversalDirty.optionalPred,hp,List.mem_append,Option.mem_toList]
  exact Or.inl (Or.inl (Or.inl (by simp)))

theorem overlap_record (capacity old fresh last next : Nat) (s : MaskedClusterLeaders.State h)
    (hi : MaskedClusterLeaders.Invariant old s) (hf : MaskedClusterLeaders.Future old s)
    (hc : capacity=2^h) (ha : Adjacent s.occurrences.entries last next)
    (hold : next<last+old) (hnew : ¬next<last+fresh) :
    ∃e,e∈(MaskedClusterLeaders.shorten capacity fresh s).live ∧ e.value.edge.2=next ∧ e.value.kind=.overlap := by
  let event : Threshold:=⟨(last,next),.overlap,next-last⟩
  have hedge:=adjacent_edge _ last next (Tree.ordered s.occurrences 0 hi.occFits) ha
  have hev : event∈thresholds (last,next) := by simp [event,thresholds]
  have hlevel : event.level<old := by
    have hh:=ha.2.2.1
    dsimp only [event]
    omega
  have hqueue:=hf (last,next) hedge event hev hlevel
  refine ⟨MaskedThresholdEvents.pack event,?_,rfl,rfl⟩
  apply (MaskedThresholdEvents.shorten_correct (h+1) fresh s.occurrences capacity s.queue
    hi.occGood hi.occFits hc hi.queueGood _).mpr
  refine ⟨hqueue,?_,ha⟩
  dsimp only [MaskedThresholdEvents.pack,event]
  have hh:=ha.2.2.1
  omega

theorem mode_away (capacity n old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (hi : MaskedClusterLeaders.Invariant old s) (hf : MaskedClusterLeaders.Future old s)
    (hc : capacity=2^h) (hle : fresh≤old)
    (d : Descriptor) (hd : Sound s capacity d) (hb : d.last+old≤n)
    (hn : ∀e,e∈(MaskedClusterLeaders.shorten capacity fresh s).live→
      d.first∉(MaskedTraversalDirty.prepareChange s.leaders
        (MaskedClusterLeaders.shorten capacity fresh s).state.leaders capacity e.value.edge.2).keys) :
    (d.nextAt n<d.last+old↔d.nextAt n<d.last+fresh) := by
  cases hnext : d.next with
  | none => simp only [Descriptor.nextAt,hnext,Option.getD_none]; omega
  | some next =>
    have hadj:=(hd.next_adjacency s capacity old hi d next hnext).1
    simp only [Descriptor.nextAt,hnext,Option.getD_some]
    constructor
    · intro hold
      by_cases hnew : next<d.last+fresh
      · exact hnew
      · obtain ⟨e,he,hep,_⟩:=overlap_record capacity old fresh d.last next s hi hf hc hadj hold hnew
        have hnot:=hn e he
        rw [hep] at hnot
        exact False.elim (hnot (List.mem_cons_of_mem next (List.mem_append_left _
          (next_marks_first s capacity old hi hc d hd next hnext))))
    · omega

theorem mode_between (capacity n old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (hi : MaskedClusterLeaders.Invariant old s) (hf : MaskedClusterLeaders.Future old s)
    (hle : fresh≤old) (hclean : MaskedTraversalEdge.Clean fresh s)
    (d : Descriptor) (hd : Sound s capacity d) (hb : d.last+old≤n) :
    (d.nextAt n<d.last+old↔d.nextAt n<d.last+fresh) := by
  cases hnext : d.next with
  | none => simp only [Descriptor.nextAt,hnext,Option.getD_none]; omega
  | some next =>
    have hadj:=(hd.next_adjacency s capacity old hi d next hnext).1
    have hedge:=adjacent_edge _ d.last next (Tree.ordered s.occurrences 0 hi.occFits) hadj
    let event : Threshold:=⟨(d.last,next),.overlap,next-d.last⟩
    have hev : event∈thresholds (d.last,next) := by simp [event,thresholds]
    have hh:=MaskedTraversalEdge.threshold_between old fresh s hf hle hclean (d.last,next) hedge event hev
    dsimp only [event] at hh
    simp only [Descriptor.nextAt,hnext,Option.getD_some]
    have hln:=hadj.2.2.1
    omega

theorem band_own (f : Nat→α) (n capacity first L : Nat) (anchors : Array (Option Nat))
    (origin : Tree h) (band : MaskedTraversalEdge.Band h) (hv : band.Valid capacity origin)
    (hc : capacity=2^h) (hl : band.lo≤L) (hh : L≤band.hi)
    (d : Descriptor) (hd : (describeLeader band.snapshot capacity first).1=some d)
    (ho : Own f n band.hi anchors first d) : Own f n L anchors first d := by
  obtain ⟨H,hH,cert⟩:=ho
  have hs:=(describeLeader_sound band.snapshot capacity band.hi first hv.invariant hc d hd).2
  have hclean:=(hv.at hc hl hh).2.2
  have hb : d.last+band.hi≤n := by have h1:=cert.current; have h2:=cert.lastBound; omega
  have hm:=mode_between capacity n band.hi L band.snapshot hv.invariant hv.future hh hclean d hs hb
  exact ⟨H,hH,MaskedLocalAnchor.shorten f n d.first band.hi L (copies d) d.last (d.nextAt n)
    d.previous d.following H cert hh hm⟩

end REWB.MaskedTraversalRetained
