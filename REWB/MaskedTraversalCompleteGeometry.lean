import REWB.MaskedTraversalCompleteOrder
import REWB.MaskedTraversalCompletePath

/-! Numerical path geometry from actual descriptor, predecessor and
retained-anchor reads. Gates affect source eligibility only; the cursor
interfaces are the same for clipped and unclipped banks. -/
namespace REWB.MaskedTraversalComplete
open REWB.MaskedCluster REWB.MaskedTraversalAggregate REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedClusterDescriptor REWB.MaskedTraversalBankReady
variable {α : Type} {C E : DFA α} {h : Nat}

structure Actual (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old : Nat) (anchors : Array (Option Nat)) (p : Part) : Prop where
  descriptor : (describeLeader partition capacity p.config.descriptor.first).1=some p.config.descriptor
  linked : Linked env st partition capacity old p.config.descriptor.first anchors p.config

theorem region_actual (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat) (anchors : Array (Option Nat))
    (entries : List (Option (Mutable.Store.Entry C E)))
    (current : CurrentEntries env st partition capacity old entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h) (hh : lo≤hi) :
    ∀p,p∈regionParts entries lo hi→Actual env st partition capacity old anchors p := by
  intro p hp
  obtain ⟨first,entry,he,rfl⟩:=(regionParts_mem entries lo hi hh p).mp hp
  have hd:=(current first entry he).descriptor
  have hs:=(describeLeader_sound partition capacity old first hv hc entry.config.descriptor hd).1
  exact ⟨by simpa only [hs] using hd,by simpa only [hs] using linked first entry he⟩

theorem Actual.geometry {env : Clip.Env C E} {st : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity old : Nat} {anchors : Array (Option Nat)} {p : Part}
    (actual : Actual env st partition capacity old anchors p)
    (w : Word α) (fallback : α) (base L : Nat)
    (band : BandGeometry w fallback partition capacity base old L anchors) :
    Geometry (ArrayText.read w.toArray fallback) w.length base L partition.occurrences.entries p.config.descriptor :=
  describeLeader_geometry partition capacity L p.config.descriptor.first band.currentInvariant band.capacity_eq
    p.config.descriptor actual.descriptor (ArrayText.read w.toArray fallback) w.length base band.currentComplete band.positive

theorem Actual.incoming {env : Clip.Env C E} {st : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity old : Nat} {anchors : Array (Option Nat)} {p : Part}
    (actual : Actual env st partition capacity old anchors p)
    (w : Word α) (fallback : α) (base L : Nat)
    (band : BandGeometry w fallback partition capacity base old L anchors) : Incoming w.length p := by
  have hsame:=MaskedTraversalIncoming.populated_length partition capacity w.length old L p.config.descriptor.first
    (ArrayText.read w.toArray fallback) anchors band.oldInvariant band.capacity_eq band.oldAnchors
  have hh:=incoming_bound partition capacity w.length base L p.config.descriptor.first (ArrayText.read w.toArray fallback)
    anchors band.currentInvariant band.capacity_eq band.currentComplete band.positive
    (fun first d hd=>(band.currentAnchors first (by simp) d hd).bounds) p.config.descriptor actual.descriptor
  simpa only [Incoming,hsame,←actual.linked.incoming,←actual.linked.enabled] using hh

theorem Actual.safe {env : Clip.Env C E} {st : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity old : Nat} {anchors : Array (Option Nat)} {p : Part}
    (actual : Actual env st partition capacity old anchors p)
    (w : Word α) (fallback : α) (base L : Nat)
    (band : BandGeometry w fallback partition capacity base old L anchors) : Safe w.length L p := by
  have geom:=actual.geometry w fallback base L band
  obtain ⟨H,hH,cert⟩:=band.currentAnchors p.config.descriptor.first (by simp) p.config.descriptor actual.descriptor
  have hanchor : p.config.anchor=H := by
    simpa only [readAnchor,hH,Option.getD_some] using actual.linked.anchor
  refine ⟨by rw [hanchor]; exact cert.current,?_⟩
  intro mode hm
  cases mode with
  | false=>
    have hs:=(describeLeader_sound partition capacity old p.config.descriptor.first band.oldInvariant band.capacity_eq
      p.config.descriptor actual.descriptor).2.first_le_last
    exact Nat.le_trans hs (Nat.le_of_lt geom.next_strict)
  | true=>
    have en : p.config.incomingEnabled=true := by simpa only [modeAllowed,Bool.not_true,Bool.false_or] using hm
    have hn:=(actual.incoming w fallback base L band) en
    by_cases hz : p.config.descriptor.repetitions=0
    · simpa only [if_pos hz] using hn.2
    · have hmul:=Nat.mul_le_mul_right p.config.descriptor.period (show 1≤p.config.descriptor.repetitions by omega)
      simp only [Nat.one_mul] at hmul
      rw [if_neg hz] at hn
      have hend:=geom.endpoint
      have hnext:=geom.next_strict
      change p.config.incoming≤p.config.descriptor.nextAt w.length
      omega

def Compatible (n : Nat) (p q : Part) : Prop :=
  (∀mode,q.input mode=p.output n mode) ∧
    (p.output n false<p.output n true→q.config.incomingEnabled=true)

theorem Actual.compatible {env : Clip.Env C E} {st : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity old : Nat} {anchors : Array (Option Nat)} {p q : Part}
    (hp : Actual env st partition capacity old anchors p) (hq : Actual env st partition capacity old anchors q)
    (w : Word α) (fallback : α) (base L : Nat)
    (band : BandGeometry w fallback partition capacity base old L anchors)
    (hs : MaskedOrdered.Tree.SuccSpec partition.leaders.entries p.config.descriptor.first (some q.config.descriptor.first))
    (hr : MaskedOrdered.Tree.PredSpec partition.leaders.entries q.config.descriptor.first (some p.config.descriptor.first)) :
    Compatible w.length p q := by
  have sound:=(describeLeader_sound partition capacity old p.config.descriptor.first band.oldInvariant band.capacity_eq
    p.config.descriptor hp.descriptor).2
  have hnext:=MaskedOrdered.succ_unique _ _ _ _ sound.nextSpec hs
  have hpred:=MaskedOrdered.pred_unique _ _ _ _
    (MaskedOrdered.Tree.pred_correct partition.leaders capacity q.config.descriptor.first
      band.oldInvariant.leadGood band.oldInvariant.leadFits band.capacity_eq) hr
  have hi : q.config.incoming=p.config.descriptor.last+p.config.anchor := by
    simp only [hq.linked.incoming,MaskedTraversalBankReady.incoming,hpred,hp.descriptor,←hp.linked.anchor]
  have he : q.config.incomingEnabled=decide (q.config.descriptor.first<p.config.descriptor.last+p.config.anchor) := by
    simp only [hq.linked.enabled,MaskedTraversalBankReady.incoming,hpred,hp.descriptor,←hp.linked.anchor]
  have hend:=(hp.geometry w fallback base L band).endpoint
  constructor
  · intro mode
    cases mode <;> simp only [Part.input,cursor,Part.output,outputCursor,Bool.false_eq_true,if_false,if_true,
      Descriptor.nextAt,hnext,Option.getD_some,hi,hend]
  · intro hover
    rw [he,decide_eq_true_eq]
    simpa only [Part.output,outputCursor,Bool.false_eq_true,if_false,if_true,Descriptor.nextAt,hnext,Option.getD_some,hend]
      using hover

theorem Actual.terminal {env : Clip.Env C E} {st : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity old : Nat} {anchors : Array (Option Nat)} {p : Part}
    (hp : Actual env st partition capacity old anchors p) (n : Nat)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (hs : MaskedOrdered.Tree.SuccSpec partition.leaders.entries p.config.descriptor.first none) :
    p.output n false=n := by
  have sound:=(describeLeader_sound partition capacity old p.config.descriptor.first hv hc p.config.descriptor hp.descriptor).2
  have hnext:=MaskedOrdered.succ_unique _ _ _ _ sound.nextSpec hs
  simp only [Part.output,outputCursor,Bool.false_eq_true,if_false,Descriptor.nextAt,hnext,Option.getD_none]

theorem interfaces (n : Nat) (parts : List Part)
    (adjacent : ∀before p q after,parts=before++p::q::after→Compatible n p q)
    (terminal : ∀before p,parts=before++[p]→p.output n false=n) :
    Enabled n parts ∧ ∃entry finish,Continuous n parts entry finish ∧ finish false=n := by
  induction parts with
  | nil=>exact ⟨True.intro,(fun _=>n),(fun _=>n),Continuous.nil _,rfl⟩
  | cons p ps ih=>
    have ha : ∀before q r after,ps=before++q::r::after→Compatible n q r := by
      intro before q r after he
      exact adjacent (p::before) q r after (by simp only [List.cons_append,he])
    have ht : ∀before q,ps=before++[q]→q.output n false=n := by
      intro before q he
      exact terminal (p::before) q (by simp only [List.cons_append,he])
    have hh:=ih ha ht
    cases ps with
    | nil=>
      refine ⟨⟨?_,True.intro⟩,p.input,p.output n,Continuous.cons p [] _ _ (fun _ _=>rfl) (Continuous.nil _),?_⟩
      · intro q he; cases he
      · exact terminal [] p rfl
    | cons q qs=>
      have hpair:=adjacent [] p q qs rfl
      obtain ⟨hen,entry,finish,hcont,hend⟩:=hh
      cases hcont with
      | cons _ _ _ _ ent rest=>
        refine ⟨⟨?_,hen⟩,p.input,finish,?_,hend⟩
        · intro r he hover
          have heq : q=r := Option.some.inj he
          subst r
          exact hpair.2 hover
        · exact Continuous.cons p (q::qs) _ _ (fun _ _=>rfl)
            (Continuous.cons q qs _ _ (fun mode _=>hpair.1 mode) rest)

theorem actual_interfaces (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L : Nat) (anchors : Array (Option Nat))
    (w : Word α) (fallback : α) (band : BandGeometry w fallback partition capacity base old L anchors)
    (parts : List Part) (keys : firsts parts=partition.leaders.entries)
    (actual : ∀p,p∈parts→Actual env st partition capacity old anchors p) :
    Enabled w.length parts ∧ ∃entry finish,Continuous w.length parts entry finish ∧ finish false=w.length := by
  have ordered : (firsts parts).Pairwise (·<·) := by
    rw [keys]; exact MaskedOrdered.Tree.ordered partition.leaders 0 band.oldInvariant.leadFits
  apply interfaces
  · intro before p q after he
    have hp:=actual p (by rw [he]; exact List.mem_append_right before List.mem_cons_self)
    have hq:=actual q (by rw [he]; exact List.mem_append_right before (List.mem_cons_of_mem p List.mem_cons_self))
    have hk : firsts parts=firsts before++p.config.descriptor.first::q.config.descriptor.first::firsts after := by
      simp only [he,firsts,List.map_append,List.map_cons]
    have hh:=adjacent_specs p.config.descriptor.first q.config.descriptor.first (firsts before) (firsts after) (by rw [←hk]; exact ordered)
    rw [←hk,keys] at hh
    exact hp.compatible hq w fallback base L band hh.1 hh.2
  · intro before p he
    have hp:=actual p (by rw [he]; exact List.mem_append_right before List.mem_cons_self)
    have hk : firsts parts=firsts before++[p.config.descriptor.first] := by simp only [he,firsts,List.map_append,List.map_cons,List.map_nil]
    have hh:=last_spec p.config.descriptor.first (firsts before) (by rw [←hk]; exact ordered)
    rw [←hk,keys] at hh
    exact hp.terminal w.length band.oldInvariant band.capacity_eq hh

end REWB.MaskedTraversalComplete
