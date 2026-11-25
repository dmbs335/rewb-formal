import REWB.MaskedTraversalCompleteGeometry
import REWB.MaskedTraversalAggregateWindowMarks

/-! Distinct physical cluster witnesses yield a path through the actual
temporarily clipped indexed banks. Occurrence membership, AP indices,
chronological order, source eligibility and cursor interfaces are all
derived from the concrete maintained model. -/
namespace REWB.MaskedTraversalComplete
open REWB.Spec REWB.MaskedCluster REWB.MaskedTraversalAggregate REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h : Nat}

theorem ordered_split (parts : List Part) (p q : Part) (hp : p∈parts) (hq : q∈parts)
    (ordered : parts.Pairwise (fun p q=>p.config.descriptor.first<q.config.descriptor.first))
    (hlt : p.config.descriptor.first<q.config.descriptor.first) :
    ∃before between after,parts=before++p::(between++q::after) := by
  obtain ⟨before,tail,he⟩:=List.mem_iff_append.mp hp
  rw [he] at ordered hq
  have hcross:=(List.pairwise_append.mp ordered).2.2
  have htail : q∈tail := by
    rcases List.mem_append.mp hq with hm|hm
    · have hh:=hcross q hm p List.mem_cons_self
      omega
    · rcases List.mem_cons.mp hm with hh|hh
      · subst q; exact False.elim (Nat.lt_irrefl _ hlt)
      · exact hh
  obtain ⟨between,after,ht⟩:=List.mem_iff_append.mp htail
  exact ⟨before,between,after,by rw [he,ht]⟩

theorem owner_order (partition : MaskedClusterLeaders.State h) (p j first second : Nat)
    (hp : Owns partition p first) (hj : Owns partition j second) (horder : p≤j) (hne : first≠second) :
    first<second := by
  have hh:=hj.2.2.2 first hp.2.1 (Nat.le_trans hp.2.2.1 horder)
  omega

theorem actual_member (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L : Nat) (anchors : Array (Option Nat))
    (w : Word α) (fallback : α) (band : BandGeometry w fallback partition capacity base old L anchors)
    (parts : List Part) (keys : firsts parts=partition.leaders.entries)
    (actual : ∀p,p∈parts→Actual env st partition capacity old anchors p)
    (x first : Nat) (owned : Owns partition x first) :
    ∃p,p∈parts ∧ p.config.descriptor.first=first ∧ ∃k,k≤p.config.descriptor.repetitions ∧ x=position p k := by
  have hm : first∈firsts parts := by rw [keys]; exact owned.2.1
  obtain ⟨p,hp,hfirst⟩:=List.mem_map.mp hm
  have hd:=actual p hp
  have hs:=(describeLeader_sound partition capacity old p.config.descriptor.first band.oldInvariant band.capacity_eq
    p.config.descriptor hd.descriptor).2
  have hx : Owns partition x p.config.descriptor.first := by rw [hfirst]; exact owned
  have hb:=(hs.owns_iff partition capacity old band.oldInvariant band.capacity_eq p.config.descriptor x).mp hx
  obtain ⟨k,hk,hx⟩:=((hd.geometry w fallback base L band).members x).mp hb
  exact ⟨p,hp,hfirst,k,hk,hx⟩

theorem window_keys (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h) (hw : lo<hi) :
    firsts (windowParts env st partition capacity old lo hi entries)=partition.leaders.entries := by
  have hk:=plan_keys_leaders partition capacity old lo hi hv hc
  have hh:=plan_lower_le partition capacity old lo hi hv hc
  exact regionParts_firsts env st partition capacity old _ hi _
    (clipEntries_current env st partition capacity old lo hi entries coherent complete _ hk)
    (clipEntries_complete env st partition capacity old lo hi entries coherent complete _)
    hv hc (by omega)

theorem window_actual (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat) (anchors : Array (Option Nat))
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h) (hw : lo<hi) :
    ∀p,p∈windowParts env st partition capacity old lo hi entries→Actual env st partition capacity old anchors p := by
  have hk:=plan_keys_leaders partition capacity old lo hi hv hc
  have hh:=plan_lower_le partition capacity old lo hi hv hc
  exact region_actual env st partition capacity old _ hi anchors _
    (clipEntries_current env st partition capacity old lo hi entries coherent complete _ hk)
    (clipEntries_linked env st partition capacity old lo hi anchors entries coherent complete linked _ hk)
    hv hc (by omega)

theorem window_complete (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L lo hi : Nat) (anchors : Array (Option Nat))
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (w : Word α) (fallback : α) (band : BandGeometry w fallback partition capacity base old L anchors)
    (unclipped : Unclipped w.length entries) (hw : lo<hi)
    (source : Array Bool) (removed : List Nat) (p j : Nat)
    (hp : windowSource partition source removed lo hi p) (hj : classTarget partition env.target j)
    (different : (locate partition capacity p).1≠(locate partition capacity j).1)
    (horder : p+L≤j) (hbound : j+L≤w.length)
    (hC : C.accepts (slice w (p+L) j)) (hE : E.accepts (slice w (j+L) w.length)) :
    ∃q : Fin E.stateCount,E.final q=true ∧
      PhysicalChain C E w L source removed env.target (windowParts env st partition capacity old lo hi entries)
        (stageCode C E false .waiting) (stageCode C E false (.suffix q)) := by
  let ps:=windowParts env st partition capacity old lo hi entries
  have keys:=window_keys env st partition capacity old lo hi entries coherent complete band.oldInvariant band.capacity_eq hw
  have actual:=window_actual env st partition capacity old lo hi anchors entries coherent complete linked
    band.oldInvariant band.capacity_eq hw
  obtain ⟨first,hfirst⟩:=locate_exists partition capacity old p band.oldInvariant band.capacity_eq hp.1
  obtain ⟨second,hsecond⟩:=locate_exists partition capacity old j band.oldInvariant band.capacity_eq hj.1
  have sourceOwn:=(locate_correct partition capacity old p first band.oldInvariant band.capacity_eq).mp hfirst
  have targetOwn:=(locate_correct partition capacity old j second band.oldInvariant band.capacity_eq).mp hsecond
  have hne : first≠second := by intro he; apply different; rw [hfirst,hsecond,he]
  have hlt:=owner_order partition p j first second sourceOwn targetOwn (by omega) hne
  obtain ⟨a,ha,hfa,k,hk,hpPos⟩:=actual_member env st partition capacity base old L anchors w fallback band ps keys actual p first sourceOwn
  obtain ⟨b,hb,hfb,l,hl,hjPos⟩:=actual_member env st partition capacity base old L anchors w fallback band ps keys actual j second targetOwn
  have hordered : ps.Pairwise (fun a b=>a.config.descriptor.first<b.config.descriptor.first) := by
    apply List.pairwise_map.mp (show (firsts ps).Pairwise (·<·) from ?_)
    rw [keys]
    exact MaskedOrdered.Tree.ordered partition.leaders 0 band.oldInvariant.leadFits
  obtain ⟨before,between,after,hsplit⟩:=ordered_split ps a b ha hb hordered (by rw [hfa,hfb]; exact hlt)
  have hsrc : ((a.config.window.gate a.gate).allows (position a k) && Mutable.Batch.currentBit source removed (position a k))=true := by
    have hlo:=plan_lower_le partition capacity old lo hi band.oldInvariant band.capacity_eq
    obtain ⟨key,entry,he,haEq⟩:=(regionParts_mem _ _ _ (by omega) a).mp ha
    cases haEq
    dsimp only [position] at hpPos
    exact (clipped_source_iff env st partition capacity base old lo hi key entries coherent complete unclipped
      band.oldInvariant band.capacity_eq (ArrayText.read w.toArray fallback) band.oldComplete source removed entry he k hk).mpr
        (by simpa only [←hpPos] using hp.2)
  have geometry:=actual_interfaces env st partition capacity base old L anchors w fallback band ps keys actual
  obtain ⟨enabled,entryAt,finish,continuous,endAt⟩:=geometry
  have hsafe : ∀r,r∈ps→Safe w.length L r := fun r hr=>(actual r hr).safe w fallback base L band
  have hin:=(actual b hb).incoming w fallback base L band
  have ht : MaskedProgression.readMask env.target (position b l)=true := by rw [←hjPos]; exact hj.2
  have hCo : C.accepts (slice w (position a k+L) (position b l)) := by rw [←hpPos,←hjPos]; exact hC
  change ∃q : Fin E.stateCount,E.final q=true ∧ PhysicalChain C E w L source removed env.target ps
    (stageCode C E false .waiting) (stageCode C E false (.suffix q))
  rw [hsplit] at continuous enabled hsafe ⊢
  refine ⟨E.run E.initial (slice w (position b l+L) w.length),?_,?_⟩
  · rw [←hjPos]; exact hE
  · exact two_jumps C E w L source removed env.target before between after a b k l entryAt finish continuous endAt
      hsafe enabled hin hk hl hsrc ht (by rw [←hpPos,←hjPos]; exact horder)
      (by rw [←hjPos]; exact hbound) hCo

end REWB.MaskedTraversalComplete
