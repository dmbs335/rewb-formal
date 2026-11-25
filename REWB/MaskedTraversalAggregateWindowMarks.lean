import REWB.MaskedTraversalAggregateRegionModel

/-! Exact source eligibility in the actual temporary window banks.
Original windows cover the input; immutable target bits are never
clipped. AP ownership comes from complete unmasked occurrences.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h : Nat}

def Unclipped (n : Nat) (entries : List (Option (Mutable.Store.Entry C E))) : Prop :=
  ∀(first : Nat) (entry : Mutable.Store.Entry C E),entries[first]?=some (some entry)→
    entry.config.window=⟨true,0,n+1⟩

theorem candidate_owner (partition : MaskedClusterLeaders.State h) (capacity old first : Nat)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (n base : Nat) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (d : MaskedClusterDescriptor.Descriptor) (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some d)
    (k : Nat) (hk : k≤d.repetitions) :
    d.first+k*d.period∈partition.occurrences.entries ∧ d.first+k*d.period≤n ∧
      MaskedOrdered.Tree.PredSpec partition.leaders.entries (d.first+k*d.period+1) (some first) := by
  have hp:=MaskedClusterDescriptor.describeLeader_progression partition capacity old first hv hc d hd f n base hfull
  have hm:=(hp.2.2 _).mpr ⟨k,hk,rfl⟩
  have ho:=MaskedClusterDescriptor.locate_descriptor partition capacity old first hv hc d hd _ hm.1 hm.2.1 hm.2.2
  have owned:=(MaskedClusterDescriptor.locate_correct partition capacity old _ first hv hc).mp ho
  have hb:=((hfull _).mp hm.1).1
  refine ⟨hm.1,by omega,owned.2.1,by have hh:=owned.2.2.1; omega,?_⟩
  intro q hq hqp
  exact owned.2.2.2 q hq (by omega)

theorem clipped_source_iff (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lo hi first : Nat)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (unclipped : Unclipped n entries)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (source : Array Bool) (removed : List Nat) (entry : Mutable.Store.Entry C E)
    (he : (clipEntries env st (Clip.plan partition.leaders capacity lo hi).keys old lo hi entries)[first]?=some (some entry))
    (k : Nat) (hk : k≤entry.config.descriptor.repetitions) :
    let p:=entry.config.descriptor.first+k*entry.config.descriptor.period
    ((entry.config.window.gate (decide ((Clip.plan partition.leaders capacity lo hi).lower≤first ∧ first<hi))).allows p &&
      Mutable.Batch.currentBit source removed p)=true ↔
      lo≤p ∧ p<hi ∧ Mutable.Batch.currentBit source removed p=true := by
  obtain ⟨before,hbefore,hcfg⟩:=clipEntries_config env st partition capacity old lo hi entries coherent complete _
    (plan_keys_leaders partition capacity old lo hi hv hc) first entry he
  have hdesc : entry.config.descriptor=before.config.descriptor := by
    rw [hcfg]
    split <;> rfl
  have hwindow : entry.config.window=windowFor (Clip.plan partition.leaders capacity lo hi) before.config.window first lo hi := by
    rw [hcfg]
    simp only [windowFor]
    split <;> rfl
  have hk' : k≤before.config.descriptor.repetitions := by simpa only [hdesc] using hk
  have own:=candidate_owner partition capacity old first hv hc f n base hfull before.config.descriptor
    (coherent first before hbefore).descriptor k hk'
  have hall : before.config.window.allows (before.config.descriptor.first+k*before.config.descriptor.period)=true := by
    rw [unclipped first before hbefore]
    simp only [SourceWindow.allows,Bool.true_and,decide_eq_true_eq]
    exact ⟨Nat.zero_le _,by have hh:=own.2.1; omega⟩
  dsimp only
  rw [hdesc,hwindow]
  exact windowFor_current partition.leaders capacity lo hi first _ before.config.window hall source removed
    hv.leadGood hv.leadFits hc own.2.2

def windowSource (partition : MaskedClusterLeaders.State h) (source : Array Bool) (removed : List Nat)
    (lo hi p : Nat) : Prop :=
  p∈partition.occurrences.entries ∧ lo≤p ∧ p<hi ∧ Mutable.Batch.currentBit source removed p=true

def classTarget (partition : MaskedClusterLeaders.State h) (target : Array Bool) (p : Nat) : Prop :=
  p∈partition.occurrences.entries ∧ MaskedProgression.readMask target p=true

theorem windowParts_marks (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lo hi : Nat)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (unclipped : Unclipped n entries)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (source : Array Bool) (removed : List Nat) (hwindow : lo<hi) :
    ∀p,p∈windowParts env st partition capacity old lo hi entries→
      Marks source removed env.target (windowSource partition source removed lo hi) (classTarget partition env.target) p := by
  intro part hpart
  have hlo:=plan_lower_le partition capacity old lo hi hv hc
  obtain ⟨first,entry,he,hpart⟩:=(regionParts_mem _ _ _ (by omega) part).mp hpart
  subst part
  have current:=clipEntries_current env st partition capacity old lo hi entries coherent complete _
    (plan_keys_leaders partition capacity old lo hi hv hc) first entry he
  constructor
  · intro k hk hgate hsource
    have hsel:=(clipped_source_iff env st partition capacity base old lo hi first entries coherent complete unclipped
      hv hc f hfull source removed entry he k hk).mp (Bool.and_eq_true_iff.mpr ⟨hgate,hsource⟩)
    exact ⟨(candidate_owner partition capacity old first hv hc f n base hfull entry.config.descriptor current.descriptor k hk).1,hsel⟩
  · intro k hk htarget
    exact ⟨(candidate_owner partition capacity old first hv hc f n base hfull entry.config.descriptor current.descriptor k hk).1,htarget⟩

end REWB.MaskedTraversalAggregate.Cells
