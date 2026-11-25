import REWB.MaskedTraversalRepairCoherenceEntry

/-! Exact selected-slot postconditions for the executable successor pass.
Every candidate is an actual current leader. Existing raw metadata may
have an older length, but the pass compiles and stores the current one.
All other slots and the mutable source snapshot are unchanged.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h : Nat}

structure GoodSlot (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (entry : Mutable.Store.Entry C E) : Prop where
  slot : st.slots[first]?.join=some entry
  current : Cells.Current env st partition capacity L first entry
  linked : Cells.Linked env st partition capacity L first anchors entry.config

theorem GoodSlot.ready {env : Clip.Env C E} {st : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity L first : Nat}
    {anchors : Array (Option Nat)} {entry : Mutable.Store.Entry C E}
    (hg : GoodSlot env st partition capacity L first anchors entry) :
    RawReady env st partition capacity L first anchors entry :=
  ⟨hg.slot,hg.current.descriptor,hg.linked.anchor,hg.linked.run⟩

theorem GoodSlot.coherent {env : Clip.Env C E} {st : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity L first : Nat}
    {anchors : Array (Option Nat)} {entry : Mutable.Store.Entry C E}
    (hg : GoodSlot env st partition capacity L first anchors entry) :
    Cells.EntryState env st partition capacity L first entry := by
  refine ⟨hg.current.descriptor,hg.current.current,hg.current.compiled,entry,hg.slot,?_⟩
  rw [←hg.current.current]
  cases entry.config
  rfl

theorem RawReady.transfer {env : Clip.Env C E} {before after : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity L first : Nat}
    {anchors : Array (Option Nat)} {entry : Mutable.Store.Entry C E}
    (hr : RawReady env before partition capacity L first anchors entry)
    (hs : after.sources=before.sources) (hp : after.slots[first]?=before.slots[first]?) :
    RawReady env after partition capacity L first anchors entry := by
  refine ⟨by rw [hp]; exact hr.slot,hr.descriptor,hr.anchor,?_⟩
  rw [hs]
  exact hr.run

theorem GoodSlot.transfer {env : Clip.Env C E} {before after : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity L first : Nat}
    {anchors : Array (Option Nat)} {entry : Mutable.Store.Entry C E}
    (hr : GoodSlot env before partition capacity L first anchors entry)
    (hs : after.sources=before.sources) (hp : after.slots[first]?=before.slots[first]?) :
    GoodSlot env after partition capacity L first anchors entry := by
  refine ⟨by rw [hp]; exact hr.slot,⟨hr.current.descriptor,hr.current.current,?_⟩,
    ⟨hr.linked.anchor,hr.linked.incoming,hr.linked.enabled,?_⟩⟩
  · change (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges after.sources env.target entry.config).1=some entry.bank
    rw [hs]
    exact hr.current.compiled
  · rw [hs]
    exact hr.linked.run

theorem RawComplete.transfer {env : Clip.Env C E} {before after : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity L : Nat} {anchors : Array (Option Nat)}
    (hr : RawComplete env before partition capacity L anchors)
    (hs : after.sources=before.sources) (hp : ∀first : Nat,after.slots[first]?=before.slots[first]?) :
    RawComplete env after partition capacity L anchors := by
  intro first hm
  obtain ⟨raw,hraw⟩:=hr first hm
  exact ⟨raw,hraw.transfer hs (hp first)⟩

def refreshBank (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (st : Mutable.Store.State C E) : Mutable.Store.State C E :=
  MaskedTraversalContext.write C E env.book env.prepared env.cRanges env.eRanges
    partition capacity first L anchors env.target st

theorem refreshBank_selected (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L first : Nat) (anchors : Array (Option Nat))
    (raw : Mutable.Store.Entry C E) (ready : RawReady env st partition capacity L first anchors raw)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hK : st.sources.modulus=env.prepared.K) :
    ∃entry,GoodSlot env (refreshBank env partition capacity L first anchors st)
      partition capacity L first anchors entry := by
  have hpres:=context_present env st partition capacity L first anchors raw ready source removed hv hK
  cases he : (MaskedTraversalContext.compile C E env.book env.prepared env.cRanges env.eRanges
      partition capacity first L anchors env.target st).1 with
  | none => rw [he] at hpres; cases hpres
  | some entry =>
    have hs:=context_selected env st partition capacity L first anchors entry raw ready he
    have hb : first<st.slots.size := by
      by_cases hb : first<st.slots.size
      · exact hb
      · have hn:=Array.getElem?_eq_none (xs:=st.slots) (i:=first) (by omega)
        have hh:=ready.slot
        simp only [hn,Option.join,Option.bind] at hh
        cases hh
    refine ⟨entry,?_,⟨hs.1.descriptor,hs.1.current,hs.1.compiled⟩,
      ⟨hs.2.anchor,hs.2.incoming,hs.2.enabled,hs.2.run⟩⟩
    change ((st.slots.setIfInBounds first _)[first]?).join=some entry
    rw [Array.getElem?_setIfInBounds_self_of_lt hb]
    exact he

theorem refreshBank_raw (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L p : Nat) (anchors : Array (Option Nat))
    (hr : RawComplete env st partition capacity L anchors)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hK : st.sources.modulus=env.prepared.K) :
    RawComplete env (refreshBank env partition capacity L p anchors st) partition capacity L anchors := by
  intro first hm
  obtain ⟨raw,hraw⟩:=hr first hm
  by_cases he : p=first
  · subst p
    obtain ⟨entry,hentry⟩:=refreshBank_selected env st partition capacity L first anchors raw hraw source removed hv hK
    exact ⟨entry,hentry.ready⟩
  · refine ⟨raw,hraw.transfer rfl ?_⟩
    exact MaskedTraversalContext.write_other C E env.book env.prepared env.cRanges env.eRanges
      partition capacity p first L anchors env.target st he

def refreshLoop (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (ps : List Nat) (st : Mutable.Store.State C E) : Mutable.Store.State C E :=
  MaskedTraversalContext.applyLoop C E env.book env.prepared env.cRanges env.eRanges
    partition capacity L anchors env.target ps st

theorem refreshLoop_sources (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (ps : List Nat) (st : Mutable.Store.State C E) :
    (refreshLoop env partition capacity L anchors ps st).sources=st.sources :=
  MaskedTraversalContext.applyLoop_sources C E env.book env.prepared env.cRanges env.eRanges
    partition capacity L anchors env.target ps st

theorem refreshLoop_other (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (ps : List Nat) (st : Mutable.Store.State C E) (hn : first∉ps) :
    (refreshLoop env partition capacity L anchors ps st).slots[first]?=st.slots[first]? := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih =>
    have hne : p≠first := by intro he; subst p; exact hn List.mem_cons_self
    have ht : first∉ps := fun hh=>hn (List.mem_cons_of_mem p hh)
    change (refreshLoop env partition capacity L anchors ps
      {refreshBank env partition capacity L p anchors st with
        repairWork:=(refreshBank env partition capacity L p anchors st).repairWork+3}).slots[first]?=_
    rw [ih _ ht]
    exact MaskedTraversalContext.write_other C E env.book env.prepared env.cRanges env.eRanges
      partition capacity p first L anchors env.target st hne

theorem refreshLoop_raw (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (ps : List Nat) (st : Mutable.Store.State C E)
    (hr : RawComplete env st partition capacity L anchors)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hK : st.sources.modulus=env.prepared.K) :
    RawComplete env (refreshLoop env partition capacity L anchors ps st) partition capacity L anchors := by
  induction ps generalizing st with
  | nil => exact hr.transfer rfl (fun _=>rfl)
  | cons p ps ih =>
    have hh:=refreshBank_raw env st partition capacity L p anchors hr source removed hv hK
    exact ih _ (hh.transfer rfl (fun _=>rfl)) hv hK

theorem refreshLoop_selected (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (ps : List Nat) (st : Mutable.Store.State C E)
    (hr : RawComplete env st partition capacity L anchors)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hK : st.sources.modulus=env.prepared.K)
    (hp : first∈ps) (hm : first∈partition.leaders.entries) :
    ∃entry,GoodSlot env (refreshLoop env partition capacity L anchors ps st)
      partition capacity L first anchors entry := by
  induction ps generalizing st with
  | nil => cases hp
  | cons p ps ih =>
    have hh:=refreshBank_raw env st partition capacity L p anchors hr source removed hv hK
    by_cases ht : first∈ps
    · exact ih _ (hh.transfer rfl (fun _=>rfl)) hv hK ht
    · have he : first=p := (List.mem_cons.mp hp).resolve_right ht
      subst p
      obtain ⟨raw,hraw⟩:=hr first hm
      obtain ⟨entry,hentry⟩:=refreshBank_selected env st partition capacity L first anchors raw hraw source removed hv hK
      refine ⟨entry,?_⟩
      apply hentry.transfer
      · exact refreshLoop_sources env partition capacity L anchors ps _
      · exact refreshLoop_other env partition capacity L first anchors ps _ ht

end REWB.MaskedTraversalRepairCoherence
