import REWB.MaskedTraversalCompleteSound

/-! Exact cross-cluster semantics of the actual temporary window query.
The finite bank path is both sound and complete for original text cuts
with distinct actual owner queries. The same-cluster periodic branch is
separate; it is not silently included in this path primitive. -/
namespace REWB.MaskedTraversalComplete
open REWB.Spec REWB.MaskedCluster REWB.MaskedTraversalAggregate REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h : Nat}

def owner (partition : MaskedClusterLeaders.State h) (capacity p : Nat) : Nat :=
  (locate partition capacity p).1.getD 0

theorem Actual.owner {env : Clip.Env C E} {st : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity old : Nat} {anchors : Array (Option Nat)} {p : Part}
    (actual : Actual env st partition capacity old anchors p)
    (w : Word α) (fallback : α) (base L : Nat)
    (band : BandGeometry w fallback partition capacity base old L anchors)
    (k : Nat) (hk : k≤p.config.descriptor.repetitions) :
    owner partition capacity (position p k)=p.config.descriptor.first := by
  have hm:=((actual.geometry w fallback base L band).members (position p k)).mpr ⟨k,hk,rfl⟩
  have hl:=locate_descriptor partition capacity L p.config.descriptor.first band.currentInvariant band.capacity_eq
    p.config.descriptor actual.descriptor (position p k) hm.1 hm.2.1 hm.2.2
  change ((locate partition capacity (position p k)).1).getD 0=p.config.descriptor.first
  rw [hl]
  rfl

theorem window_sound (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L lo hi : Nat) (anchors : Array (Option Nat))
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (w : Word α) (fallback : α) (band : BandGeometry w fallback partition capacity base old L anchors)
    (unclipped : Unclipped w.length entries) (hw : lo<hi)
    (source : Array Bool) (removed : List Nat)
    (q : Fin E.stateCount) (hf : E.final q=true)
    (path : PhysicalChain C E w L source removed env.target (windowParts env st partition capacity old lo hi entries)
      (stageCode C E false .waiting) (stageCode C E false (.suffix q))) :
    ∃p j,windowSource partition source removed lo hi p ∧ classTarget partition env.target j ∧
      (locate partition capacity p).1≠(locate partition capacity j).1 ∧ p+L≤j ∧ j+L≤w.length ∧
      C.accepts (slice w (p+L) j) ∧ E.accepts (slice w (j+L) w.length) := by
  let ps:=windowParts env st partition capacity old lo hi entries
  have keys:=window_keys env st partition capacity old lo hi entries coherent complete band.oldInvariant band.capacity_eq hw
  have actual:=window_actual env st partition capacity old lo hi anchors entries coherent complete linked
    band.oldInvariant band.capacity_eq hw
  have hordered : ps.Pairwise (fun a b=>a.config.descriptor.first<b.config.descriptor.first) := by
    apply List.pairwise_map.mp (show (firsts ps).Pairwise (·<·) from ?_)
    rw [keys]
    exact MaskedOrdered.Tree.ordered partition.leaders 0 band.oldInvariant.leadFits
  obtain ⟨_,entryAt,finish,continuous,endAt⟩:=actual_interfaces env st partition capacity base old L anchors
    w fallback band ps keys actual
  have marks:=windowParts_marks env st partition capacity base old lo hi entries coherent complete unclipped
    band.oldInvariant band.capacity_eq (ArrayText.read w.toArray fallback) band.oldComplete source removed hw
  have hh:=tracked_final C E w L source removed env.target (owner partition capacity)
    (windowSource partition source removed lo hi) (classTarget partition env.target) ps entryAt finish continuous endAt
    hordered (fun p hp=>(actual p hp).safe w fallback base L band) marks
    (fun p hp k hk=>(actual p hp).owner w fallback base L band k hk) q hf path
  obtain ⟨p,j,hp,hj,hkeys,horder,hbound,hC,hE⟩:=hh
  refine ⟨p,j,hp,hj,?_,horder,hbound,hC,hE⟩
  intro he
  have hsame : owner partition capacity p=owner partition capacity j := congrArg (fun x : Option Nat=>x.getD 0) he
  rw [hsame] at hkeys
  exact Nat.lt_irrefl _ hkeys

theorem window_path_iff (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L lo hi : Nat) (anchors : Array (Option Nat))
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (w : Word α) (fallback : α) (band : BandGeometry w fallback partition capacity base old L anchors)
    (unclipped : Unclipped w.length entries) (hw : lo<hi) (source : Array Bool) (removed : List Nat) :
    (∃q : Fin E.stateCount,E.final q=true ∧
      PhysicalChain C E w L source removed env.target (windowParts env st partition capacity old lo hi entries)
        (stageCode C E false .waiting) (stageCode C E false (.suffix q))) ↔
    ∃p j,windowSource partition source removed lo hi p ∧ classTarget partition env.target j ∧
      (locate partition capacity p).1≠(locate partition capacity j).1 ∧ p+L≤j ∧ j+L≤w.length ∧
      C.accepts (slice w (p+L) j) ∧ E.accepts (slice w (j+L) w.length) := by
  constructor
  · rintro ⟨q,hf,path⟩
    exact window_sound env st partition capacity base old L lo hi anchors entries coherent complete linked
      w fallback band unclipped hw source removed q hf path
  · rintro ⟨p,j,hp,hj,hne,horder,hbound,hC,hE⟩
    exact window_complete env st partition capacity base old L lo hi anchors entries coherent complete linked
      w fallback band unclipped hw source removed p j hp hj hne horder hbound hC hE

def BandGood (B C E : DFA α) (w : Word α) (partition : MaskedClusterLeaders.State h)
    (capacity lengthLo lengthHi : Nat) (source : Array Bool) (removed : List Nat) (target : Array Bool) (p : Nat) : Prop :=
  Mutable.Batch.currentBit source removed p=true ∧ p∈partition.occurrences.entries ∧
    ∃L,lengthLo≤L ∧ L≤lengthHi ∧ ∃j,j∈partition.occurrences.entries ∧ MaskedProgression.readMask target j=true ∧
      (locate partition capacity p).1≠(locate partition capacity j).1 ∧ p+L≤j ∧ j+L≤w.length ∧
      B.accepts (slice w p (p+L)) ∧ C.accepts (slice w (p+L) j) ∧ E.accepts (slice w (j+L) w.length)

theorem class_slice (w : Word α) (fallback : α) (partition : MaskedClusterLeaders.State h)
    (capacity base old L : Nat) (anchors : Array (Option Nat))
    (band : BandGeometry w fallback partition capacity base old L anchors)
    (p : Nat) (hp : p∈partition.occurrences.entries) :
    slice w p (p+L)=slice w base (base+L) := by
  have hh:=(band.currentComplete p).mp hp
  have hbase : base+L≤w.length := Nat.le_trans (Nat.add_le_add_left band.ordered base) band.representative
  have he:=hh.2
  rw [ArrayText.segment_word w fallback p L hh.1,ArrayText.segment_word w fallback base L hbase] at he
  simpa only [slice,Nat.add_sub_cancel_left] using he

theorem queryWindow_iff (B : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi lo hi : Nat)
    (anchors : Array (Option Nat)) (tree : BankTree C E h) (good : tree.Good)
    (entries : List (Option (Mutable.Store.Entry C E))) (represented : Represents tree entries)
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (unclipped : Unclipped w.length entries)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hK : st.sources.modulus=env.prepared.K)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi) :
    (queryWindow B C E (Cut.build B C E w) env st partition capacity tree lo hi base lengthLo lengthHi old).band.answer=true ↔
      ∃p,lo≤p ∧ p<hi ∧ BandGood B C E w partition capacity lengthLo lengthHi source removed env.target p := by
  by_cases hw : lo<hi
  · rw [queryWindow_physical B env st partition capacity base old lengthLo lengthHi lo hi anchors tree good entries
      represented coherent complete linked w fallback geometry source removed hv hn hK hc he hlength hw]
    constructor
    · rintro ⟨L,hlo,hhi,hB,q,hf,path⟩
      obtain ⟨p,j,hp,hj,hne,horder,hbound,hC,hE⟩:=window_sound env st partition capacity base old L lo hi anchors entries
        coherent complete linked w fallback (geometry L hlo hhi) unclipped hw source removed q hf path
      refine ⟨p,hp.2.1,hp.2.2.1,hp.2.2.2,hp.1,L,hlo,hhi,j,hj.1,hj.2,hne,horder,hbound,?_,hC,hE⟩
      rw [class_slice w fallback partition capacity base old L anchors (geometry L hlo hhi) p hp.1]
      exact hB
    · rintro ⟨p,hplo,hphi,hbit,hp,L,hlo,hhi,j,hj,htarget,hne,horder,hbound,hB,hC,hE⟩
      refine ⟨L,hlo,hhi,?_,?_⟩
      · rw [←class_slice w fallback partition capacity base old L anchors (geometry L hlo hhi) p hp]
        exact hB
      · exact window_complete env st partition capacity base old L lo hi anchors entries coherent complete linked
          w fallback (geometry L hlo hhi) unclipped hw source removed p j ⟨hp,hplo,hphi,hbit⟩ ⟨hj,htarget⟩
          hne horder hbound hC hE
  · simp only [queryWindow,Clip.window,hw,if_false,Bool.false_eq_true,rejectedBand,false_iff]
    rintro ⟨p,hlo,hhi,_⟩
    omega

end REWB.MaskedTraversalComplete
