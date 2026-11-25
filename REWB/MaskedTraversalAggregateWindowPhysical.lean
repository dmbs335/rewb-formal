import REWB.MaskedTraversalAggregateClippedModel

/-! The actual bounded window query is equivalent to a literal physical
cursor path at one common accepted length. Readiness, every cell's
meaning and the clipped leaf model are derived from concrete maintained
state. No supplied bank-answer or cell-semantics premise remains.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h : Nat}

def windowParts (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (entries : List (Option (Mutable.Store.Entry C E))) : List Part :=
  regionParts (clipEntries env st (Clip.plan partition.leaders capacity lo hi).keys old lo hi entries)
    (Clip.plan partition.leaders capacity lo hi).lower hi

theorem window_denotes (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L lo hi : Nat)
    (anchors : Array (Option Nat)) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (represented : Represents tree entries)
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (w : Word α) (fallback : α) (geometry : BandGeometry w fallback partition capacity base old L anchors)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hK : st.sources.modulus=env.prepared.K)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hwindow : lo<hi) :
    Denotes C E w L source removed env.target
      (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (base+L) (base+old))))
      (regionCells (Clip.window env st partition capacity old lo hi tree).update.tree.leaves
        (Clip.window env st partition capacity old lo hi tree).lower hi)
      (windowParts env st partition capacity old lo hi entries) := by
  have ready:=window_ready env st partition capacity old lo hi entries coherent complete
    geometry.oldInvariant geometry.capacity_eq tree hwindow
  have represented':=(window_represents env st partition capacity old lo hi tree entries represented ready).2
  have keys:=plan_keys_leaders partition capacity old lo hi geometry.oldInvariant geometry.capacity_eq
  have current':=clipEntries_current env st partition capacity old lo hi entries coherent complete _ keys
  have linked':=clipEntries_linked env st partition capacity old lo hi anchors entries coherent complete linked _ keys
  have hh:=CurrentEntries.denotes_region env st partition capacity base old L
    (Clip.plan partition.leaders capacity lo hi).lower hi anchors
    (Clip.window env st partition capacity old lo hi tree).update.tree _ represented' current' linked'
    w fallback geometry source removed hv hn hK hc he
  simpa only [windowParts,Clip.window,hwindow,if_true] using hh

theorem queryWindow_physical (B : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi lo hi : Nat)
    (anchors : Array (Option Nat)) (tree : BankTree C E h) (good : tree.Good)
    (entries : List (Option (Mutable.Store.Entry C E))) (represented : Represents tree entries)
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hK : st.sources.modulus=env.prepared.K)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi) (hwindow : lo<hi) :
    (queryWindow B C E (Cut.build B C E w) env st partition capacity tree lo hi base lengthLo lengthHi old).band.answer=true ↔
      ∃L,lengthLo≤L ∧ L≤lengthHi ∧ B.accepts (Spec.slice w base (base+L)) ∧
        ∃q : Fin E.stateCount,E.final q=true ∧
          PhysicalChain C E w L source removed env.target (windowParts env st partition capacity old lo hi entries)
            (code _ false (MaskedClusterStage.encode C E .waiting))
            (code _ false (MaskedClusterStage.encode C E (.suffix q))) := by
  have low:=geometry lengthLo (Nat.le_refl _) hlength
  have high:=geometry lengthHi hlength (Nat.le_refl _)
  have ready:=window_ready env st partition capacity old lo hi entries coherent complete
    low.oldInvariant low.capacity_eq tree hwindow
  rw [queryWindow_correct B C E w env st partition capacity tree good lo hi base lengthLo lengthHi old
    hlength high.ordered low.representative]
  simp only [ready,true_and]
  constructor
  · rintro ⟨L,hlo,hhi,hB,q,hq,path⟩
    refine ⟨L,hlo,hhi,hB,q,hq,?_⟩
    exact (chain_denotes C E w L source removed env.target _ _ _
      (window_denotes env st partition capacity base old L lo hi anchors tree entries represented coherent complete
        linked w fallback (geometry L hlo hhi) source removed hv hn hK hc he hwindow) _ _).mp path
  · rintro ⟨L,hlo,hhi,hB,q,hq,path⟩
    refine ⟨L,hlo,hhi,hB,q,hq,?_⟩
    exact (chain_denotes C E w L source removed env.target _ _ _
      (window_denotes env st partition capacity base old L lo hi anchors tree entries represented coherent complete
        linked w fallback (geometry L hlo hhi) source removed hv hn hK hc he hwindow) _ _).mpr path

end REWB.MaskedTraversalAggregate.Cells
