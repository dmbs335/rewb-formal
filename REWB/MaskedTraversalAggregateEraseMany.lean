import REWB.MaskedTraversalAggregateActualCost
import REWB.MaskedTraversalAggregateWindowMarks

/-! Actual batch source removal after reporting a band. The executable
fold updates the shared source batch and one current bank per affected
source. Local repair work and the source batch's fanout ledger are
separate counters; the charged theorem below combines both. The sparse
entry lists and deleted histories below are proof
models only. Every intermediate repair is proved ready and coherent.
-/
namespace REWB.MaskedTraversalAggregate
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h : Nat}

def eraseStep (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (acc : SourceChange C E h) (p : Nat) : SourceChange C E h :=
  let out:=eraseCurrent env partition capacity old p acc.store acc.tree
  {out with ready:=acc.ready && out.ready,work:=acc.work+out.work+1,calls:=acc.calls+out.calls}

def eraseMany (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (positions : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) : SourceChange C E h :=
  positions.foldl (eraseStep env partition capacity old) ⟨st,tree,true,0,0⟩

namespace Cells

theorem eraseMany_sources (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (positions : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseMany env partition capacity old positions st tree).store.sources=
      MaskedMutableProgression.Batch.eraseMany positions st.sources := by
  have go : ∀(ps : List Nat) (acc : SourceChange C E h),
      (ps.foldl (eraseStep env partition capacity old) acc).store.sources=
        MaskedMutableProgression.Batch.eraseMany ps acc.store.sources := by
    intro ps
    induction ps with
    | nil=>intro acc; rfl
    | cons p ps ih=>
      intro acc
      rw [List.foldl_cons,ih]
      simp only [eraseStep,eraseCurrent_sources,MaskedMutableProgression.Batch.eraseMany,List.foldl_cons]
  exact go positions ⟨st,tree,true,0,0⟩

def Maintained (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old n : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) : Prop :=
  MaskedMutableProgression.Batch.Valid source removed st.sources ∧ st.sources.n=n ∧
    st.sources.modulus=env.prepared.K ∧ tree.Good ∧
      ∃entries,Represents tree entries ∧ Coherent env st partition capacity old entries ∧
        CompleteModel partition entries ∧ LinkedEntries env st partition capacity old anchors entries ∧ Unclipped n entries

theorem eraseCurrent_unclipped (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old n p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (unclipped : Unclipped n entries) (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) :
    Unclipped n (erasedEntries env partition capacity old p st tree entries) := by
  intro first entry he
  obtain ⟨before,hbefore,hcfg⟩:=erasedEntries_config env partition capacity old p st tree entries hi hc
    coherent complete source removed hv first entry he
  rw [hcfg]
  exact unclipped first before hbefore

theorem eraseCurrent_maintained (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old n p : Nat) (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (base : Nat) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (hm : Maintained env partition capacity old n anchors source removed st tree) :
    (eraseCurrent env partition capacity old p st tree).ready=true ∧
      Maintained env partition capacity old n anchors source (p::removed)
        (eraseCurrent env partition capacity old p st tree).store (eraseCurrent env partition capacity old p st tree).tree := by
  obtain ⟨hv,hn,hK,hg,entries,hr,hco,hcp,hl,hu⟩:=hm
  have ready:=eraseCurrent_ready env partition capacity old p st tree entries hi hc hco hcp source removed hv
  refine ⟨ready,?_,?_,?_,eraseCurrent_good env partition capacity old p st tree hg,
    erasedEntries env partition capacity old p st tree entries,?_,?_,?_,?_,?_⟩
  · rw [eraseCurrent_sources]
    exact MaskedMutableProgression.Batch.eraseSource_valid hv p
  · rw [eraseCurrent_sources,MaskedMutableProgression.Batch.eraseSource_n,hn]
  · rw [eraseCurrent_sources,MaskedMutableProgression.Batch.eraseSource_modulus,hK]
  · exact eraseCurrent_represents env partition capacity old p st tree entries hr ready
  · exact eraseCurrent_coherent env partition capacity old p st tree entries hi hc f n base hfull hco hcp source removed hv
  · exact eraseCurrent_complete env partition capacity old p st tree entries hi hc hco hcp source removed hv
  · exact eraseCurrent_linked env partition capacity old p st tree anchors entries hi hc hco hcp hl source removed hv
  · exact eraseCurrent_unclipped env partition capacity old n p st tree entries hi hc hco hcp hu source removed hv

theorem eraseMany_maintained (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old n : Nat) (anchors : Array (Option Nat)) (source : Array Bool) (removed positions : List Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (base : Nat) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (hm : Maintained env partition capacity old n anchors source removed st tree) :
    (eraseMany env partition capacity old positions st tree).ready=true ∧
      Maintained env partition capacity old n anchors source (positions.reverse++removed)
        (eraseMany env partition capacity old positions st tree).store (eraseMany env partition capacity old positions st tree).tree := by
  have go : ∀(ps hist : List Nat) (acc : SourceChange C E h),acc.ready=true→
      Maintained env partition capacity old n anchors source hist acc.store acc.tree→
      (ps.foldl (eraseStep env partition capacity old) acc).ready=true ∧
        Maintained env partition capacity old n anchors source (ps.reverse++hist)
          (ps.foldl (eraseStep env partition capacity old) acc).store (ps.foldl (eraseStep env partition capacity old) acc).tree := by
    intro ps
    induction ps with
    | nil=>intro hist acc ready hh; exact ⟨ready,hh⟩
    | cons p ps ih=>
      intro hist acc ready hh
      have one:=eraseCurrent_maintained env partition capacity old n p anchors source hist acc.store acc.tree hi hc f base hfull hh
      have next : (eraseStep env partition capacity old acc p).ready=true := by
        simp only [eraseStep,ready,one.1,Bool.true_and]
      simpa only [List.foldl_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        ih (p::hist) (eraseStep env partition capacity old acc p) next one.2
  exact go positions removed ⟨st,tree,true,0,0⟩ rfl hm

theorem eraseMany_calls (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (positions : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseMany env partition capacity old positions st tree).calls≤positions.length := by
  have go : ∀(ps : List Nat) (acc : SourceChange C E h),
      (ps.foldl (eraseStep env partition capacity old) acc).calls≤acc.calls+ps.length := by
    intro ps
    induction ps with
    | nil=>intro acc; simp only [List.foldl_nil,List.length_nil,Nat.add_zero,Nat.le_refl]
    | cons p ps ih=>
      intro acc
      have hh:=ih (eraseStep env partition capacity old acc p)
      have hc:=eraseCurrent_calls env partition capacity old p acc.store acc.tree
      simp only [List.foldl_cons,List.length_cons]
      simp only [eraseStep] at hh ⊢
      omega
  simpa only [eraseMany,Nat.zero_add] using go positions ⟨st,tree,true,0,0⟩

theorem eraseMany_work (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity base old L : Nat) (anchors : Array (Option Nat)) (source : Array Bool) (removed positions : List Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) (w : Word α) (fallback : α)
    (geometry : BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source removed st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w) :
    (eraseMany env partition capacity old positions st tree).work≤positions.length*(11*h+25+
      Mutable.Store.bankLimit C E env.prepared.K w.length+
        (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
          (2*(MaskedClusterStage.dfa C E).stateCount)) := by
  let budget:=11*h+25+Mutable.Store.bankLimit C E env.prepared.K w.length+
    (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)
  have go : ∀(ps hist : List Nat) (acc : SourceChange C E h),
      Maintained env partition capacity old w.length anchors source hist acc.store acc.tree→
      (ps.foldl (eraseStep env partition capacity old) acc).work≤acc.work+ps.length*budget := by
    intro ps
    induction ps with
    | nil=>intro hist acc _; simp only [List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero,Nat.le_refl]
    | cons p ps ih=>
      intro hist acc hh
      have one:=eraseCurrent_maintained env partition capacity old w.length p anchors source hist acc.store acc.tree
        geometry.oldInvariant geometry.capacity_eq (ArrayText.read w.toArray fallback) base geometry.oldComplete hh
      obtain ⟨hv,hn,_,_,entries,_,hco,hcp,hl,_⟩:=hh
      have hw:=eraseCurrent_actual_work env acc.store partition capacity base old L p anchors acc.tree entries hco hcp hl
        w fallback geometry source hist hv hn hc he
      have ht:=ih (p::hist) (eraseStep env partition capacity old acc p) one.2
      simp only [List.foldl_cons,List.length_cons,Nat.succ_mul]
      simp only [eraseStep] at ht ⊢
      dsimp only [budget] at ht ⊢
      omega
  simpa only [eraseMany,Nat.zero_add] using go positions removed ⟨st,tree,true,0,0⟩ hm

theorem eraseMany_charged (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity base old L : Nat) (anchors : Array (Option Nat)) (source : Array Bool) (removed positions : List Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) (w : Word α) (fallback : α)
    (geometry : BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source removed st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w) :
    let out:=eraseMany env partition capacity old positions st tree
    out.work+out.store.sources.updateWork+st.sources.delivered*MaskedMutableProgression.Batch.rowBudget w.length≤
      st.sources.updateWork+positions.length*(11*h+25+Mutable.Store.bankLimit C E env.prepared.K w.length+
        (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)+
        MaskedMutableProgression.Batch.requestBudget w.length)+
      out.store.sources.delivered*MaskedMutableProgression.Batch.rowBudget w.length := by
  have hb:=eraseMany_work env partition capacity base old L anchors source removed positions st tree w fallback geometry hm hc he
  have hs:=MaskedMutableProgression.Batch.eraseMany_charged hm.1 positions
  rw [hm.2.1,←eraseMany_sources env partition capacity old positions st tree] at hs
  dsimp only
  rw [Nat.mul_add]
  omega

theorem eraseMany_fanout_balance (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (positions : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (source : Array Bool) (removed : List Nat) (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) :
    let out:=(eraseMany env partition capacity old positions st tree).store.sources
    out.delivered+out.sources.memberships=st.sources.delivered+st.sources.sources.memberships := by
  rw [eraseMany_sources]
  exact MaskedMutableProgression.Batch.eraseMany_balance hv positions

end Cells
end REWB.MaskedTraversalAggregate
