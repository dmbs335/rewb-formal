import REWB.MaskedTraversalRepairSnapshot
import REWB.MaskedTraversalAggregateEraseMany

/-! Actual current-source snapshots, including states returned by prior
reporting erasures, feed the complete-band repair and recover the full
Maintained model expected by the next report. No Batch.run ledger equality
is assumed. The input Pending invariant still belongs to the real Driver
transport induction, whose operation lemmas are separate.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h σ : Nat}

theorem snapshot_apply_maintained (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Snapshot text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (hp : Pending env partition capacity L anchors dirty st entries)
    (hg : tree.Good) (hr : Cells.Represents tree entries)
    (hw : env.window=⟨true,0,text.size+1⟩) (hu : Cells.Unclipped text.size entries) :
    Cells.Maintained env.shared partition capacity L text.size
      (apply env partition capacity L anchors dirty st tree).anchors source removed
      (apply env partition capacity L anchors dirty st tree).store
      (apply env partition capacity L anchors dirty st tree).tree := by
  have hpoint : ∀(first : Nat) (entry : Mutable.Store.Entry C E),
      (model env partition capacity L anchors dirty st tree entries)[first]?=some (some entry)→
      Cells.EntryState env.shared (apply env partition capacity L anchors dirty st tree).store partition capacity L first entry ∧
      Cells.Linked env.shared (apply env partition capacity L anchors dirty st tree).store partition capacity L first
        (apply env partition capacity L anchors dirty st tree).anchors entry.config := by
    intro first entry he
    have hb:=(List.getElem?_eq_some_iff.mp he).1
    rw [model_length] at hb
    rw [model_get env partition capacity L anchors dirty st tree entries first hb] at he
    by_cases hsel : first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions
    · simp only [if_pos hsel,Option.some.injEq] at he
      have hh:=snapshot_apply_selected text fallback source removed env partition capacity L base first st hs anchors dirty tree hp.raw hsel entry he
      exact ⟨hh.coherent,hh.linked⟩
    · simp only [if_neg hsel] at he
      have hn:=not_or.mp hsel
      have before:=hp.coherent first hn.1 entry he
      have hd:=describeLeader_sound partition capacity L first hs.invariant hs.capacity_eq entry.config.descriptor before.descriptor
      have hm : first∈partition.leaders.entries := by simpa only [hd.1] using hd.2.firstLeader
      exact ⟨entry_transfer env.shared st _ partition capacity L first entry before
          (apply_sources env partition capacity L anchors dirty st tree)
          (apply_other env partition capacity L first anchors dirty st tree hn.1 hn.2),
        linked_unmarked env partition capacity L first anchors dirty st tree entry.config hs.invariant hs.capacity_eq hm
          hn.1 hn.2 (hp.linked first hn.1 hn.2 entry he)⟩
  have hlen : entries.length=2^h := by
    have hh:=congrArg List.length hr
    simpa only [List.length_map,Tree.leaves_length] using hh.symm
  have hcomplete : Cells.CompleteModel partition (model env partition capacity L anchors dirty st tree entries) := by
    intro first hm
    have hb:=MaskedOrdered.Tree.within partition.leaders 0 hs.invariant.leadFits first hm
    have hbound : first<entries.length := by rw [hlen]; omega
    by_cases hsel : first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions
    · obtain ⟨entry,hentry⟩:=snapshot_apply_present text fallback source removed env partition capacity L base first st hs anchors dirty tree hp.raw hsel hm
      exact ⟨entry,by rw [model_get env partition capacity L anchors dirty st tree entries first hbound,if_pos hsel,hentry.slot]⟩
    · have hn:=not_or.mp hsel
      obtain ⟨entry,hentry⟩:=hp.complete first hm hn.1
      exact ⟨entry,by rw [model_get env partition capacity L anchors dirty st tree entries first hbound,if_neg hsel]; exact hentry⟩
  refine ⟨?_,?_,?_,apply_good env partition capacity L anchors dirty st tree hg,
    model env partition capacity L anchors dirty st tree entries,
    apply_represents env partition capacity L anchors dirty st tree entries hr,
    fun first entry he=>(hpoint first entry he).1,hcomplete,
    fun first entry he=>(hpoint first entry he).2,
    apply_unclipped env partition capacity L text.size anchors dirty st tree entries hs.invariant hs.capacity_eq hp hw hu⟩
  · rw [apply_sources]
    exact hs.valid
  · rw [apply_sources]
    exact hs.size
  · rw [apply_sources]
    exact hs.modulus

theorem snapshot_apply_anchors (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Snapshot text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (ha : MaskedTraversalRetained.Away partition capacity (ArrayText.read text fallback) text.size L anchors dirty.keys.positions)
    (hb : text.size<anchors.size) :
    MaskedTraversalRetained.Away partition capacity (ArrayText.read text fallback) text.size L
      (apply env partition capacity L anchors dirty st tree).anchors [] :=
  MaskedTraversalRetained.reset_all partition capacity text.size base L (ArrayText.read text fallback) anchors dirty.keys.positions
    hs.invariant hs.capacity_eq hs.complete hs.positive hb ha

end REWB.MaskedTraversalRepairCoherence
