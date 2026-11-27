import REWB.MaskedTraversalContextPhysical

/-! The scoped refresh-ready invariant concerns only the computed
successor keys, so unrelated active-frontier slots need no geometry for
this partition. Preparation and bank compilation use actual stored
metadata and current source indexes. The loop preserves this invariant,
including repeated keys, and accounts for every descriptor comparison,
neighbor read, compiler call and direct slot write.
-/
namespace REWB.MaskedTraversalContext
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalBankReady
variable {α : Type} {h : Nat}

def Ready (partition : MaskedClusterLeaders.State h) (capacity L n : Nat)
    (anchors : Array (Option Nat)) (ps : List Nat) (st : Mutable.Store.State C E) : Prop :=
  ∀first,first∈ps→∀entry,st.slots[first]?.join=some entry→
    Mutable.Store.Geometry (config partition capacity first L anchors entry.config) n

theorem prepare_work (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (old : Option (Mutable.Store.Entry C E)) :
    (prepare partition capacity first L anchors old).2≤85*h+117 := by
  have hd:=MaskedClusterDescriptor.describeLeader_work partition capacity first
  have hi:=incoming_work partition capacity first L anchors
  cases old with
  | none => simp [prepare]
  | some entry =>
    simp only [prepare]
    cases he : (MaskedClusterDescriptor.describeLeader partition capacity first).1 with
    | none => simp only [he]; omega
    | some d => simp only [he]; split <;> omega

theorem write_ready (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity p L n : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (ps : List Nat) (st : Mutable.Store.State C E)
    (hr : Ready partition capacity L n anchors ps st) :
    Ready partition capacity L n anchors ps (write C E book prepared ci ei partition capacity p L anchors target st) := by
  intro first hf entry he
  by_cases hp : p=first
  · subst p
    change ((st.slots.setIfInBounds first _)[first]?).join=some entry at he
    rw [Array.getElem?_setIfInBounds_self] at he
    split at he
    · simp only [Option.join] at he
      obtain ⟨old,hold,_,hcfg,_⟩:=compile_selected C E book prepared ci ei partition capacity first L anchors target st entry he
      rw [hcfg,config_idempotent]
      exact hr first hf old hold
    · cases he
  · rw [write_other C E book prepared ci ei partition capacity p first L anchors target st hp] at he
    exact hr first hf entry he

theorem compile_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (source : Array Bool) (removed : List Nat) (st : Mutable.Store.State C E)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool)
    (hr : Ready partition capacity L w.length anchors [first] st) :
    (compile C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      partition capacity first L anchors target st).2≤85*h+122+Mutable.Store.bankLimit C E prepared.K w.length := by
  have hp:=prepare_work partition capacity first L anchors (st.slots[first]?.join)
  simp only [compile]
  cases he : (prepare partition capacity first L anchors (st.slots[first]?.join)).1 with
  | none => simp only [he]; omega
  | some cfg =>
    obtain ⟨old,hold,_,hcfg⟩:=prepare_some partition capacity first L anchors (st.slots[first]?.join) cfg he
    have hg : Mutable.Store.Geometry cfg w.length := by
      rw [hcfg]
      exact hr first List.mem_cons_self old hold
    have hw:=Mutable.Store.compile_work C E book prepared w source removed st.sources hv hn target cfg hg
    simp only [he]
    omega

theorem applyLoop_sources (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (ps : List Nat) (st : Mutable.Store.State C E) :
    (applyLoop C E book prepared ci ei partition capacity L anchors target ps st).sources=st.sources := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih => rw [applyLoop,ih]; rfl

theorem applyLoop_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (source : Array Bool) (removed : List Nat) (st : Mutable.Store.State C E)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (ps : List Nat)
    (hr : Ready partition capacity L w.length anchors ps st) :
    (applyLoop C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      partition capacity L anchors target ps st).repairWork≤
      st.repairWork+(85*h+130+Mutable.Store.bankLimit C E prepared.K w.length)*ps.length+1 := by
  induction ps generalizing st with
  | nil => simp [applyLoop]
  | cons p ps ih =>
    let next:=write C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      partition capacity p L anchors target st
    have hready:=write_ready C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      partition capacity p L w.length anchors target (p::ps) st hr
    have ht:=ih {next with repairWork:=next.repairWork+3} hv hn (by
      intro first hf entry he
      exact hready first (List.mem_cons_of_mem p hf) entry he)
    have hw:=compile_work C E book prepared w source removed st hv hn partition capacity p L anchors target (by
      intro first hf entry he
      have hh : first=p := by simpa only [List.mem_singleton] using hf
      subst first
      exact hr p List.mem_cons_self entry he)
    have hnext : next.repairWork=st.repairWork+
        (compile C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
          partition capacity p L anchors target st).2+5 := rfl
    rw [applyLoop]
    change _≤st.repairWork+(85*h+130+Mutable.Store.bankLimit C E prepared.K w.length)*(ps.length+1)+1
    rw [Nat.mul_succ]
    dsimp only [next] at ht hnext ⊢
    omega

end REWB.MaskedTraversalContext
