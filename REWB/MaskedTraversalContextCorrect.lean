import REWB.MaskedTraversalContext

/-! Exact propagation of an anchor reset: among actual current leaders,
only the actual successor of a reset leader can observe a changed incoming
cursor. The sparse executable successor pass contains all such leaders.
This closes anchor-reset propagation without any cascading anchor reset.
Occurrence/leader structural locality remains a distinct obligation.
-/
namespace REWB.MaskedTraversalContext
open REWB.MaskedOrdered REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalBankReady
variable {α : Type} {h : Nat}

def Target (leaders : Tree h) (capacity p x : Nat) : Prop :=
  p∈leaders.entries ∧ (Tree.succ leaders capacity p).1=some x

theorem step_spec (leaders : Tree h) (capacity p : Nat) (out : MaskedTraversalDirty.Marked h)
    (hg : leaders.Good) (hf : leaders.Fits 0) (hc : capacity=2^h) (hv : out.keys.Valid) :
    (step leaders capacity p out).keys.Valid ∧
    (∀x,x∈(step leaders capacity p out).keys.tree.entries ↔ Target leaders capacity p x ∨ x∈out.keys.tree.entries) ∧
    (step leaders capacity p out).requests≤out.requests+1 ∧
    (step leaders capacity p out).keys.positions.length≤out.keys.positions.length+1 ∧
    (step leaders capacity p out).work≤out.work+39*h+34 := by
  have hmw:=Tree.contains_work leaders capacity p
  have hnw:=Tree.succ_work leaders capacity p
  by_cases hm : (Tree.contains leaders capacity p).1=true
  · have hp:=(Tree.contains_correct leaders capacity p hf hc).mp hm
    cases hn : (Tree.succ leaders capacity p).1 with
    | none =>
      simp only [step,hm,if_true,hn]
      refine ⟨hv,?_,by omega,by omega,by omega⟩
      intro x
      simp [Target,hn]
    | some q =>
      have hs:=Tree.succ_correct leaders capacity p hg hf hc
      rw [hn] at hs
      have hq:=Tree.within leaders 0 hf q hs.1
      have hb : q<2^h := by omega
      have ha:=MaskedOrdered.add_valid out.keys capacity q hv hc hb
      have hh:=MaskedTraversalDirty.markList_card capacity [q] out
      have hw:=MaskedOrdered.insert_work out.keys.tree capacity q
      simp only [step,hm,if_true,hn]
      refine ⟨ha,?_,?_,?_,?_⟩
      · intro x
        change x∈(MaskedOrdered.add out.keys capacity q).1.tree.entries ↔ _
        rw [MaskedOrdered.add_mem out.keys capacity q x hv hc hb]
        simp only [Target,hp,hn,true_and,Option.some.injEq]
        simp only [eq_comm]
      · exact Nat.le_refl _
      · exact hh
      · change out.work+(MaskedOrdered.add out.keys capacity q).2.work+4+
          (Tree.contains leaders capacity p).2+(Tree.succ leaders capacity p).2+7≤_
        change (MaskedOrdered.add out.keys capacity q).2.work≤28*h+18 at hw
        omega
  · have hp : p∉leaders.entries := by
      intro hp
      exact hm ((Tree.contains_correct leaders capacity p hf hc).mpr hp)
    simp only [step,hm,Bool.false_eq_true,if_false]
    refine ⟨hv,?_,by omega,by omega,by omega⟩
    intro x
    simp [Target,hp]

theorem successors_spec (leaders : Tree h) (capacity : Nat) (ps : List Nat)
    (out : MaskedTraversalDirty.Marked h) (hg : leaders.Good) (hf : leaders.Fits 0)
    (hc : capacity=2^h) (hv : out.keys.Valid) :
    (successors leaders capacity ps out).keys.Valid ∧
    (∀x,x∈(successors leaders capacity ps out).keys.tree.entries ↔
      (∃p,p∈ps ∧ Target leaders capacity p x) ∨ x∈out.keys.tree.entries) ∧
    (successors leaders capacity ps out).requests≤out.requests+ps.length ∧
    (successors leaders capacity ps out).keys.positions.length≤out.keys.positions.length+ps.length ∧
    (successors leaders capacity ps out).work≤out.work+(39*h+34)*ps.length+1 := by
  induction ps generalizing out with
  | nil =>
    refine ⟨hv,?_,?_,?_,?_⟩
    · intro x; simp [successors]
    · simp [successors]
    · simp [successors]
    · simp [successors]
  | cons p ps ih =>
    have hs:=step_spec leaders capacity p out hg hf hc hv
    have ht:=ih (step leaders capacity p out) hs.1
    rw [successors]
    refine ⟨ht.1,?_,?_,?_,?_⟩
    · intro x
      rw [ht.2.1,hs.2.1]
      simp only [List.mem_cons,exists_eq_or_imp,or_assoc,or_left_comm]
    · have hh:=ht.2.2.1
      have hp:=hs.2.2.1
      change _≤out.requests+(ps.length+1)
      omega
    · have hh:=ht.2.2.2.1
      have hp:=hs.2.2.2.1
      change _≤out.keys.positions.length+(ps.length+1)
      omega
    · have hh:=ht.2.2.2.2
      have hp:=hs.2.2.2.2
      change _≤out.work+(39*h+34)*(ps.length+1)+1
      rw [Nat.mul_succ]
      omega

theorem pred_next (leaders : Tree h) (capacity first p : Nat)
    (hg : leaders.Good) (hf : leaders.Fits 0) (hc : capacity=2^h)
    (hm : first∈leaders.entries) (hp : (Tree.pred leaders capacity first).1=some p) :
    (Tree.succ leaders capacity p).1=some first := by
  have hs:=Tree.pred_correct leaders capacity first hg hf hc
  rw [hp] at hs
  apply succ_unique leaders.entries p _ (some first) (Tree.succ_correct leaders capacity p hg hf hc)
  refine ⟨hm,hs.2.1,?_⟩
  intro x hx hpx
  by_cases hfirst : first≤x
  · exact hfirst
  · have hh:=hs.2.2 x hx (by omega)
    omega

theorem incoming_unchanged (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (ps : List Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hf : first∈partition.leaders.entries)
    (hn : first∉(successors partition.leaders capacity ps (MaskedTraversalDirty.empty h)).keys.tree.entries) :
    incoming partition capacity first L (MaskedTraversalRepair.anchorsLoop L ps anchors 0).1=
      incoming partition capacity first L anchors := by
  have hs:=successors_spec partition.leaders capacity ps (MaskedTraversalDirty.empty h)
    hi.leadGood hi.leadFits hc (MaskedOrdered.State.empty_valid h)
  cases hp : (Tree.pred partition.leaders capacity first).1 with
  | none => simp only [incoming,hp]
  | some p =>
    have hpred:=Tree.pred_correct partition.leaders capacity first hi.leadGood hi.leadFits hc
    rw [hp] at hpred
    have hnot : p∉ps := by
      intro hm
      apply hn
      apply (hs.2.1 first).mpr
      exact Or.inl ⟨p,hm,hpred.1,pred_next partition.leaders capacity first p hi.leadGood hi.leadFits hc hf hp⟩
    simp only [incoming,hp]
    cases hd : (MaskedClusterDescriptor.describeLeader partition capacity p).1 with
    | none => simp only [hd]
    | some d => simp only [hd,MaskedTraversalRepair.anchorsLoop_read,if_neg hnot]

theorem prepare_known (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (entry : Mutable.Store.Entry C E)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some entry.config.descriptor) :
    (prepare partition capacity first L anchors (some entry)).1=
      some (config partition capacity first L anchors entry.config) := by
  simp only [prepare,hd,if_pos rfl,if_true]

theorem prepare_some (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (old : Option (Mutable.Store.Entry C E)) (cfg : Mutable.Store.Config)
    (he : (prepare partition capacity first L anchors old).1=some cfg) :
    ∃entry,old=some entry ∧
      (MaskedClusterDescriptor.describeLeader partition capacity first).1=some entry.config.descriptor ∧
      cfg=config partition capacity first L anchors entry.config := by
  cases old with
  | none => cases he
  | some entry =>
    cases hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1 with
    | none => simp only [prepare,hd,reduceCtorEq] at he
    | some d =>
      by_cases heq : d=entry.config.descriptor
      · simp only [prepare,hd,if_pos heq,Option.some.injEq] at he
        exact ⟨entry,rfl,by simpa only [heq] using hd,he.symm⟩
      · simp only [prepare,hd,if_neg heq,reduceCtorEq] at he

theorem config_retains (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (old : Mutable.Store.Config) :
    (config partition capacity first L anchors old).descriptor=old.descriptor ∧
    (config partition capacity first L anchors old).runId=old.runId ∧
    (config partition capacity first L anchors old).targetCounts=old.targetCounts ∧
    (config partition capacity first L anchors old).window=old.window ∧
    (config partition capacity first L anchors old).anchor=readAnchor anchors first L :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem config_idempotent (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (old : Mutable.Store.Config) :
    config partition capacity first L anchors (config partition capacity first L anchors old)=
      config partition capacity first L anchors old := rfl

theorem compile_selected (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (st : Mutable.Store.State C E)
    (entry : Mutable.Store.Entry C E)
    (he : (compile C E book prepared ci ei partition capacity first L anchors target st).1=some entry) :
    ∃old,st.slots[first]?.join=some old ∧
      (MaskedClusterDescriptor.describeLeader partition capacity first).1=some old.config.descriptor ∧
      entry.config=config partition capacity first L anchors old.config ∧
      (Mutable.Store.compile C E book prepared ci ei st.sources target entry.config).1=some entry.bank := by
  cases hp : (prepare partition capacity first L anchors (st.slots[first]?.join)).1 with
  | none => simp only [compile,hp,reduceCtorEq] at he
  | some cfg =>
    obtain ⟨old,hold,hdesc,hcfg⟩:=prepare_some partition capacity first L anchors (st.slots[first]?.join) cfg hp
    simp only [compile,hp] at he
    cases hb : (Mutable.Store.compile C E book prepared ci ei st.sources target cfg).1 with
    | none =>
      simp only [hb] at he
      change none=some entry at he
      cases he
    | some bank =>
      simp only [hb] at he
      have heq : (⟨cfg,bank⟩ : Mutable.Store.Entry C E)=entry := Option.some.inj he
      subst entry
      exact ⟨old,hold,hdesc,hcfg,hb⟩

theorem write_other (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first other L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (st : Mutable.Store.State C E) (hne : first≠other) :
    (write C E book prepared ci ei partition capacity first L anchors target st).slots[other]?=st.slots[other]? :=
  Array.getElem?_setIfInBounds_ne hne

theorem write_selected (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (st : Mutable.Store.State C E) (hb : first<st.slots.size) :
    (write C E book prepared ci ei partition capacity first L anchors target st).slots[first]?=
      some (compile C E book prepared ci ei partition capacity first L anchors target st).1 :=
  Array.getElem?_setIfInBounds_self_of_lt hb

end REWB.MaskedTraversalContext
