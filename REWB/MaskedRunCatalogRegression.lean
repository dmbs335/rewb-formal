import REWB.MaskedRunCatalogDiscovery

/-! Kernel regressions for exact array IDs, truncated-key rejection,
short target masks, persistent targets after source erasure, and actual
dense-descriptor discovery covering the whole current component. -/
namespace REWB.MaskedRunCatalog.Regression
open REWB.RunGeometry REWB.Periodic REWB.MaskedRunDiscovery

private def R : Bounds := ⟨0,6,1⟩
private def S : Bounds := ⟨1,5,1⟩
private def target : Array Bool := #[true,false,true]
private def raw := build 6 target 2 #[R,S]

private theorem width_six : width 6=3 := by simp [width,Nat.log2]

theorem exact_ids : (lookupId raw R).1=some 0 ∧ (lookupId raw S).1=some 1 := by
  unfold raw build
  rw [width_six]
  decide

theorem short_mask_counts :
    ((raw.entries[0]?).map Entry.counts)=some #[1,0,2,0,2,0,2] := by decide

theorem huge_step_counts :
    (((build 6 target 100 #[R]).entries[0]?).map Entry.counts)=some #[1,0,1,0,0,0,0] := by decide

/-- The low-width bits alone would collide; the physical bound guard
rejects the out-of-text triple before constructing or traversing a key. -/
theorem truncated_alias_rejected :
    RunDedup.key (width 6) ⟨8,6,1⟩=RunDedup.key (width 6) R ∧
      (lookupId raw ⟨8,6,1⟩).1=none := by
  unfold raw build
  rw [width_six]
  decide

theorem source_erase_keeps_target (st : MaskedMutableProgression.Batch.State) (ps : List Nat) :
    ofBatch target (MaskedMutableProgression.Batch.eraseMany ps st)=ofBatch target st :=
  ofBatch_eraseMany target ps st

private def text : Array (Fin 2) := Array.replicate 6 0
private def current := MaskedClusterLeaders.execute 3 2
  [.insert 4,.insert 1,.insert 0,.insert 3,.insert 2]
private def dense : MaskedClusterDescriptor.Descriptor := ⟨0,4,1,4,none,some 3,none⟩

private theorem read_zero : ArrayText.read text 0=(fun _=>0) := by
  funext i
  simp only [text,ArrayText.read,Array.getElem?_replicate]
  split <;> rfl

private theorem complete : Complete (ArrayText.read text 0) text.size 0 2 current.state.occurrences.entries := by
  have he : current.state.occurrences.entries=[0,1,2,3,4] := by decide
  rw [he]
  intro k
  change k∈[0,1,2,3,4] ↔ k+2≤6 ∧ segment (ArrayText.read text 0) k 2=segment (ArrayText.read text 0) 0 2
  rw [read_zero]
  simp only [segment,Nat.add_zero,List.cons.injEq,and_self,true_and]
  simp only [List.mem_cons,List.not_mem_nil,or_false,and_true]
  omega

/-- A retained actual leader state yields a run catalog ID through two
shared rank queries. Its entire four-step component ends exactly at 6. -/
theorem actual_dense_catalog :
    ∃id,(descriptorShared (ofBatch target (MaskedMutableProgression.Batch.prepare text 0 #[] 2))
      (MaskedSuffixClass.prepare text 0) dense 2).1=some ⟨id,entry target 2 R⟩ := by
  have hi:=(MaskedClusterLeaders.execute_valid 3 2
    [.insert 4,.insert 1,.insert 0,.insert 3,.insert 2]).invariant
  change MaskedClusterLeaders.Invariant current.length current.state at hi
  have hl : current.length=2 := by decide
  rw [hl] at hi
  have hd : (MaskedClusterDescriptor.describeLeader current.state 8 0).1=some dense := by decide
  obtain ⟨run,id,he,_,hv,hq,hlo,hhi⟩:=descriptor_complete text 0 #[] target 2 current.state 8 2 0 0
    hi (by decide) dense hd complete (by decide) (by decide)
  have hr : run=R := by
    have hn:=hv.2.1
    change run.period=1 at hq
    change run.lo≤0 at hlo
    change 4+2≤run.hi at hhi
    change run.hi≤6 at hn
    cases run
    simp only [R,Bounds.mk.injEq]
    simp only at hq hlo hhi hn
    omega
  exact ⟨id,hr ▸ he⟩

end REWB.MaskedRunCatalog.Regression
