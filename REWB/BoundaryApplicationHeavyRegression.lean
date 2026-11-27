import REWB.BoundaryApplicationHeavyQuery

/-! Kernel equality of the constructor-pattern implementation and the
original whole-pattern-alias specification. The alias specification is
deliberately noncomputable: a Lean 4.19.0 generated-code discrepancy was
observed when executing that form. No compiler pass or general upstream
cause is asserted here. The executable empty-input audit separately
tests the production definition. -/
namespace REWB.BoundaryApplication.Heavy.Regression
open REWB.BoundaryIndex
variable {σ : Nat}

noncomputable def aliased (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) {h : Nat} (base : BoundaryIndex.Tree (Subset.count A) E.stateCount h) :
    TrieFor w→Versions.Snapshot D.stateCount E.stateCount h→
      Merge.State (Subset.count A) E.stateCount h→ResultAt A D E w.length h
  | t@(.empty),s,incoming =>
    let rr:=RTable.node A B D w rows t
    let normal:=Versions.root s
    let out:=Lift.importMany rr.map normal.state.tree normal.state.positions incoming
    let entry : EntryAt A D E h:=⟨normal,out.1,rr.map,t.depth,
      rows.length-(representative w t).start⟩
    ⟨.leaf entry none,1,normal.state.cachedSize,out.2+rr.work A D+8⟩
  | t@(.leaf key),s,incoming =>
    let rr:=RTable.node A B D w rows t
    let normal:=Versions.root s
    let out:=Lift.importMany rr.map normal.state.tree normal.state.positions incoming
    let entry : EntryAt A D E h:=⟨normal,out.1,rr.map,t.depth,
      rows.length-(representative w t).start⟩
    ⟨.leaf entry (some key.record),1,normal.state.cachedSize,out.2+rr.work A D+8⟩
  | t@(.node _ depth l r),s,incoming =>
    let rr:=RTable.node A B D w rows t
    let normal:=Versions.root s
    let chooseRight:=heavyRight s
    let light:=lightState s
    let out:=Lift.importMany rr.map normal.state.tree light.positions incoming
    let entry : EntryAt A D E h:=⟨normal,out.1,rr.map,depth,
      rows.length-(representative w t).start⟩
    let next:=advance A E w ranges depth (if chooseRight then r else l) out.1
    let a:=aliased A B D E w rows ranges base l (left s) (if chooseRight then blank base else next.1)
    let b:=aliased A B D E w rows ranges base r (right s) (if chooseRight then next.1 else blank base)
    ⟨.node entry chooseRight a.saved b.saved,a.allocated+b.allocated+1,
      a.imports+b.imports+light.cachedSize,a.work+b.work+out.2+rr.work A D+next.2+14⟩

theorem aliased_eq_go (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) {h : Nat} (base : BoundaryIndex.Tree (Subset.count A) E.stateCount h)
    (t : TrieFor w) (s : Versions.Snapshot D.stateCount E.stateCount h)
    (incoming : Merge.State (Subset.count A) E.stateCount h) :
    aliased A B D E w rows ranges base t s incoming=go A B D E w rows ranges base t s incoming := by
  induction t generalizing s incoming with
  | empty => rfl
  | leaf _ => rfl
  | node key depth l r ihl ihr => simp only [aliased,go,ihl,ihr]; rfl

/-- Rank-zero jumps stop and positive ranks have an existing predecessor;
these are the exact properties needed by the executable fuel choice. -/
theorem empty_input_sources (A B D E : DFA (Fin σ)) (fallback : Fin σ) :
    ∃i,(HeavyIndex.build A B D E [] fallback 0 (Nat.le_refl 0)).addresses.sources.get 0=some i :=
  HeavyIndex.build_source A B D E [] fallback 0 (Nat.le_refl 0) 0 (Nat.le_refl 0)

/-- Two silent sources outweigh one target although their target list
is empty. The path builder follows total mass, matching the normal merge. -/
theorem silent_mass_retained {k m h : Nat} (base : BoundaryIndex.Tree k m h)
    (pos : Merge.Position h) (color : Fin k) (state : Fin m) :
    heavyRight (Versions.execute base (.node (Counted.identity k) (Counted.identity k)
      (.node (Counted.identity k) (Counted.identity k) (.source pos) (.source pos)) (.target pos color state)))=false ∧
    decide ((Mixed.execute base (.node (Counted.identity k) (Counted.identity k) (.source pos) (.source pos))).state.cachedSize≤
      (Mixed.execute base (.target pos color state)).state.cachedSize)=true := by
  rw [heavyRight_execute]
  simp only [Mixed.execute_mass,Mixed.shape,MaskedEventBudget.size,
    Mixed.execute_size,Mixed.targetPositions,List.length_append,List.length_nil,List.length_cons]
  decide

end REWB.BoundaryApplication.Heavy.Regression
