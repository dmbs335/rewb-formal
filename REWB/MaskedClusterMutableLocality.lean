import REWB.MaskedClusterMutableBatchCorrect

/-! Candidate/source-window locality for every finite replay-bank entry.
    Erasing a position outside the actual candidate set or source window
    preserves the entire materialized bank, including artificial replay
    maps and both source components. The candidate set matters: a point
    between AP starts can lie in the hull without being an occurrence.
    The target array/counts stay fixed. Counters may change with a source
    tree snapshot, so these statements concern stored matrix values.
-/
namespace REWB.MaskedCluster.Mutable
open REWB.MaskedPeriodic REWB.MaskedFiniteAction
variable {α : Type}

structure SameOn (positions : Nat→Prop) (window : SourceWindow) (a b : Index) : Prop where
  left : a.Valid
  right : b.Valid
  base : a.base=b.base
  len : a.len=b.len
  step : a.step=b.step
  live : ∀p,positions p→window.allows p=true→(a.Live p ↔ b.Live p)

theorem SameOn.gate {positions : Nat→Prop} {window : SourceWindow} {a b : Index}
    (h : SameOn positions window a b) (enabled : Bool) : SameOn positions (window.gate enabled) a b := by
  refine ⟨h.left,h.right,h.base,h.len,h.step,?_⟩
  intro p hpos hp
  cases enabled with
  | false => rw [SourceWindow.gate_false] at hp; cases hp
  | true => rw [SourceWindow.gate_true] at hp; exact h.live p hpos hp

theorem SameOn.erase {positions : Nat→Prop} {window : SourceWindow} {idx : Index} (hv : idx.Valid)
    (p : Nat) (hp : positions p→window.allows p=false) :
    SameOn positions window idx (MaskedMutableProgression.erase idx p).index := by
  refine ⟨hv,MaskedMutableProgression.erase_valid idx hv p,
    (MaskedMutableProgression.erase_base idx p).symm,(MaskedMutableProgression.erase_len idx p).symm,
    (MaskedMutableProgression.erase_step idx p).symm,?_⟩
  intro x hpos hx
  have hn : x≠p := by intro he; subst x; rw [hp hpos] at hx; cases hx
  rw [MaskedMutableProgression.erase_live idx hv p x]
  exact ⟨fun h=>⟨hn,h⟩,fun h=>h.2⟩

theorem SameOn.history {positions : Nat→Prop} {window : SourceWindow} {source : Array Bool} {removed : List Nat}
    {base len step : Nat} {a b : Index}
    (ha : MaskedMutableProgression.Batch.IndexSpec source removed base len step a)
    (hb : MaskedMutableProgression.Batch.IndexSpec source (p::removed) base len step b)
    (hp : positions p→window.allows p=false) : SameOn positions window a b := by
  refine ⟨ha.good,hb.good,ha.base_eq.trans hb.base_eq.symm,ha.len_eq.trans hb.len_eq.symm,
    ha.step_eq.trans hb.step_eq.symm,?_⟩
  intro x hpos hx
  have hn : x≠p := by intro he; subst x; rw [hp hpos] at hx; cases hx
  rw [ha.live x,hb.live x,ha.base_eq,hb.base_eq,ha.len_eq,hb.len_eq]
  simp only [MaskedMutableProgression.Batch.Current,List.mem_cons,not_or,hn,not_false_eq_true,true_and]

theorem gated_member_same {positions : Nat→Prop} {window : SourceWindow} {a b : Index}
    (h : SameOn positions window a b) (p : Nat) (hp : positions p) :
    (window.allows p && (MaskedMutableProgression.member a p).1)=
      (window.allows p && (MaskedMutableProgression.member b p).1) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true,Bool.and_eq_true,MaskedMutableProgression.member_correct a h.left p,
    MaskedMutableProgression.member_correct b h.right p]
  exact ⟨fun hx=>⟨hx.1,(h.live p hp hx.1).mp hx.2⟩,fun hx=>⟨hx.1,(h.live p hp hx.1).mpr hx.2⟩⟩

theorem sourcePairQuery_same {positions : Nat→Prop} {m n : Nat} (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (a b : Index) (q s S : Nat) (window : SourceWindow) (h : SameOn positions window a b)
    (hq : 0<q) (hm : m≤S) (hn : n≤S) (hstep : a.step=common S*q)
    (hc : ∀k,lo≤k→k≤hi→positions (s+k*q)) :
    (sourcePairQuery before after lo hi a q s (common S) window).answer=
      (sourcePairQuery before after lo hi b q s (common S) window).answer := by
  apply Bool.eq_iff_iff.mpr
  have hstep' : b.step=common S*q := h.step.symm.trans hstep
  rw [sourcePairQuery_correct before after lo hi a h.left q s S window hq hm hn hstep,
    sourcePairQuery_correct before after lo hi b h.right q s S window hq hm hn hstep']
  constructor
  · rintro ⟨k,hk,hb,he,hl,hw⟩
    refine ⟨k,hk,?_,?_,(h.live _ (hc k hk.1 hk.2.1) hw).mp hl,hw⟩
    · rwa [←h.base]
    · rwa [←h.base,←h.len]
  · rintro ⟨k,hk,hb,he,hl,hw⟩
    refine ⟨k,hk,?_,?_,(h.live _ (hc k hk.1 hk.2.1) hw).mpr hl,hw⟩
    · rwa [h.base]
    · rwa [h.base,h.len]

theorem cell_same {positions : Nat→Prop} (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat) (a b : Index)
    (targetCounts : Array Nat) (q s : Nat) (window : SourceWindow) (h : SameOn positions window a b)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hq : 0<q) (hstep : a.step=prepared.K*q) (hc : ∀k,lo≤k→k≤hi→positions (s+k*q)) :
    (cell C E prepared maps tail lo hi a targetCounts q s window input output).answer=
      (cell C E prepared maps tail lo hi b targetCounts q s window input output).answer := by
  cases input with
  | waiting =>
    cases output with
    | gap output =>
      simp only [cell,prepared.exact,modulus]
      apply sourcePairQuery_same _ _ _ _ a b q s (max C.stateCount E.stateCount) window h hq
        (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      · simpa only [prepared.exact,modulus] using hstep
      · exact hc
    | waiting => simp only [cell,h.base]
    | suffix _ => simp only [cell,h.base]
  | gap _ => cases output <;> simp only [cell,h.base]
  | suffix _ => cases output <;> simp only [cell,h.base]

theorem pointCell_same {positions : Nat→Prop} (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (a b : Index) (target : Array Bool) (p : Nat) (window : SourceWindow) (h : SameOn positions window a b) (hp : positions p)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (pointCell C E maps tail a target p window input output).answer=
      (pointCell C E maps tail b target p window input output).answer := by
  simp only [pointCell,gated_member_same h p hp]

theorem rowCell_same {positions : Nat→Prop} (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (a b : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (h : SameOn positions window a b)
    (outMode : Bool) (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hctx : ∀row,ctx=some row→0<row.step ∧ a.step=prepared.K*row.step ∧ positions row.last ∧
      ∀k,row.lo≤k→k≤row.hi→positions (row.start+k*row.step)) :
    (rowCell C E prepared ctx tail a target targetCounts window outMode input output).answer=
      (rowCell C E prepared ctx tail b target targetCounts window outMode input output).answer := by
  cases ctx with
  | none => rfl
  | some ctx =>
    have hh:=hctx ctx rfl
    cases outMode with
    | true =>
      cases ho : ctx.over with
      | none => simp only [rowCell,if_true,ho]
      | some maps =>
        simp only [rowCell,if_true,ho]
        exact pointCell_same C E maps tail a b target ctx.last window h hh.2.2.1 input output
    | false =>
      cases hn : ctx.normal with
      | none => simp only [rowCell,Bool.false_eq_true,if_false,hn]
      | some maps =>
        simp only [rowCell,Bool.false_eq_true,if_false,hn,either]
        rw [cell_same C E prepared maps tail ctx.lo ctx.hi a b targetCounts ctx.step ctx.start window h input output
          hh.1 hh.2.1 hh.2.2.2]

theorem pointRowCell_same {positions : Nat→Prop} (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (a b : Index) (target : Array Bool) (window : SourceWindow) (h : SameOn positions window a b)
    (outMode : Bool) (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hctx : ∀row,ctx=some row→positions row.last) :
    (pointRowCell C E ctx tail a target window outMode input output).answer=
      (pointRowCell C E ctx tail b target window outMode input output).answer := by
  cases ctx with
  | none => rfl
  | some ctx =>
    have hp:=hctx ctx rfl
    cases outMode with
    | true =>
      cases ho : ctx.over <;> simp only [pointRowCell,if_true,ho,pointCell_same C E _ tail a b target ctx.last window h hp]
    | false =>
      cases hn : ctx.normal <;> simp only [pointRowCell,Bool.false_eq_true,if_false,hn,either,
        pointCell_same C E _ tail a b target ctx.last window h hp]

theorem blocks_same {positions : Nat→Prop} (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (a b : Index) (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (h : SameOn positions window a b)
    (input output : Bool) (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (ha : ∀row,rows.1=some row→0<row.step ∧ a.step=prepared.K*row.step ∧ positions row.last ∧
      ∀k,row.lo≤k→k≤row.hi→positions (row.start+k*row.step))
    (hb : ∀row,rows.2=some row→0<row.step ∧ a.step=prepared.K*row.step ∧ positions row.last ∧
      ∀k,row.lo≤k→k≤row.hi→positions (row.start+k*row.step)) :
    ((((blocks C E prepared rows tail a target targetCounts window).get input output).cells.get i).get j)=
      ((((blocks C E prepared rows tail b target targetCounts window).get input output).cells.get i).get j) := by
  cases input <;>
    simp only [blocks,CursorBlocks.get,Bool.false_eq_true,if_false,if_true,rowMatrix_get] <;>
    apply rowCell_same <;> assumption

theorem pointBlocks_same {positions : Nat→Prop} (C E : DFA α) (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (a b : Index) (target : Array Bool) (window : SourceWindow) (h : SameOn positions window a b)
    (input output : Bool) (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (ha : ∀row,rows.1=some row→positions row.last) (hb : ∀row,rows.2=some row→positions row.last) :
    ((((pointBlocks C E rows tail a target window).get input output).cells.get i).get j)=
      ((((pointBlocks C E rows tail b target window).get input output).cells.get i).get j) := by
  cases input <;>
    simp only [pointBlocks,CursorBlocks.get,Bool.false_eq_true,if_false,if_true,pointRowMatrix_get] <;>
    apply pointRowCell_same <;> assumption

theorem denseBank_same {positions : Nat→Prop} (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail : Replay C E) (a b : Index) (target : Array Bool) (targetCounts : Array Nat)
    (window : SourceWindow) (h : SameOn positions window a b)
    (ha : ∀row,rows.1=some row→0<row.step ∧ a.step=prepared.K*row.step ∧ positions row.last ∧
      ∀k,row.lo≤k→k≤row.hi→positions (row.start+k*row.step))
    (hb : ∀row,rows.2=some row→0<row.step ∧ a.step=prepared.K*row.step ∧ positions row.last ∧
      ∀k,row.lo≤k→k≤row.hi→positions (row.start+k*row.step)) :
    (denseBank C E book prepared rows tail a target targetCounts window).1=
      (denseBank C E book prepared rows tail b target targetCounts window).1 := by
  apply table_eq
  funext key i j
  simp only [denseBank,tabulate_view]
  rw [←code_decode i,←code_decode j,flatten_get,flatten_get]
  exact blocks_same C E prepared rows _ a b target targetCounts _ (h.gate _) _ _ _ _ ha hb

theorem pointBank_same {positions : Nat→Prop} (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (a b : Index) (target : Array Bool) (window : SourceWindow) (h : SameOn positions window a b)
    (ha : ∀row,rows.1=some row→positions row.last) (hb : ∀row,rows.2=some row→positions row.last) :
    (pointBank C E book rows tail a target window).1=(pointBank C E book rows tail b target window).1 := by
  apply table_eq
  funext key i j
  simp only [pointBank,tabulate_view]
  rw [←code_decode i,←code_decode j,flatten_get,flatten_get]
  exact pointBlocks_same C E rows _ a b target _ (h.gate _) _ _ _ _ ha hb

theorem prepareRow_candidates (C E : DFA α) (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m H next incoming : Nat) (enabled mode : Bool) (row : RowContext C E)
    (h : (prepareRow C E ci ei s q m H next incoming enabled mode).1=some row) :
    row.start=s ∧ row.step=q ∧ row.last=s+m*q ∧ row.hi≤m := by
  unfold prepareRow at h
  split at h
  · have he:=Option.some.inj h
    rw [←he]
    exact ⟨rfl,rfl,rfl,normalHi_le s q m H next⟩
  · cases h

theorem preparePointRow_last (C E : DFA α) (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s H next incoming : Nat) (enabled mode : Bool) (row : RowContext C E)
    (h : (preparePointRow C E ci ei s H next incoming enabled mode).1=some row) : row.last=s := by
  unfold preparePointRow at h
  split at h
  · exact congrArg RowContext.last (Option.some.inj h).symm
  · cases h

theorem compileDenseBank_same {positions : Nat→Prop} (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m L H next incoming : Nat) (enabled : Bool) (a b : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (h : SameOn positions window a b)
    (hq : 0<q) (hstep : a.step=prepared.K*q) (hp : ∀k,k≤m→positions (s+k*q)) :
    (compileDenseBank C E book prepared ci ei s q m L H next incoming enabled a target targetCounts window).1=
      (compileDenseBank C E book prepared ci ei s q m L H next incoming enabled b target targetCounts window).1 := by
  apply denseBank_same C E book prepared _ _ a b target targetCounts window h
  · intro row hr
    have he:=prepareRow_candidates C E ci ei s q m H next incoming enabled false row hr
    refine ⟨by rw [he.2.1]; exact hq,by rw [he.2.1]; exact hstep,?_,?_⟩
    · rw [he.2.2.1]; exact hp m (Nat.le_refl _)
    · intro k _ hk
      rw [he.1,he.2.1]
      exact hp k (Nat.le_trans hk he.2.2.2)
  · intro row hr
    have he:=prepareRow_candidates C E ci ei s q m H next incoming enabled true row hr
    refine ⟨by rw [he.2.1]; exact hq,by rw [he.2.1]; exact hstep,?_,?_⟩
    · rw [he.2.2.1]; exact hp m (Nat.le_refl _)
    · intro k _ hk
      rw [he.1,he.2.1]
      exact hp k (Nat.le_trans hk he.2.2.2)

theorem compilePointBank_same {positions : Nat→Prop} (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s L H next incoming : Nat) (enabled : Bool) (a b : Index)
    (target : Array Bool) (window : SourceWindow) (h : SameOn positions window a b) (hp : positions s) :
    (compilePointBank C E book ci ei s L H next incoming enabled a target window).1=
      (compilePointBank C E book ci ei s L H next incoming enabled b target window).1 := by
  apply pointBank_same C E book _ _ a b target window h
  · intro row hr
    rw [preparePointRow_last C E ci ei s H next incoming enabled false row hr]
    exact hp
  · intro row hr
    rw [preparePointRow_last C E ci ei s H next incoming enabled true row hr]
    exact hp

end REWB.MaskedCluster.Mutable
