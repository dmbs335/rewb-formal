import REWB.ResidualDispatchLists

/-! An actual bounded list of separated equality windows. One retained
sampled run list feeds both run-derived selectors. The later P1/P2
language queries are predicates over this list, not an assumed oracle. -/
namespace REWB.ResidualDispatch
open REWB.RunGeometry REWB.IndexedGrid REWB.GlobalCoverage
variable {σ : Nat}

structure Selection where
  windows : List Strip := []
  count : Nat := 0
  work : Nat := 1
  deriving Repr

def select : List Row→Selection
  | [] => {}
  | row::rows =>
      let candidate:=ResidualRunWindows.candidate row.1 row.2.1 row.2.2
      let tail:=select rows
      match candidate.1 with
      | none => ⟨tail.windows,tail.count,candidate.2+tail.work+5⟩
      | some c => ⟨c::tail.windows,tail.count+1,candidate.2+tail.work+5⟩

def selectTail (acc : List Strip) (count work : Nat) : List Row→Selection
  | [] => ⟨acc.reverse,count,work+1⟩
  | row::rows =>
      let candidate:=ResidualRunWindows.candidate row.1 row.2.1 row.2.2
      match candidate.1 with
      | none => selectTail acc count (work+candidate.2+5) rows
      | some c => selectTail (c::acc) (count+1) (work+candidate.2+5) rows

theorem selectTail_spec (acc : List Strip) (count work : Nat) (rows : List Row) :
    selectTail acc count work rows=
      ⟨acc.reverse++(select rows).windows,count+(select rows).count,work+(select rows).work⟩ := by
  induction rows generalizing acc count work with
  | nil => simp [selectTail,select]
  | cons row rows ih =>
    simp only [selectTail,select]
    cases hc:(ResidualRunWindows.candidate row.1 row.2.1 row.2.2).1 <;>
      simp only [ih,List.reverse_cons,List.append_assoc,List.singleton_append]
    · congr 1 <;> omega
    · congr 1 <;> omega

def selectTR (rows : List Row) : Selection := selectTail [] 0 0 rows

@[csimp] theorem select_eq_selectTR : select=selectTR := by
  funext rows
  simp only [selectTR,selectTail_spec,List.reverse_nil,List.nil_append,Nat.zero_add]

theorem select_mem (rows : List Row) (c : Strip) :
    c∈(select rows).windows ↔ ∃row,row∈rows ∧
      (ResidualRunWindows.candidate row.1 row.2.1 row.2.2).1=some c := by
  induction rows with
  | nil => simp [select]
  | cons row rows ih =>
    simp only [select]
    cases hc:(ResidualRunWindows.candidate row.1 row.2.1 row.2.2).1 with
    | none =>
      rw [ih]
      constructor
      · rintro ⟨x,hx,he⟩; exact ⟨x,List.mem_cons_of_mem row hx,he⟩
      · rintro ⟨x,hx,h⟩
        rcases List.mem_cons.mp hx with he|hx
        · subst x; rw [hc] at h; cases h
        · exact ⟨x,hx,h⟩
    | some v =>
      rw [List.mem_cons,ih]
      constructor
      · rintro (he|⟨x,hx,h⟩)
        · subst c; exact ⟨row,List.mem_cons_self,hc⟩
        · exact ⟨x,List.mem_cons_of_mem row hx,h⟩
      · rintro ⟨x,hx,h⟩
        rcases List.mem_cons.mp hx with he|hx
        · subst x; exact Or.inl ((Option.some.inj (hc.symm.trans h)).symm)
        · exact Or.inr ⟨x,hx,h⟩

theorem select_counts (rows : List Row) :
    (select rows).count=(select rows).windows.length ∧
    (select rows).count≤rows.length ∧ (select rows).work≤16*rows.length+1 := by
  induction rows with
  | nil => exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩
  | cons row rows ih =>
    have hh:=ResidualRunWindows.candidate_work row.1 row.2.1 row.2.2
    simp only [select,List.length_cons,Nat.mul_succ]
    cases hc:(ResidualRunWindows.candidate row.1 row.2.1 row.2.2).1 <;>
      simp only [List.length_cons] <;> omega

def stripWindow (W : ResidualStripSchedule.Job) : Strip := ⟨W.left,W.right,W.distance⟩

structure Plan where
  strips : ResidualStripSchedule.Prepared
  generated : RankIndexSchedule.Result
  windows : List Strip
  selectors : Nat
  selectorWork : Nat
  work : Nat

def runWork (runs : RankIndexSchedule.Result) : Nat :=
  runs.preparation+runs.divisorWork+runs.queryWork+runs.periodWork+runs.dedupWork+6*runs.probes

def compile (D Q : Nat) (strips : ResidualStripSchedule.Prepared) (runs : RankIndexSchedule.Result) : Plan :=
  let low:=lowRows D runs.runs
  let large:=largeRows Q runs.runs
  let lowWindows:=select low.1
  let largeWindows:=select large.1
  let stripWindows:=CountedProjection.map (fun W=>(stripWindow W,3)) strips.batch.jobs
  let tail:=CountedProjection.append lowWindows.windows largeWindows.windows
  let all:=CountedProjection.append stripWindows.1 tail.1
  let work:=low.2+large.2+lowWindows.work+largeWindows.work+stripWindows.2+tail.2+all.2+8
  ⟨strips,runs,all.1,strips.batch.queries+lowWindows.count+largeWindows.count,work,
    strips.work+runWork runs+work+5⟩

def prepare (f : Nat→Fin σ) (n s L D Q : Nat) : Plan :=
  let strips:=ResidualStripSchedule.prepare f n s L D
  let runs:=RankIndexSchedule.generate f n s
  compile D Q strips runs

theorem compile_windows (D Q : Nat) (strips : ResidualStripSchedule.Prepared) (runs : RankIndexSchedule.Result) :
    (compile D Q strips runs).windows=strips.batch.jobs.map stripWindow++
      ((select (lowRows D runs.runs).1).windows++(select (largeRows Q runs.runs).1).windows) := by
  simp only [compile,CountedProjection.append_value,CountedProjection.map_value]

theorem compile_count (D Q : Nat) (strips : ResidualStripSchedule.Prepared) (runs : RankIndexSchedule.Result)
    (hs : strips.batch.queries=strips.batch.jobs.length) :
    (compile D Q strips runs).selectors=(compile D Q strips runs).windows.length := by
  rw [compile_windows,List.length_append,List.length_append,List.length_map]
  simp only [compile,hs,(select_counts _).1]
  omega

theorem prepare_count (f : Nat→Fin σ) (n s L D Q : Nat) :
    (prepare f n s L D Q).selectors=(prepare f n s L D Q).windows.length :=
  compile_count D Q _ _ (ResidualStripSchedule.prepare_query_length f n s L D)

theorem compile_mem (D Q : Nat) (strips : ResidualStripSchedule.Prepared) (runs : RankIndexSchedule.Result) (c : Strip) :
    c∈(compile D Q strips runs).windows ↔
      (∃W,W∈strips.batch.jobs ∧ stripWindow W=c) ∨
      (∃R p,(R,p)∈lowSchedule D runs.runs ∧ (ResidualRunWindows.candidate R p R.period).1=some c) ∨
      (∃R p d,(R,(p,d))∈largeSchedule
        (runs.runs.filter (fun R=>decide (Q<R.period ∧ 3*R.period≤R.hi-R.lo))) ∧
        (ResidualRunWindows.candidate R p d).1=some c) := by
  rw [compile_windows,List.mem_append,List.mem_append,List.mem_map,select_mem,select_mem,
    lowRows_value,largeRows_value]
  constructor
  · rintro (h|h|h)
    · exact Or.inl h
    · obtain ⟨row,hrow,hc⟩:=h
      obtain ⟨⟨R,p⟩,hm,he⟩:=List.mem_map.mp hrow
      subst row
      exact Or.inr (Or.inl ⟨R,p,hm,hc⟩)
    · obtain ⟨⟨R,p,d⟩,hm,hc⟩:=h
      exact Or.inr (Or.inr ⟨R,p,d,hm,hc⟩)
  · rintro (h|h|h)
    · exact Or.inl h
    · obtain ⟨R,p,hm,hc⟩:=h
      exact Or.inr (Or.inl ⟨lowRow (R,p),List.mem_map.mpr ⟨(R,p),hm,rfl⟩,hc⟩)
    · obtain ⟨R,p,d,hm,hc⟩:=h
      exact Or.inr (Or.inr ⟨(R,(p,d)),hm,hc⟩)

theorem prepare_mem (f : Nat→Fin σ) (n s L D Q : Nat) (c : Strip) :
    c∈(prepare f n s L D Q).windows ↔
      (∃W,W∈(ResidualStripSchedule.prepare f n s L D).batch.jobs ∧ stripWindow W=c) ∨
      (∃R p,(R,p)∈RankIndexSchedule.low f n s D ∧ (ResidualRunWindows.candidate R p R.period).1=some c) ∨
      (∃R p d,(R,(p,d))∈RankIndexSchedule.large f n s Q ∧ (ResidualRunWindows.candidate R p d).1=some c) :=
  compile_mem D Q _ _ c

theorem compile_selector_work (D Q : Nat) (strips : ResidualStripSchedule.Prepared) (runs : RankIndexSchedule.Result) :
    (compile D Q strips runs).selectorWork≤5*strips.batch.jobs.length+
      31*(lowSchedule D runs.runs).length+34*(largeRows Q runs.runs).1.length+12*runs.runs.length+15 := by
  have hl:=lowRows_work D runs.runs
  have hg:=largeRows_work Q runs.runs
  have hls:=select_counts (lowRows D runs.runs).1
  have hgs:=select_counts (largeRows Q runs.runs).1
  have hlen : (lowRows D runs.runs).1.length=(lowSchedule D runs.runs).length := by
    rw [lowRows_value,List.length_map]
  simp only [compile,CountedProjection.map_plain_steps,CountedProjection.append_steps,
    CountedProjection.map_value,List.length_map]
  rw [←hls.1]
  rw [hlen] at hls
  omega

end REWB.ResidualDispatch
