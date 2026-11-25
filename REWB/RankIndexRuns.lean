import REWB.IndexedGrid
import REWB.RankIndexPeriod

/-! Sampled all-period run construction from concrete LCE/LCS indexes.
For every grid anchor, positive displacements are visited once. The
precomputed divisor buckets bound all minimum-period tests by their
aggregate O(n log n) cell count per anchor. The output may contain
duplicate maximal runs; deterministic deduplication is a separate step. -/
namespace REWB.RankIndexRuns
open REWB.Periodic REWB.RunGeometry REWB.LCEIndex REWB.RankIndex
open REWB.RankIndexDivisors (bucket buckets cells)
variable {σ : Nat}

theorem candidate_distance (F B : Index) (n i j : Nat) (S : IndexedGrid.Strip)
    (h : (IndexedGrid.candidate F B n (i,j)).1=some S) : S.distance=j-i := by
  unfold IndexedGrid.candidate at h
  split at h
  · dsimp only at h
    split at h
    · cases h
      rfl
    · contradiction
  · contradiction

structure One where
  run : Option Bounds
  queryWork : Nat
  periodWork : Nat

def one (F B : Index) (bs : Array (List Nat)) (n i d : Nat) : One :=
  let c:=IndexedGrid.candidate F B n (i,i+d)
  match c.1 with
  | none => ⟨none,c.2,0⟩
  | some S =>
    if S.distance≤S.hi-S.lo then
      let r:=RankIndexPeriod.fromStrip F bs n S.lo S.hi S.distance
      ⟨some r.1,c.2,r.2⟩
    else ⟨none,c.2,0⟩

theorem one_queryWork (f : Nat→Fin σ) (bs : Array (List Nat)) (n i d : Nat) :
    (one (prepare f n) (prepareReverse f n) bs n i d).queryWork≤26*(n.log2+1)+2 := by
  have hh:=IndexedGrid.candidate_work f n (i,i+d)
  unfold one
  dsimp only
  split
  · exact hh
  · split <;> exact hh

theorem one_periodWork (F B : Index) (bs : Array (List Nat)) (n i d : Nat) :
    (one F B bs n i d).periodWork≤(bucket bs d).length*(13*(n.log2+1)+6) := by
  unfold one
  dsimp only
  split
  · simp
  next S he =>
    split
    next ho =>
      have hd : S.distance=d := by
        have hh:=candidate_distance F B n i (i+d) S he
        omega
      have hh:=RankIndexPeriod.fromStrip_work F bs n S.lo S.hi S.distance
      simpa only [hd] using hh
    next hn => simp

theorem one_sound (f : Nat→Fin σ) (n i d : Nat) (R : Bounds)
    (h : (one (prepare f n) (prepareReverse f n) (buckets n).1 n i d).run=some R) :
    R.Valid f n := by
  unfold one at h
  dsimp only at h
  split at h
  · contradiction
  next S hc =>
    split at h
    next ho =>
      cases h
      exact (RankIndexPeriod.fromStrip_spec f n S.lo S.hi S.distance
        (IndexedGrid.candidate_sound f n (i,i+d) S hc) ho).1
    next hn => contradiction

/-- A probe at the true period recovers the exact maximal run. The
minimum-period selector is executed from the precomputed divisor list. -/
theorem one_complete (f : Nat→Fin σ) (n i : Nat) (R : Bounds) (hR : R.Valid f n)
    (hlo : R.lo≤i) (hhi : i+R.period<R.hi) :
    (one (prepare f n) (prepareReverse f n) (buckets n).1 n i R.period).run=some R := by
  have hp:=hR.2.2.2.1.1
  have hlen:=hR.2.2.1
  have hbound:=hR.2.1
  have hlr:=hR.1
  let S : IndexedGrid.Strip:=⟨R.lo,R.hi-R.period,R.period⟩
  have hc : (IndexedGrid.candidate (prepare f n) (prepareReverse f n)
      n (i,i+R.period)).1=some S := by
    unfold IndexedGrid.candidate
    rw [if_pos (by omega : i<i+R.period ∧ i+R.period≤n)]
    dsimp only
    rw [IndexedGrid.extend_eq f n i (i+R.period) (by omega) (by omega)]
    dsimp only
    rw [show i+R.period-i=R.period by omega]
    obtain ⟨hl,hr⟩ := GridCoverage.extend_run_exact f n R hR i hlo hhi
    have hr' : GridCoverage.regionEnd f n R.period i=R.hi-R.period := by omega
    rw [hl,hr',if_pos (by omega)]
  have ho : S.distance≤S.hi-S.lo := by dsimp [S]; omega
  unfold one
  dsimp only
  simp only [hc,if_pos ho]
  apply congrArg some
  have hmem : R.period∈bucket (buckets n).1 R.period :=
    (RankIndexDivisors.buckets_mem n R.period R.period).mpr
      ⟨hp,by omega,hp,Nat.dvd_refl _⟩
  have hper := RankIndexPeriod.minimum_period f n R.lo R.hi R.period R.period
    (bucket (buckets n).1 R.period) (by omega) hbound hR.2.2.2.1
    (by omega) (Nat.le_refl _) hmem
  change (RankIndexPeriod.fromStrip (prepare f n) (buckets n).1
    n R.lo (R.hi-R.period) R.period).1=R
  unfold RankIndexPeriod.fromStrip
  rw [show R.hi-R.period+R.period=R.hi by omega]
  dsimp only
  rw [hper]

structure Batch where
  runs : List Bounds := []
  queryWork : Nat := 0
  periodWork : Nat := 0
  probes : Nat := 0
  deriving Repr

def inner (F B : Index) (bs : Array (List Nat)) (n i : Nat) : List Nat→Batch
  | [] => {}
  | d::ds =>
    let r:=one F B bs n i d
    let acc:=inner F B bs n i ds
    ⟨match r.run with | none=>acc.runs | some R=>R::acc.runs,
      r.queryWork+acc.queryWork,r.periodWork+acc.periodWork,acc.probes+1⟩

def innerTR (F B : Index) (bs : Array (List Nat)) (n i : Nat) (ds : List Nat) : Batch :=
  ds.foldr (fun d acc=>
    let r:=one F B bs n i d
    ⟨match r.run with | none=>acc.runs | some R=>R::acc.runs,
      r.queryWork+acc.queryWork,r.periodWork+acc.periodWork,acc.probes+1⟩) {}

@[csimp] theorem inner_eq_innerTR : @inner=@innerTR := by
  funext F B bs n i ds
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [inner,innerTR,List.foldr_cons] at ih ⊢
    rw [ih]

theorem inner_mem (F B : Index) (bs : Array (List Nat)) (n i : Nat)
    (ds : List Nat) (R : Bounds) :
    R∈(inner F B bs n i ds).runs ↔ ∃ d∈ds,(one F B bs n i d).run=some R := by
  induction ds with
  | nil => simp [inner]
  | cons d ds ih =>
    simp only [inner]
    cases he : (one F B bs n i d).run with
    | none => simp only [he,ih]; simp [he]
    | some S =>
      simp only [he,List.mem_cons]
      change (R=S ∨ R∈(inner F B bs n i ds).runs) ↔ _
      rw [ih]
      constructor
      · rintro (h|⟨e,he',hr⟩)
        · subst R
          exact ⟨d,by simp,he⟩
        · exact ⟨e,by simp [he'],hr⟩
      · rintro ⟨e,he',hr⟩
        rcases he' with hh|hm
        · subst e
          rw [he] at hr
          exact Or.inl (Option.some.inj hr).symm
        · exact Or.inr ⟨e,hm,hr⟩

def weight (bs : Array (List Nat)) (ds : List Nat) : Nat :=
  (ds.map (fun d=>(bucket bs d).length)).sum

theorem inner_counts (f : Nat→Fin σ) (bs : Array (List Nat)) (n i : Nat) (ds : List Nat) :
    (inner (prepare f n) (prepareReverse f n) bs n i ds).probes=ds.length ∧
      (inner (prepare f n) (prepareReverse f n) bs n i ds).runs.length≤ds.length ∧
      (inner (prepare f n) (prepareReverse f n) bs n i ds).queryWork≤
        (26*(n.log2+1)+2)*ds.length ∧
      (inner (prepare f n) (prepareReverse f n) bs n i ds).periodWork≤
        weight bs ds*(13*(n.log2+1)+6) := by
  induction ds with
  | nil => simp [inner,weight]
  | cons d ds ih =>
    have hq:=one_queryWork f bs n i d
    have hp:=one_periodWork (prepare f n) (prepareReverse f n) bs n i d
    refine ⟨?_,?_,?_,?_⟩
    · change (inner _ _ _ _ _ ds).probes+1=ds.length+1
      omega
    · simp only [inner]
      cases he : (one (prepare f n) (prepareReverse f n) bs n i d).run <;>
        simp only [he,List.length_cons] <;> exact (by omega)
    · change (one _ _ _ _ _ d).queryWork+(inner _ _ _ _ _ ds).queryWork≤_
      rw [List.length_cons,Nat.mul_succ]
      omega
    · change (one _ _ _ _ _ d).periodWork+(inner _ _ _ _ _ ds).periodWork≤_
      simp only [weight,List.map_cons,List.sum_cons,Nat.add_mul]
      change _≤(bucket bs d).length*(13*(n.log2+1)+6)+weight bs ds*(13*(n.log2+1)+6)
      exact Nat.add_le_add hp ih.2.2.2

theorem weight_range (bs : Array (List Nat)) : weight bs (List.range bs.size)=cells bs := by
  have he : (List.range bs.size).map (bucket bs)=bs.toList := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i<bs.size
    · simp only [List.getElem?_map,List.getElem?_range,hi,if_true,Option.map,Array.getElem?_toList]
      rw [Array.getElem?_eq_getElem hi]
      simp only [bucket,Array.getElem?_eq_getElem hi,Option.getD_some]
    · simp only [List.getElem?_map,List.getElem?_range,hi,if_false,Option.map]
      rw [List.getElem?_eq_none (by rw [List.length_range]; omega)]
      change (none : Option (List Nat))=bs.toList[i]?
      rw [List.getElem?_eq_none (by rw [Array.length_toList]; omega)]
  have hc : ∀ xs : List (List Nat),(xs.map List.length).sum=RankIndexDivisors.cellsList xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons,List.sum_cons,RankIndexDivisors.cellsList,ih]
  have hh:=congrArg (fun xs : List (List Nat)=>(xs.map List.length).sum) he
  simp only [List.map_map] at hh
  exact hh.trans (hc bs.toList)

def outer (F B : Index) (bs : Array (List Nat)) (n s : Nat) (anchors : List Nat) : Batch :=
  anchors.foldr (fun a acc=>
    let r:=inner F B bs n (a*s) (List.range (n+1))
    ⟨r.runs++acc.runs,r.queryWork+acc.queryWork,r.periodWork+acc.periodWork,r.probes+acc.probes⟩) {}

theorem outer_mem (F B : Index) (bs : Array (List Nat)) (n s : Nat)
    (anchors : List Nat) (R : Bounds) :
    R∈(outer F B bs n s anchors).runs ↔
      ∃ a∈anchors,∃ d,d≤n ∧ (one F B bs n (a*s) d).run=some R := by
  induction anchors with
  | nil => simp [outer]
  | cons a as ih =>
    change R∈(inner F B bs n (a*s) (List.range (n+1))).runs++
      (outer F B bs n s as).runs ↔ _
    rw [List.mem_append,inner_mem,ih]
    constructor
    · rintro (⟨d,hd,hr⟩|⟨b,hb,d,hd,hr⟩)
      · exact ⟨a,by simp,d,by have hh:=List.mem_range.mp hd; omega,hr⟩
      · exact ⟨b,by simp [hb],d,hd,hr⟩
    · rintro ⟨b,hb,d,hd,hr⟩
      rcases List.mem_cons.mp hb with he|hm
      · subst b
        exact Or.inl ⟨d,List.mem_range.mpr (by omega),hr⟩
      · exact Or.inr ⟨b,hm,d,hd,hr⟩

theorem outer_counts (f : Nat→Fin σ) (bs : Array (List Nat)) (n s : Nat)
    (anchors : List Nat) (hb : bs.size=n+1) :
    (outer (prepare f n) (prepareReverse f n) bs n s anchors).probes=anchors.length*(n+1) ∧
      (outer (prepare f n) (prepareReverse f n) bs n s anchors).runs.length≤anchors.length*(n+1) ∧
      (outer (prepare f n) (prepareReverse f n) bs n s anchors).queryWork≤
        anchors.length*((26*(n.log2+1)+2)*(n+1)) ∧
      (outer (prepare f n) (prepareReverse f n) bs n s anchors).periodWork≤
        anchors.length*(cells bs*(13*(n.log2+1)+6)) := by
  induction anchors with
  | nil => simp [outer]
  | cons a as ih =>
    have hr:=inner_counts f bs n (a*s) (List.range (n+1))
    rw [List.length_range,← hb,weight_range] at hr
    rw [hb] at hr
    refine ⟨?_,?_,?_,?_⟩
    · change (inner _ _ _ _ _ _).probes+(outer _ _ _ _ _ as).probes=_
      rw [hr.1,ih.1,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm]
    · change ((inner _ _ _ _ _ _).runs++(outer _ _ _ _ _ as).runs).length≤_
      rw [List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · change (inner _ _ _ _ _ _).queryWork+(outer _ _ _ _ _ as).queryWork≤_
      rw [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · change (inner _ _ _ _ _ _).periodWork+(outer _ _ _ _ _ as).periodWork≤_
      rw [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

structure Result extends Batch where
  preparation : Nat
  divisorWork : Nat
  deriving Repr

def generate (f : Nat→Fin σ) (n s : Nat) : Result :=
  let F:=prepare f n
  let B:=prepareReverse f n
  let ds:=buckets n
  ⟨outer F B ds.1 n s (List.range (n/s+1)),F.countedWork+B.countedWork,ds.2⟩

theorem generate_sound (f : Nat→Fin σ) (n s : Nat) (R : Bounds)
    (h : R∈(generate f n s).runs) : R.Valid f n := by
  obtain ⟨a,ha,d,hd,hr⟩ := (outer_mem _ _ _ _ _ _ R).mp h
  exact one_sound f n (a*s) d R hr

/-- Every valid maximal run with at least s equality positions appears
in the actual generated list, including exponent-exactly-two runs. -/
theorem generate_complete (f : Nat→Fin σ) (n s : Nat) (R : Bounds)
    (hR : R.Valid f n) (hs : 0<s) (hspan : s≤R.hi-R.lo-R.period) :
    R∈(generate f n s).runs := by
  have hp:=hR.2.2.2.1.1
  have hlen:=hR.2.2.1
  have hn:=hR.2.1
  have hlr:=hR.1
  have hP:=run_on f n R.lo R.hi R.period hR
  have hreg : GridCoverage.EqualityRegion f n R.lo (R.hi-R.lo-R.period) R.period := by
    refine ⟨hp,by omega,?_⟩
    intro j hj hj'
    exact hP j hj (by omega)
  obtain ⟨i,hi,hlo,hhi,_⟩ := GridCoverage.equality_grid f n s R.lo
    (R.hi-R.lo-R.period) R.period hs hspan hreg
  unfold GridCoverage.probes at hi
  obtain ⟨a,ha,hij⟩ := List.mem_flatMap.mp hi
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hij
  have hai : a*s=i := congrArg Prod.fst he
  apply (outer_mem _ _ _ _ _ _ R).mpr
  refine ⟨a,ha,R.period,by omega,?_⟩
  rw [hai]
  exact one_complete f n i R hR hlo (by omega)

/-- A long outer-copy witness whose maximal strips overlap obtains a
generated run containing both complete copies, at the true minimum
period dividing their displacement. -/
theorem copy_overlap_complete (f : Nat→Fin σ) (n s p e k : Nat)
    (hc : GlobalCoverage.Copy f n p e k) (hs : 0<s) (hspan : s≤e-p)
    (ho : k-p≤(GlobalCoverage.expand f n p k).2-(GlobalCoverage.expand f n p k).1) :
    ∃ R,R∈(generate f n s).runs ∧ R.lo≤p ∧ e+(k-p)≤R.hi ∧ R.period∣k-p := by
  obtain ⟨hl,hr,hstrip⟩ := GlobalCoverage.expand_spec f n p e k hc
  obtain ⟨R,hR,hlo,hhi,hdiv,hq⟩ := GlobalCoverage.overlapping_run f n _ _ _ hstrip ho
  have heq : s≤R.hi-R.lo-R.period := by
    rw [hlo,hhi]
    omega
  exact ⟨R,generate_complete f n s R hR hs heq,
    by rwa [hlo],by rw [hhi]; omega,hdiv⟩

theorem generate_counts (f : Nat→Fin σ) (n s : Nat) :
    (generate f n s).probes=(n/s+1)*(n+1) ∧
      (generate f n s).runs.length≤(n/s+1)*(n+1) ∧
      (generate f n s).queryWork≤(n/s+1)*((26*(n.log2+1)+2)*(n+1)) ∧
      (generate f n s).periodWork≤
        (n/s+1)*((n*(n.log2+1))*(13*(n.log2+1)+6)) ∧
      (generate f n s).preparation≤
        2*((n+1)*((n.log2+1)*(16*width σ n+4)+1)) ∧
      (generate f n s).divisorWork≤3*(n*(n.log2+1)) := by
  have hh:=outer_counts f (buckets n).1 n s (List.range (n/s+1))
    (RankIndexDivisors.buckets_size n)
  rw [List.length_range,RankIndexDivisors.buckets_cells] at hh
  have hcells:=RankIndexDivisors.pairs_length n
  have hp:=prepare_work f n
  have hb:=prepareReverse_work f n
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_,?_,RankIndexDivisors.buckets_work n⟩
  · exact Nat.le_trans hh.2.2.2 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcells))
  · change (prepare f n).countedWork+(prepareReverse f n).countedWork≤_
    omega

end REWB.RankIndexRuns
