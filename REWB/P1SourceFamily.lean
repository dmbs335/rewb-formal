import REWB.P1PhaseFamily
import REWB.SmallPeriodP2

/-! A source ending at one boundary has one record per phase, with all
    possible lengths encoded by its free exponent. Long equal sources
    belong to an enumerated cubic run of the target's least period. -/
namespace REWB.P1SourceFamily
open REWB.Periodic REWB.PhaseSolver REWB.AffineProjection REWB.RunGeometry
variable {α : Type}

def residue (q a phase : Nat) : Nat :=
  tailLen q (P1Source.start q a phase) (P2Periodic.endEndpoint q a)

def choices (q n : Nat) : List (Nat×Nat) :=
  (List.range (n+1)).flatMap fun a=>(List.range q).map fun phase=>(a,phase)

theorem choices_length (q n : Nat) : (choices q n).length=(n+1)*q := by
  have aux : ∀ xs : List Nat,
      (xs.flatMap (fun a=>(List.range q).map fun phase=>(a,phase))).length=xs.length*q := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_range,
        ih,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  unfold choices
  rw [aux,List.length_range]

theorem choices_mem (q n a phase : Nat) (ha : a≤n) (hp : phase<q) :
    (a,phase)∈choices q n :=
  List.mem_flatMap.mpr ⟨a,List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨phase,List.mem_range.mpr hp,rfl⟩⟩

theorem recover_number (q i a : Nat) (hq : 0<q) (hi : i≤a) :
    (P1Source.start q a (i%q)).number [(((a-i)/q : Nat) : Int)]=((i/q : Nat) : Int) := by
  have hc := P1PhaseFamily.copies_div q i a hq hi
  have hb := borrow_order q (coord q i) (coord q a) (coord_phase q a hq)
    (by simpa only [coord_pos] using hi)
  have hnum := P1Source.start_number q a (i%q) ((a-i)/q)
  have hcarry : carry (P1Source.start q a (i%q)) (P2Periodic.endEndpoint q a)=
      borrow (coord q i) (coord q a) := rfl
  rw [hcarry] at hnum
  simp only [Int.ofNat_eq_coe] at hnum
  unfold copies at hc
  change a/q-i/q-borrow (coord q i) (coord q a)=(a-i)/q at hc
  change i/q+borrow (coord q i) (coord q a)≤a/q at hb
  omega

/-- Recover an arbitrary source start from its end, phase and length
    quotient. No source length is enumerated. -/
theorem recover_coordinate (q i a : Nat) (hq : 0<q) (hi : i≤a) :
    (P1Source.start q a (i%q)).coordinate [(((a-i)/q : Nat) : Int)]=coord q i := by
  change ⟨((P1Source.start q a (i%q)).number [(((a-i)/q : Nat) : Int)]).toNat,i%q⟩=coord q i
  rw [recover_number q i a hq hi]
  rfl

theorem residue_correct (q i a : Nat) (hq : 0<q) (hi : i≤a) :
    residue q a (i%q)=(a-i)%q :=
  P2Periodic.residual_mod q i a hq hi

theorem local_complete (P : SevenDFA α) (s : Nat→α) (n q i a : Nat)
    (pre : Word α) (h : Period s n q) (hq : 0<q) (hi : i≤a) (ha : a≤n)
    (hA : P.A.accepts (pre++P2Periodic.factor s 0 i)) :
    decideFormula (UniformJoin.localSource P s n q a (i%q) (residue q a (i%q)) pre)
      [(((a-i)/q : Nat) : Int)]=true := by
  apply (UniformJoin.localSource_correct P s n q a (i%q) (residue q a (i%q))
    ((a-i)/q) pre h hq).mpr
  have hcoord := recover_coordinate q i a hq hi
  have hpos : (P1Source.start q a (i%q)).pos q [(((a-i)/q : Nat) : Int)]=i := by
    change ((P1Source.start q a (i%q)).coordinate [(((a-i)/q : Nat) : Int)]).pos q=i
    rw [hcoord,coord_pos]
  have hv : (P1Source.start q a (i%q)).valid q n [(((a-i)/q : Nat) : Int)] := by
    refine ⟨?_,Nat.mod_lt _ hq,by rw [hpos]; omega⟩
    rw [recover_number q i a hq hi]
    exact Int.ofNat_nonneg _
  refine ⟨hv,P1Target.fixed_valid q n a _ hq ha,?_,rfl,?_⟩
  · rw [hpos]
    exact hi
  · rwa [hpos]

def allSources : List Bounds→List (Bounds×(Nat×Nat))
  | [] => []
  | R::Rs => (choices R.period (R.hi-R.lo)).map (R,·)++allSources Rs

theorem allSources_mem (Rs : List Bounds) (R : Bounds) (a phase : Nat) :
    (R,(a,phase))∈allSources Rs ↔ R∈Rs ∧ (a,phase)∈choices R.period (R.hi-R.lo) := by
  induction Rs with
  | nil => simp [allSources]
  | cons S Ss ih =>
    rw [allSources,List.mem_append,ih]
    constructor
    · rintro (hm|⟨hR,hm⟩)
      · obtain ⟨z,hz,he⟩ := List.mem_map.mp hm
        obtain ⟨hS,hz'⟩ := Prod.mk.inj he
        subst S
        subst z
        exact ⟨by simp,hz⟩
      · exact ⟨by simp [hR],hm⟩
    · rintro ⟨hR,hm⟩
      rcases List.mem_cons.mp hR with he|hR
      · subst S
        exact Or.inl (List.mem_map.mpr ⟨(a,phase),hm,rfl⟩)
      · exact Or.inr ⟨hR,hm⟩

theorem allSources_bound (Q : Nat) (Rs : List Bounds)
    (h : ∀ R,R∈Rs→R.period≤Q ∧ 3*R.period≤R.hi-R.lo) :
    (allSources Rs).length≤3*Q*RunBudget.totalMass Rs := by
  induction Rs with
  | nil => simp [allSources,RunBudget.totalMass]
  | cons R Rs ih =>
    obtain ⟨hq,hc⟩ := h R (by simp)
    have hr := Nat.mul_le_mul (P1PhaseFamily.cubic_anchor_budget R hc) hq
    have hs := ih (fun S hS=>h S (by simp [hS]))
    simp only [allSources,List.length_append,List.length_map,choices_length,
      RunBudget.totalMass,Nat.mul_add]
    have he : (3*RunBudget.mass R)*Q=3*Q*RunBudget.mass R := by ac_rfl
    rw [he] at hr
    exact Nat.add_le_add hr hs

theorem concrete_source_bound [DecidableEq α] (f : Nat→α) (n Q : Nat) :
    (allSources (SmallPeriodRuns.cubic f n Q)).length≤
      3*Q*(2*n*DyadicIndex.heightFor n) := by
  have h := allSources_bound Q (SmallPeriodRuns.cubic f n Q)
    (fun R hR=>((SmallPeriodRuns.cubic_mem f n Q R).mp hR).2)
  have hm := RunBudget.totalMass_bound f n _ (SmallPeriodRuns.cubic_nodup f n Q)
    (fun R hR=>((SmallPeriodRuns.cubic_mem f n Q R).mp hR).1)
  exact Nat.le_trans h (Nat.mul_le_mul_left _ hm)

/-- The formula attached to a generated source record uses the original
    text prefix, the local end and its start phase. Its one free variable
    is the quotient of the source length by the run period. -/
def formula (P : SevenDFA α) (f : Nat→α) (R : Bounds) (a phase : Nat) : Formula :=
  UniformJoin.localSource P (shift f R.lo) (R.hi-R.lo) R.period a phase
    (residue R.period a phase) (segment f 0 R.lo)

theorem prefix_at (f : Nat→α) (a i : Nat) (hai : a≤i) :
    segment f 0 a++P2Periodic.factor (shift f a) 0 (i-a)=segment f 0 i := by
  unfold P2Periodic.factor
  rw [Nat.sub_zero,LongSourceCoverage.segment_shift,Nat.add_zero]
  have hh := segment_append f 0 a (i-a)
  simp only [Nat.zero_add] at hh
  rw [← hh,show a+(i-a)=i by omega]

theorem formula_complete (P : SevenDFA α) (f : Nat→α) (n : Nat)
    (R : Bounds) (hR : R.Valid f n) (i L : Nat)
    (hlo : R.lo≤i) (hhi : i+L≤R.hi) (hA : P.A.accepts (segment f 0 i)) :
    decideFormula (formula P f R (i+L-R.lo) ((i-R.lo)%R.period))
      [((L/R.period : Nat) : Int)]=true := by
  have hh := local_complete P (shift f R.lo) (R.hi-R.lo) R.period
    (i-R.lo) (i+L-R.lo) (segment f 0 R.lo)
    hR.2.2.2.1.2.1 hR.2.2.2.1.1 (by omega) (by omega)
    (by rwa [prefix_at f R.lo i hlo])
  rwa [show i+L-R.lo-(i-R.lo)=L by omega] at hh

theorem formula_residue (R : Bounds) (i L : Nat)
    (hq : 0<R.period) (hlo : R.lo≤i) :
    residue R.period (i+L-R.lo) ((i-R.lo)%R.period)=L%R.period := by
  rw [residue_correct R.period (i-R.lo) (i+L-R.lo) hq (by omega),
    show i+L-R.lo-(i-R.lo)=L by omega]

/-- Semantic source record. The executable cached compiler may reuse its
    boundary context instead of materializing this prefix for each event. -/
def data (f : Nat→α) (key : Nat) (R : Bounds) (a phase : Nat) : UniformJoin.SourceData α :=
  ⟨shift f R.lo,R.hi-R.lo,R.period,a,phase,residue R.period a phase,
    segment f 0 R.lo,R.lo+a,key⟩

theorem data_entry (P : SevenDFA α) (f : Nat→α) (key : Nat)
    (R : Bounds) (a phase : Nat) :
    UniformJoin.sourceEntry P (data f key R a phase)=
      ⟨R.lo+a,⟨key,formula P f R a phase⟩⟩ := rfl

/-- Keys are supplied by the shared exact-word registry. This function
    specifies the semantic records; cached event construction is separate. -/
def generated [DecidableEq α] (f : Nat→α) (n Q : Nat)
    (key : Bounds→Nat→Nat→Nat) : List (UniformJoin.SourceData α) :=
  (allSources (SmallPeriodRuns.cubic f n Q)).map fun z=>
    data f (key z.1 z.2.2 (residue z.1.period z.2.1 z.2.2)) z.1 z.2.1 z.2.2

theorem generated_mem [DecidableEq α] (f : Nat→α) (n Q : Nat)
    (key : Bounds→Nat→Nat→Nat) (R : Bounds) (a phase : Nat)
    (h : (R,(a,phase))∈allSources (SmallPeriodRuns.cubic f n Q)) :
    data f (key R phase (residue R.period a phase)) R a phase∈generated f n Q key :=
  List.mem_map.mpr ⟨(R,(a,phase)),h,rfl⟩

theorem generated_bound [DecidableEq α] (f : Nat→α) (n Q : Nat)
    (key : Bounds→Nat→Nat→Nat) :
    (generated f n Q key).length≤3*Q*(2*n*DyadicIndex.heightFor n) := by
  simpa only [generated,List.length_map] using concrete_source_bound f n Q

theorem generated_valid [DecidableEq α] (f : Nat→α) (n Q : Nat)
    (key : Bounds→Nat→Nat→Nat) (x : UniformJoin.SourceData α)
    (hx : x∈generated f n Q key) :
    Period x.text x.n x.q ∧ 0<x.q ∧ x.q≤Q ∧ x.position≤n := by
  obtain ⟨⟨R,a,phase⟩,hz,rfl⟩ := List.mem_map.mp hx
  obtain ⟨hR,hz⟩ := (allSources_mem _ R a phase).mp hz
  obtain ⟨hv,hq,_⟩ := (SmallPeriodRuns.cubic_mem f n Q R).mp hR
  obtain ⟨b,hb,hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨p,_,he⟩ := List.mem_map.mp hz
  have hab : b=a := (Prod.mk.inj he).1
  subst b
  have ha := List.mem_range.mp hb
  refine ⟨hv.2.2.2.1.2.1,hv.2.2.2.1.1,hq,?_⟩
  change R.lo+a≤n
  have hhi := hv.2.1
  have hlo := hv.1
  omega

/-- A source equal to a length-at-least-3q target factor is present in
    the generated schedule, with the same exact phase word. -/
theorem long_source_covered [DecidableEq α] (f : Nat→α) (n Q i j L : Nat)
    (T : Bounds) (hT : T.Valid f n) (hq : T.period≤Q)
    (hj : T.lo≤j) (hjt : j+L≤T.hi) (hL : 3*T.period≤L) (hi : i+L≤n)
    (he : segment f i L=segment f j L) :
    ∃ S : Bounds,S.Valid f n ∧ S.period=T.period ∧ S.lo≤i ∧ i+L≤S.hi ∧
      (S,(i+L-S.lo,(i-S.lo)%T.period))∈allSources (SmallPeriodRuns.cubic f n Q) ∧
      segment (shift f S.lo) ((i-S.lo)%T.period) T.period=
        segment (shift f T.lo) ((j-T.lo)%T.period) T.period := by
  obtain ⟨S,hS,hp,hlo,hhi,hkey⟩ := LongSourceCoverage.long_source f n i j L T hT hj hjt
    (by omega) hi he
  have hSq : S.period≤Q := by omega
  have hSc : 3*S.period≤S.hi-S.lo := by omega
  have hSmem := (SmallPeriodRuns.cubic_mem f n Q S).mpr ⟨hS,hSq,hSc⟩
  have hphase : (i-S.lo)%T.period<S.period := by
    rw [hp]
    exact Nat.mod_lt _ hT.2.2.2.1.1
  refine ⟨S,hS,hp,hlo,hhi,?_,hkey⟩
  apply (allSources_mem _ S _ _).mpr
  exact ⟨hSmem,choices_mem S.period (S.hi-S.lo) (i+L-S.lo)
    ((i-S.lo)%T.period) (by omega) hphase⟩

/-- Long-source completeness includes the accepted source formula, not
    just membership of a geometric record. No source length or target
    boundary is enumerated by the source schedule. -/
theorem long_source_complete [DecidableEq α] (P : SevenDFA α)
    (f : Nat→α) (n Q i j L : Nat) (T : Bounds) (hT : T.Valid f n)
    (hq : T.period≤Q) (hj : T.lo≤j) (hjt : j+L≤T.hi)
    (hL : 3*T.period≤L) (hi : i+L≤n)
    (he : segment f i L=segment f j L) (hA : P.A.accepts (segment f 0 i)) :
    ∃ S : Bounds,S.Valid f n ∧ S.period=T.period ∧ S.lo≤i ∧ i+L≤S.hi ∧
      (S,(i+L-S.lo,(i-S.lo)%T.period))∈allSources (SmallPeriodRuns.cubic f n Q) ∧
      residue T.period (i+L-S.lo) ((i-S.lo)%T.period)=L%T.period ∧
      decideFormula (formula P f S (i+L-S.lo) ((i-S.lo)%T.period))
        [((L/T.period : Nat) : Int)]=true ∧
      segment (shift f S.lo) ((i-S.lo)%T.period) T.period=
        segment (shift f T.lo) ((j-T.lo)%T.period) T.period := by
  obtain ⟨S,hS,hp,hlo,hhi,hmem,hkey⟩ :=
    long_source_covered f n Q i j L T hT hq hj hjt hL hi he
  have hr := formula_residue S i L hS.2.2.2.1.1 hlo
  have hf := formula_complete P f n S hS i L hlo hhi hA
  rw [hp] at hr hf
  exact ⟨S,hS,hp,hlo,hhi,hmem,hr,hf,hkey⟩

theorem long_source_data [DecidableEq α] (P : SevenDFA α)
    (f : Nat→α) (n Q i j L : Nat) (key : Bounds→Nat→Nat→Nat)
    (T : Bounds) (hT : T.Valid f n) (hq : T.period≤Q)
    (hj : T.lo≤j) (hjt : j+L≤T.hi) (hL : 3*T.period≤L) (hi : i+L≤n)
    (he : segment f i L=segment f j L) (hA : P.A.accepts (segment f 0 i)) :
    ∃ x : UniformJoin.SourceData α,x∈generated f n Q key ∧
      x.position=i+L ∧ x.q=T.period ∧ x.rho=L%T.period ∧
      decideFormula (UniformJoin.sourceEntry P x).entry.formula
        [((L/T.period : Nat) : Int)]=true ∧
      segment x.text x.phase x.q=
        segment (shift f T.lo) ((j-T.lo)%T.period) T.period := by
  obtain ⟨S,hS,hp,hlo,hhi,hmem,hr,hf,hword⟩ :=
    long_source_complete P f n Q i j L T hT hq hj hjt hL hi he hA
  let phase := (i-S.lo)%T.period
  let a := i+L-S.lo
  let x := data f (key S phase (residue S.period a phase)) S a phase
  refine ⟨x,generated_mem f n Q key S a phase hmem,?_,hp,?_,hf,?_⟩
  · change S.lo+(i+L-S.lo)=i+L
    omega
  · change residue S.period a phase=L%T.period
    rwa [hp]
  · change segment (shift f S.lo) phase S.period=_
    rwa [hp]

end REWB.P1SourceFamily
