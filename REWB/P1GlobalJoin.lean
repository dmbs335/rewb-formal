import REWB.P1SourceFamily

/-! Global P1 joins between two generated periodic intervals. The source
    and target formulas share an exponent, residue and exact period word;
    the chronological join checks the original C gap. These statements
    are semantic glue and do not perform any text scans. -/
namespace REWB.P1GlobalJoin
open REWB.Periodic REWB.RunGeometry REWB.AffineProjection
variable {α : Type}

theorem prefix_local (f : Nat→α) (lo a : Nat) :
    segment f 0 lo++segment (shift f lo) 0 a=segment f 0 (lo+a) := by
  rw [LongSourceCoverage.segment_shift,Nat.add_zero]
  simpa only [Nat.zero_add] using (segment_append f 0 lo a).symm

theorem slice_segment (f : Nat→α) (n a b : Nat) (hab : a≤b) (hbn : b≤n) :
    Spec.slice (segment f 0 n) a b=segment f a (b-a) := by
  unfold Spec.slice
  rw [SmallPeriodP2.segment_drop f 0 n a (by omega),Nat.zero_add,
    SmallPeriodP2.segment_take f a (n-a) (b-a) (by omega)]

theorem prefix_gap (f : Nat→α) (n a b : Nat) (hab : a≤b) (hbn : b≤n) :
    segment f 0 a++Spec.slice (segment f 0 n) a b=segment f 0 b := by
  rw [slice_segment f n a b hab hbn]
  have hh := segment_append f 0 a (b-a)
  simp only [Nat.zero_add] at hh
  rw [← hh,show a+(b-a)=b by omega]

def targetData (f : Nat→α) (n key : Nat) (T : Bounds) (p rho : Nat)
    (ph : P1Target.Layout Nat) : UniformJoin.TargetData α :=
  ⟨shift f T.lo,T.hi-T.lo,T.period,p,rho,(segment f 0 n).drop T.hi,
    ph,T.lo+p,key⟩

/-- Exact equality of the two period words joins all represented source
    lengths at once. The only cross-run regular test is the actual C gap. -/
theorem join_sound [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n : Nat)
    (S T : Bounds) (hS : S.Valid f n) (hT : T.Valid f n)
    (a phase p rho m : Nat) (ph : P1Target.Layout Nat)
    (hp : p≤T.hi-T.lo) (horder : S.lo+a≤T.lo+p)
    (hr : P1SourceFamily.residue S.period a phase=rho)
    (hword : segment (shift f S.lo) phase S.period=
      segment (shift f T.lo) ph.j T.period)
    (hs : decideFormula (P1SourceFamily.formula P f S a phase) [(m:Int)]=true)
    (ht : decideFormula (P1Target.projection P (shift f T.lo) (T.hi-T.lo)
      T.period p rho ((segment f 0 n).drop T.hi) ph) [(m:Int)]=true)
    (hC : P.C.accepts (Spec.slice (segment f 0 n) (S.lo+a) (T.lo+p))) :
    MatchesWithin P.nested1 (segment f 0 n) 2 := by
  have htb : T.lo+p≤n := by
    have hh := hT.2.1
    have hl := hT.1
    omega
  have hsource := UniformJoin.localSource_with_gap P (shift f S.lo)
    (S.hi-S.lo) S.period a phase (P1SourceFamily.residue S.period a phase) m
    (segment f 0 S.lo) (Spec.slice (segment f 0 n) (S.lo+a) (T.lo+p))
    hS.2.2.2.1.2.1 hS.2.2.2.1.1 hs hC
  rw [prefix_local,prefix_gap f n (S.lo+a) (T.lo+p) horder htb,hr,hword] at hsource
  have htlo : T.lo≤(segment f 0 n).length := by
    rw [segment_length]
    have hh := hT.2.1
    have hl := hT.1
    omega
  have hpre : (segment f 0 n).take T.lo++P2Periodic.factor (shift f T.lo) 0 p=
      segment f 0 (T.lo+p) := by
    rw [SmallPeriodP2.segment_take f 0 n T.lo (by simpa only [segment_length] using htlo)]
    simpa only [P2Periodic.factor,Nat.sub_zero] using prefix_local f T.lo p
  have hj := P1Target.projected_join_sound P (shift f T.lo) (T.hi-T.lo)
    T.period p rho m hT.2.2.2.1 hp ((segment f 0 n).take T.lo)
    ((segment f 0 n).drop T.hi) ph ht (by rwa [hpre])
  rwa [SmallPeriodP2.text_reconstruct f n T.lo T.hi
    (by have hh := hT.1; omega) hT.2.1] at hj

/-- A concrete long-inner P1 witness in one target run. The earlier
    source need not initially be supplied with any periodic interval. -/
structure LongWitness (P : SevenDFA α) (f : Nat→α) (n : Nat) (T : Bounds) where
  outerStart : Nat
  target : P1Target.Layout Nat
  earlierStart : Nat
  target_ok : P1Target.Witness P (shift f T.lo) (T.hi-T.lo) outerStart
    ((segment f 0 n).drop T.hi) target
  long_inner : 3*T.period≤target.t-target.j
  earlier : earlierStart+(target.t-target.j)≤T.lo+outerStart
  equal_inner : segment f earlierStart (target.t-target.j)=
    P2Periodic.factor (shift f T.lo) target.j target.t
  prefix_ok : P.A.accepts (segment f 0 earlierStart)
  gap_ok : P.C.accepts (Spec.slice (segment f 0 n)
    (earlierStart+(target.t-target.j)) (T.lo+outerStart))

def LongWitness.innerLength {P : SevenDFA α} {f : Nat→α} {n : Nat} {T : Bounds}
    (w : LongWitness P f n T) : Nat := w.target.t-w.target.j

/-- Exact conditions on one source/target record pair. -/
def PairFacts [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat)
    (T : Bounds) (w : LongWitness P f n T) (S : Bounds) (v : P1PhaseFamily.Three) : Prop :=
  S.Valid f n ∧ S.period=T.period ∧ S.lo≤w.earlierStart ∧
  w.earlierStart+w.innerLength≤S.hi ∧ S∈SmallPeriodRuns.cubic f n Q ∧
  T∈SmallPeriodRuns.cubic f n Q ∧
  (w.earlierStart+w.innerLength-S.lo,(w.earlierStart-S.lo)%T.period)∈
    P1SourceFamily.choices S.period (S.hi-S.lo) ∧
  (w.outerStart,v)∈P1PhaseFamily.targets T.period (T.hi-T.lo) ∧
  P1SourceFamily.residue S.period (w.earlierStart+w.innerLength-S.lo)
    ((w.earlierStart-S.lo)%T.period)=v.rho ∧
  decideFormula (P1SourceFamily.formula P f S
      (w.earlierStart+w.innerLength-S.lo) ((w.earlierStart-S.lo)%T.period))
    [((w.innerLength/T.period : Nat) : Int)]=true ∧
  decideFormula (P1Target.projection P (shift f T.lo)
      (T.hi-T.lo) T.period w.outerStart v.rho ((segment f 0 n).drop T.hi)
      (P1PhaseFamily.extend T.period w.outerStart v))
    [((w.innerLength/T.period : Nat) : Int)]=true ∧
  segment (shift f S.lo) ((w.earlierStart-S.lo)%T.period) S.period=
    segment (shift f T.lo) (P1PhaseFamily.extend T.period w.outerStart v).j T.period

/-- Generated pair with a compact proof field, to keep record elaboration
    independent of the internal arithmetic compiler definitions. -/
structure LongPair [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat)
    (T : Bounds) (w : LongWitness P f n T) where
  source : Bounds
  phases : P1PhaseFamily.Three
  facts : PairFacts P f n Q T w source phases

namespace LongPair
variable [DecidableEq α] {P : SevenDFA α} {f : Nat→α} {n Q : Nat}
  {T : Bounds} {w : LongWitness P f n T}

theorem valid (z : LongPair P f n Q T w) :
    z.source.Valid f n := z.facts.1

theorem period (z : LongPair P f n Q T w) :
    z.source.period=T.period := z.facts.2.1

theorem left (z : LongPair P f n Q T w) :
    z.source.lo≤w.earlierStart := z.facts.2.2.1

theorem right (z : LongPair P f n Q T w) :
    w.earlierStart+w.innerLength≤z.source.hi := z.facts.2.2.2.1

theorem source_mem (z : LongPair P f n Q T w) :
    z.source∈SmallPeriodRuns.cubic f n Q := z.facts.2.2.2.2.1

theorem target_mem (z : LongPair P f n Q T w) :
    T∈SmallPeriodRuns.cubic f n Q := z.facts.2.2.2.2.2.1

theorem source_choice (z : LongPair P f n Q T w) :
    (w.earlierStart+w.innerLength-z.source.lo,(w.earlierStart-z.source.lo)%T.period)∈
      P1SourceFamily.choices z.source.period (z.source.hi-z.source.lo) := z.facts.2.2.2.2.2.2.1

theorem target_choice (z : LongPair P f n Q T w) :
    (w.outerStart,z.phases)∈P1PhaseFamily.targets T.period (T.hi-T.lo) := z.facts.2.2.2.2.2.2.2.1

theorem residue (z : LongPair P f n Q T w) :
    P1SourceFamily.residue z.source.period (w.earlierStart+w.innerLength-z.source.lo)
      ((w.earlierStart-z.source.lo)%T.period)=z.phases.rho := z.facts.2.2.2.2.2.2.2.2.1

theorem source_accepted (z : LongPair P f n Q T w) :
    decideFormula (P1SourceFamily.formula P f z.source
      (w.earlierStart+w.innerLength-z.source.lo) ((w.earlierStart-z.source.lo)%T.period))
      [((w.innerLength/T.period : Nat) : Int)]=true := z.facts.2.2.2.2.2.2.2.2.2.1

theorem target_accepted (z : LongPair P f n Q T w) :
    decideFormula (P1Target.projection P (shift f T.lo) (T.hi-T.lo) T.period
      w.outerStart z.phases.rho ((segment f 0 n).drop T.hi)
      (P1PhaseFamily.extend T.period w.outerStart z.phases))
      [((w.innerLength/T.period : Nat) : Int)]=true := z.facts.2.2.2.2.2.2.2.2.2.2.1

theorem word (z : LongPair P f n Q T w) :
    segment (shift f z.source.lo) ((w.earlierStart-z.source.lo)%T.period) z.source.period=
      segment (shift f T.lo) (P1PhaseFamily.extend T.period w.outerStart z.phases).j T.period := z.facts.2.2.2.2.2.2.2.2.2.2.2

end LongPair

theorem long_complete [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat)
    (T : Bounds) (hT : T.Valid f n) (hq : T.period≤Q)
    (w : LongWitness P f n T) : Nonempty (LongPair P f n Q T w) := by
  have ho := w.target_ok
  obtain ⟨h1,h2,h3,h4,h5,h6,_⟩ := ho
  have hlo := hT.1
  have hhi := hT.2.1
  have hlong := w.long_inner
  have hearlier := w.earlier
  have heq : segment f w.earlierStart w.innerLength=
      segment f (T.lo+w.target.j) w.innerLength := by
    have hh := w.equal_inner
    unfold P2Periodic.factor at hh
    rwa [LongSourceCoverage.segment_shift] at hh
  obtain ⟨S,hS,hp,hsl,hsr,hsmem,hr,hs,hword⟩ :=
    P1SourceFamily.long_source_complete P f n Q w.earlierStart
      (T.lo+w.target.j) w.innerLength T hT hq (by omega)
      (by dsimp only [LongWitness.innerLength]; omega) hlong
      (by dsimp only [LongWitness.innerLength]; omega) heq w.prefix_ok
  have htc : 3*T.period≤T.hi-T.lo := by omega
  have htm := (SmallPeriodRuns.cubic_mem f n Q T).mpr ⟨hT,hq,htc⟩
  obtain ⟨v,hv,hphase,hres⟩ := P1PhaseFamily.phase_family P (shift f T.lo)
    (T.hi-T.lo) T.period w.outerStart hT.2.2.2.1 ((segment f 0 n).drop T.hi)
    w.target w.target_ok (by omega)
  have ht := P1PhaseFamily.projection_complete P (shift f T.lo) (T.hi-T.lo)
    T.period w.outerStart hT.2.2.2.1 ((segment f 0 n).drop T.hi) w.target w.target_ok
  have hsj : (T.lo+w.target.j-T.lo)%T.period=w.target.j%T.period := by
    rw [Nat.add_sub_cancel_left]
  rw [hsj] at hword
  have hvj : (P1PhaseFamily.extend T.period w.outerStart v).j=w.target.j%T.period :=
    congrArg P1Target.Layout.j hphase
  obtain ⟨hSm,hchoices⟩ := (P1SourceFamily.allSources_mem _ S _ _).mp hsmem
  refine ⟨⟨S,v,⟨hS,hp,hsl,hsr,hSm,htm,hchoices,?_,?_,hs,?_,?_⟩⟩⟩
  · exact List.mem_flatMap.mpr ⟨w.outerStart,List.mem_range.mpr (by omega),
      List.mem_map.mpr ⟨v,hv,rfl⟩⟩
  · rw [hp]
    exact hr.trans hres.symm
  · rw [hphase,hres]
    exact ht
  · rw [hp,hvj]
    exact hword

end REWB.P1GlobalJoin
