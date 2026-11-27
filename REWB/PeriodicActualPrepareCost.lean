import REWB.PeriodicActualPrepare
import REWB.PeriodicActualP2Cost

/-! The actual additional P1 preparation operations are absorbed by fixed
pattern coefficients of the existing degree-69 periodic expressions. -/
namespace REWB.PeriodicActual
open REWB.PeriodicAccounting
variable {σ : Nat}

theorem eventCells_length (es : List TimedJoin.TimedEntry) :
    es.length≤ActualModulus.eventCells es := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
    simp only [ActualModulus.eventCells,List.map_cons,List.sum_cons,List.length_cons]
    simp only [ActualModulus.eventCells] at ih
    omega

theorem long_expr_input (P : SevenDFA (Fin σ)) (n Q : Nat) :
    n+1≤(longExpr P).eval n Q := by
  change n+1≤_+4*(n+1)
  omega

theorem long_expr_text (P : SevenDFA (Fin σ)) (n Q : Nat) :
    (DyadicIndex.heightFor n+1)*n≤(longExpr P).eval n Q := by
  change (n.log2+1+1)*n≤_+(n.log2+1+1)*n+_+4*(n+1)
  omega

theorem short_expr_input (P : SevenDFA (Fin σ)) (n Q : Nat) :
    n+1≤(shortExpr P).eval n Q := by
  change n+1≤_+4*(n+1)
  omega

theorem short_expr_text (P : SevenDFA (Fin σ)) (n Q : Nat) :
    (DyadicIndex.heightFor n+1)*n≤(shortExpr P).eval n Q := by
  change (n.log2+1+1)*n≤_+(n.log2+1+1)*n+_+4*(n+1)
  omega

theorem short_expr_sources (P : SevenDFA (Fin σ)) (n Q : Nat) :
    (n+1)*(3*Q)≤(shortExpr P).eval n Q := by
  change (n+1)*(3*Q)≤_+(n+1)*(3*Q)+_+_+_+_+_+_+_+_
  omega

theorem mass_le_text (n B : Nat) (h : (DyadicIndex.heightFor n+1)*n≤B) :
    2*n*DyadicIndex.heightFor n≤2*B := by
  have hh := Nat.mul_le_mul_right n
    (show DyadicIndex.heightFor n≤DyadicIndex.heightFor n+1 by omega)
  have hb := Nat.mul_le_mul_left 2 (Nat.le_trans hh h)
  have he : 2*(DyadicIndex.heightFor n*n)=2*n*DyadicIndex.heightFor n := by ac_rfl
  rwa [he] at hb

namespace Long

def coefficient (P : SevenDFA (Fin σ)) : Nat := Events.sourceBudget P+Events.targetBudget P+110

theorem prepare_expr (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).work≤coefficient P*(longExpr P).eval n Q := by
  let old := CountedSmallPeriodP1.solve P f n Q
  let B := (longExpr P).eval n Q
  let S := Events.sourceBudget P+39
  let T := Events.targetBudget P+37
  have hh := prepare_work P f n Q
  have hs := eventCells_length (P1Events.generated P f n Q).sources
  have ht := eventCells_length (P1Events.generated P f n Q).targets
  have hm := CountedSmallPeriodP1.solve_modulus_steps P f n Q
  have hlen : (P1Events.generated P f n Q).sources.length+
      (P1Events.generated P f n Q).targets.length≤old.modulusSteps := by
    change (CountedSmallPeriodP1.solve P f n Q).modulusSteps=_ at hm
    change _≤(CountedSmallPeriodP1.solve P f n Q).modulusSteps
    omega
  have hbase : old.runComparisons+old.contextEntries+old.keyWork+old.cacheWork+old.modulusSteps≤longWork old := by
    unfold longWork
    omega
  have hmod : old.modulusSteps≤longWork old := by unfold longWork; omega
  have hevents : S*(P1Events.generated P f n Q).sources.length+
      T*(P1Events.generated P f n Q).targets.length≤(S+T)*longWork old := by
    have hsa := Nat.mul_le_mul_right (P1Events.generated P f n Q).sources.length
      (show S≤S+T by omega)
    have hta := Nat.mul_le_mul_right (P1Events.generated P f n Q).targets.length
      (show T≤S+T by omega)
    have hsum := Nat.add_le_add hsa hta
    rw [← Nat.mul_add] at hsum
    exact Nat.le_trans hsum (Nat.mul_le_mul_left (S+T) (Nat.le_trans hlen hmod))
  have hold : longWork old≤B := long_bound P f n Q
  have hmain := Nat.add_le_add hbase hevents
  have hmain' : old.runComparisons+old.contextEntries+old.keyWork+old.cacheWork+old.modulusSteps+
      S*(P1Events.generated P f n Q).sources.length+
      T*(P1Events.generated P f n Q).targets.length≤(S+T+1)*B := by
    have he : longWork old+(S+T)*longWork old=(S+T+1)*longWork old := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    rw [he] at hmain
    exact Nat.le_trans (by simpa only [Nat.add_assoc] using hmain)
      (Nat.mul_le_mul_left (S+T+1) hold)
  have hmass := Nat.mul_le_mul_left 5 (mass_le_text n B (long_expr_text P n Q))
  have hin := long_expr_input P n Q
  have hlin : 3*n+23≤23*B := by change n+1≤B at hin; omega
  have hcoeff : coefficient P=S+T+34 := by
    dsimp only [coefficient,S,T]
    omega
  rw [hcoeff]
  change (prepare P f n Q).work≤(S+T+34)*B
  simp only [Nat.add_mul]
  change (prepare P f n Q).work≤old.runComparisons+old.contextEntries+old.keyWork+old.cacheWork+
    old.modulusSteps+S*(_)+T*(_)+5*(2*n*DyadicIndex.heightFor n)+3*n+23 at hh
  simp only [Nat.add_mul] at hmain'
  omega

theorem prepare_rounded (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    (prepare P f n (ThresholdBudget.period n)).work≤
      (coefficient P*(longExpr P).coeff)*(ThresholdBudget.base n)^75 := by
  have hb := Expr.bound75 (longExpr P) (by rw [long_degree]; decide) n
  exact Nat.le_trans (prepare_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (coefficient P) hb)

end Long

namespace Short

theorem target_tests (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (es : List (RunGeometry.Bounds×Array Nat)) :
    (CountedShortTargets.targets P f I es).exponentTests=
      3*(P1PhaseFamily.allTargets (es.map Prod.fst)).length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change (CountedShortTargets.runTargets P f I e).exponentTests+
      (CountedShortTargets.targets P f I es).exponentTests=_
    rw [CountedShortTargets.runTargets_tests,ih]
    simp only [List.map_cons,P1PhaseFamily.allTargets,List.length_append,List.length_map,Nat.mul_add]

def coefficient (P : SevenDFA (Fin σ)) : Nat := choiceBudget P+133

theorem prepare_expr (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).work≤coefficient P*(shortExpr P).eval n Q := by
  let old := CountedShortBranch.solve P f n Q
  let B := (shortExpr P).eval n Q
  let T := choiceBudget P+58
  let A := (P1PhaseFamily.allTargets ((P1ShortBranch.keyTables f n Q).tables.map Prod.fst)).length
  have hh := prepare_work P f n Q
  have ht := target_tests P f (BoundaryContexts.build P (Periodic.segment f 0 n)).1
    (P1ShortBranch.keyTables f n Q).tables
  have htests : A≤old.targets.exponentTests := by
    change (CountedShortBranch.solve P f n Q).targets.exponentTests=_ at ht
    change A≤(CountedShortBranch.solve P f n Q).targets.exponentTests
    change (CountedShortBranch.solve P f n Q).targets.exponentTests=3*A at ht
    omega
  have hat : old.targets.exponentTests≤shortWork old := by
    unfold shortWork CountedShortBranch.Result.targetWork CountedShortTargets.work
    omega
  have hbase : old.runComparisons+old.contextEntries+old.keyWork+old.targets.cacheWork≤shortWork old := by
    unfold shortWork
    omega
  have hsc : old.sourcePrefixReads+old.sourceWordCells≤shortWork old := by unfold shortWork; omega
  have hsc' : 17*old.sourcePrefixReads+3*old.sourceWordCells≤17*shortWork old := by
    have hb := Nat.mul_le_mul_left 17 hsc
    simp only [Nat.mul_add] at hb
    omega
  have htar := Nat.mul_le_mul_left T (Nat.le_trans htests hat)
  have hold : shortWork old≤B := short_bound P f n Q
  have hmain : old.runComparisons+old.contextEntries+old.keyWork+old.targets.cacheWork+
      17*old.sourcePrefixReads+3*old.sourceWordCells+T*A≤(T+18)*B := by
    have hsum := Nat.add_le_add (Nat.add_le_add hbase hsc') htar
    have he : shortWork old+17*shortWork old+T*shortWork old=(T+18)*shortWork old := by
      simp only [Nat.add_mul]
      omega
    rw [he] at hsum
    exact Nat.le_trans (by simpa only [Nat.add_assoc] using hsum)
      (Nat.mul_le_mul_left (T+18) hold)
  have hsrc := Nat.mul_le_mul_left 9 (short_expr_sources P n Q)
  have hmass := Nat.mul_le_mul_left 5 (mass_le_text n B (short_expr_text P n Q))
  have hin := short_expr_input P n Q
  have hlin : 10*n+38≤38*B := by change n+1≤B at hin; omega
  have hcoeff : coefficient P=T+75 := by
    dsimp only [coefficient,T]
  rw [hcoeff]
  change (prepare P f n Q).work≤(T+75)*B
  simp only [Nat.add_mul]
  change (prepare P f n Q).work≤old.runComparisons+old.contextEntries+old.keyWork+old.targets.cacheWork+
    17*old.sourcePrefixReads+3*old.sourceWordCells+T*A+9*((n+1)*(3*Q))+
    5*(2*n*DyadicIndex.heightFor n)+10*n+38 at hh
  change 9*((n+1)*(3*Q))≤9*B at hsrc
  simp only [Nat.add_mul] at hmain
  omega

theorem prepare_rounded (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    (prepare P f n (ThresholdBudget.period n)).work≤
      (coefficient P*(shortExpr P).coeff)*(ThresholdBudget.base n)^75 := by
  have hb := Expr.bound75 (shortExpr P) (by rw [short_degree]; decide) n
  exact Nat.le_trans (prepare_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (coefficient P) hb)

end Short
end REWB.PeriodicActual
