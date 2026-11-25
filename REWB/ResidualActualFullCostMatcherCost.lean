import REWB.ResidualActualFullCostMatcherCostBase
import REWB.ResidualActualFullCostDispatchCost
import REWB.ResidualActualFullCostIndependentCost

/-! The actual six-constructor dispatch, finite normalized form list and
original source expression satisfy the rounded accounted-work target.
The charge is arbitrary fixed-pattern work per counted action build.

These are bounds for the concrete returned ledgers, including measured
all-start row factories and external periodic formula/event/join assembly.
Inherited primitive transition/comparison counters keep their documented
scope. Machine-bit, reference-counting, allocator and garbage-collector
costs are not asserted. -/
namespace REWB.ResidualActual.FullCost.Matcher.Cost
open REWB.ResidualCached.Growth
variable {σ : Nat}

theorem p1_charged_bound (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (P1.auto P text fallback).accountedWork+charge*(P1.auto P text fallback).fixedPatternBuilds≤
        coefficient*scale text.size := by
  obtain ⟨coefficient,hc⟩:=ResidualActual.FullCost.Cost.auto_charged_bound P charge
  refine ⟨coefficient,?_⟩
  intro text fallback
  have hh:=hc text fallback
  have hb : (P1.auto P text fallback).accountedWork+(P2.auto P text fallback).accountedWork+
      charge*((P1.auto P text fallback).fixedPatternBuilds+(P2.auto P text fallback).fixedPatternBuilds)≤
      coefficient*scale text.size := by
    simpa only [scale,Nat.mul_assoc] using hh
  rw [Nat.mul_add] at hb
  omega

theorem p2_charged_bound (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (P2.auto P text fallback).accountedWork+charge*(P2.auto P text fallback).fixedPatternBuilds≤
        coefficient*scale text.size := by
  obtain ⟨coefficient,hc⟩:=ResidualActual.FullCost.Cost.auto_charged_bound P charge
  refine ⟨coefficient,?_⟩
  intro text fallback
  have hh:=hc text fallback
  have hb : (P1.auto P text fallback).accountedWork+(P2.auto P text fallback).accountedWork+
      charge*((P1.auto P text fallback).fixedPatternBuilds+(P2.auto P text fallback).fixedPatternBuilds)≤
      coefficient*scale text.size := by
    simpa only [scale,Nat.mul_assoc] using hh
  rw [Nat.mul_add] at hb
  omega

theorem form_charged_bound (F : CompleteNormalization.Form (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (form F text fallback).accountedWork+charge*(form F text fallback).fixedPatternBuilds≤
        coefficient*scale text.size := by
  cases F with
  | regular A =>
    refine ⟨3,?_⟩
    intro text fallback
    have h:=Nat.mul_le_mul_left 3 (scale_length text.size)
    change 3*text.size+5+charge*0≤_
    omega
  | once A B C E =>
    obtain ⟨coefficient,hc⟩:=p2_charged_bound (oncePattern A B C E) charge
    refine ⟨coefficient+3,?_⟩
    intro text fallback
    have hh:=add_fixed (hc text fallback) 3
    change (P2.auto (oncePattern A B C E) text fallback).accountedWork+3+
      charge*(P2.auto (oncePattern A B C E) text fallback).fixedPatternBuilds≤_
    omega
  | sameValue P =>
    obtain ⟨coefficient,hc⟩:=p1_charged_bound (samePattern P) charge
    refine ⟨coefficient+3,?_⟩
    intro text fallback
    have hh:=add_fixed (hc text fallback) 3
    change (P1.auto (samePattern P) text fallback).accountedWork+3+
      charge*(P1.auto (samePattern P) text fallback).fixedPatternBuilds≤_
    omega
  | independent P =>
    obtain ⟨coefficient,hc⟩:=Independent.Cost.execute_charged_rounded P charge
    refine ⟨coefficient+3,?_⟩
    intro text fallback
    have hb : (Independent.execute P text fallback).2+
        charge*(Independent.execute P text fallback).1.fixedPatternBuilds≤coefficient*scale text.size := by
      simpa only [scale,Nat.mul_assoc] using hc text fallback
    have hh:=add_fixed hb 3
    change (Independent.execute P text fallback).2+3+
      charge*(Independent.execute P text fallback).1.fixedPatternBuilds≤_
    omega
  | nested1 P =>
    obtain ⟨coefficient,hc⟩:=p1_charged_bound P charge
    refine ⟨coefficient+3,?_⟩
    intro text fallback
    have hh:=add_fixed (hc text fallback) 3
    change (P1.auto P text fallback).accountedWork+3+charge*(P1.auto P text fallback).fixedPatternBuilds≤_
    omega
  | nested2 P =>
    obtain ⟨coefficient,hc⟩:=p2_charged_bound P charge
    refine ⟨coefficient+3,?_⟩
    intro text fallback
    have hh:=add_fixed (hc text fallback) 3
    change (P2.auto P text fallback).accountedWork+3+charge*(P2.auto P text fallback).fixedPatternBuilds≤_
    omega

theorem run_charged_bound (compiled : Compiled σ) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (run compiled text fallback).accountedWork+charge*(run compiled text fallback).fixedPatternBuilds≤
        coefficient*scale text.size :=
  run_charged_of_forms compiled charge (fun F _=>form_charged_bound F charge)

theorem solve_charged_bound (p : Expr (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (solve p text fallback).accountedWork+charge*(solve p text fallback).fixedPatternBuilds≤
        coefficient*scale text.size :=
  run_charged_bound (compile p) charge

theorem solve_target (p : Expr (Fin σ)) (charge : Nat) (texts : Nat→Array (Fin σ))
    (fallback : Fin σ) (hsize : ∀n,(texts n).size=n) :
    Spec.Target25Over13 (fun n=>(solve p (texts n) fallback).accountedWork+
      charge*(solve p (texts n) fallback).fixedPatternBuilds) := by
  obtain ⟨coefficient,hc⟩:=solve_charged_bound p charge
  apply target_of_bound _ coefficient
  intro n
  simpa only [hsize n] using hc (texts n) fallback

/-- The original word entry point additionally materializes its array
once. The fixed-pattern normalizer can be compiled and reused separately. -/
def wordWork (p : Expr (Fin σ)) (fallback : Fin σ) (charge : Nat) (w : Word (Fin σ)) : Nat :=
  let out:=solve p w.toArray fallback
  out.accountedWork+charge*out.fixedPatternBuilds+w.length+2

theorem word_charged_bound (p : Expr (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ),
      wordWork p fallback charge w≤coefficient*scale w.length := by
  obtain ⟨coefficient,hc⟩:=solve_charged_bound p charge
  refine ⟨coefficient+1,?_⟩
  intro w fallback
  have h:=hc w.toArray fallback
  rw [List.size_toArray] at h
  have hn:=scale_length w.length
  unfold wordWork
  dsimp only
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem word_target (p : Expr (Fin σ)) (charge : Nat) (words : Nat→Word (Fin σ))
    (fallback : Fin σ) (hsize : ∀n,(words n).length=n) :
    Spec.Target25Over13 (fun n=>wordWork p fallback charge (words n)) := by
  obtain ⟨coefficient,hc⟩:=word_charged_bound p charge
  apply target_of_bound _ coefficient
  intro n
  simpa only [hsize n] using hc (words n) fallback

theorem correctMatcher_with_accounting (p : Expr (Fin σ)) (fallback : Fin σ) (charge : Nat)
    (words : Nat→Word (Fin σ)) (hsize : ∀n,(words n).length=n) :
    Spec.CorrectMatcher p (matchWord p fallback) ∧
      Spec.Target25Over13 (fun n=>wordWork p fallback charge (words n)) :=
  ⟨Matcher.correctMatcher p fallback,word_target p charge words fallback hsize⟩

end REWB.ResidualActual.FullCost.Matcher.Cost
