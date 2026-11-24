import REWB.P1Target

/-! A source ending at a known point of an earlier periodic interval.
    The source start block is determined by the free exponent, so there
    is no enumeration of its possible lengths. The text between the
    source end and the outer capture is supplied as a C-context. -/
namespace REWB.P1Source
open REWB.Periodic
open REWB.PhaseSolver
open REWB.AffineProjection
open REWB.P2Periodic (factor factor_split zeroEndpoint zero_valid zero_pos endEndpoint end_pos end_valid interval_factor)
open REWB.P1Target (keyWord SourceOK)
variable {α : Type}

def start (q a phase : Nat) : Endpoint :=
  let endp := endEndpoint q a
  let fromPhase : Endpoint := (.lit 0,phase)
  (((Aff.lit (Int.ofNat (a/q))).sub (.lit (Int.ofNat (carry fromPhase endp)))).sub (.var 0),phase)

theorem start_number (q a phase m : Nat) :
    (start q a phase).number [(m:Int)]=
      (Int.ofNat (a/q))-(carry (start q a phase) (endEndpoint q a):Int)-(m:Int) := by
  unfold start Endpoint.number
  simp only [Aff.eval_sub,Aff.eval]
  rfl

theorem source_count (q n a phase m : Nat) (h : 0<q)
    (ha : (start q a phase).valid q n [(m:Int)])
    (hb : a≤n) (ho : (start q a phase).pos q [(m:Int)]≤a) :
    (countExpr (start q a phase) (endEndpoint q a)).eval [(m:Int)]=(m:Int) := by
  rw [count_eval,start_number]
  change (Int.ofNat (a/q))-((Int.ofNat (a/q))-
    (carry (start q a phase) (endEndpoint q a):Int)-(m:Int))-
    (carry (start q a phase) (endEndpoint q a):Int)=(m:Int)
  omega

def formula (P : SevenDFA α) (s : Nat→α) (n q a phase rho : Nat)
    (pre gap : Word α) : Formula :=
  let l := start q a phase
  let r := endEndpoint q a
  if decide (tailLen q l r=rho) && P.C.final (P.C.run P.C.initial gap) then
    both (regularFormula q n s (contextual P.A pre []) zeroEndpoint l)
      (orderFormula q n l r)
  else []

theorem formula_good (P : SevenDFA α) (s : Nat→α) (n q a phase rho : Nat)
    (pre gap : Word α) (h : Period s n q) :
    FormulaGood (formula P s n q a phase rho pre gap) := by
  unfold formula
  dsimp only
  split
  · exact both_good _ _ (regularFormula_good _ _ _ _ _ _ h) (orderFormula_good _ _ _ _)
  · intro C hC
    simp at hC

theorem formula_correct (P : SevenDFA α) (s : Nat→α) (n q a phase rho m : Nat)
    (pre gap : Word α) (h : Period s n q) (hq : 0<q) :
    decideFormula (formula P s n q a phase rho pre gap) [(m:Int)]=true ↔
      let env := [(m:Int)]
      let l := start q a phase
      l.valid q n env ∧ (endEndpoint q a).valid q n env ∧
        l.pos q env≤a ∧ tailLen q l (endEndpoint q a)=rho ∧
        P.A.accepts (pre++factor s 0 (l.pos q env)) ∧ P.C.accepts gap := by
  rw [decideFormula_correct _ _ (formula_good P s n q a phase rho pre gap h)]
  unfold formula
  dsimp only
  let l := start q a phase
  let r := endEndpoint q a
  change Satisfies (if decide (tailLen q l r=rho) && P.C.final (P.C.run P.C.initial gap) then
    both (regularFormula q n s (contextual P.A pre []) zeroEndpoint l)
      (orderFormula q n l r) else []) [(m:Int)] ↔
    l.valid q n [(m:Int)] ∧ r.valid q n [(m:Int)] ∧
      l.pos q [(m:Int)]≤a ∧ tailLen q l r=rho ∧
      P.A.accepts (pre++factor s 0 (l.pos q [(m:Int)])) ∧ P.C.accepts gap
  by_cases hr : tailLen q l r=rho
  · by_cases hc : P.C.final (P.C.run P.C.initial gap)=true
    · have hcond : (decide (tailLen q l r=rho) && P.C.final (P.C.run P.C.initial gap))=true := by simp [hr,hc]
      rw [if_pos hcond,both_correct,regularFormula_correct _ _ _ _ _ _ _ hq h,
        orderFormula_correct _ _ _ _ _ hq]
      have hpos : r.pos q [(m:Int)]=a := end_pos q a _
      simp only [zero_pos,interval_factor,contextual_accepts,List.append_nil,hpos]
      constructor
      · rintro ⟨⟨_,_,_,hA⟩,hl,hr',ho⟩
        exact ⟨hl,hr',ho,hr,hA,hc⟩
      · rintro ⟨hl,hr',ho,_,hA,_⟩
        exact ⟨⟨zero_valid q n _ hq,hl,Nat.zero_le _,hA⟩,hl,hr',ho⟩
    · have hcond : ¬(decide (tailLen q l r=rho) && P.C.final (P.C.run P.C.initial gap))=true := by
        simp [hr,hc]
      rw [if_neg hcond]
      constructor
      · rintro ⟨C,hC,_⟩
        simp at hC
      · rintro ⟨_,_,_,_,_,hC⟩
        exact False.elim (hc hC)
  · have hcond : ¬(decide (tailLen q l r=rho) && P.C.final (P.C.run P.C.initial gap))=true := by simp [hr]
    rw [if_neg hcond]
    constructor
    · rintro ⟨C,hC,_⟩
      simp at hC
    · rintro ⟨_,_,_,ht,_,_⟩
      exact False.elim (hr ht)

theorem source_sound (P : SevenDFA α) (s : Nat→α) (n q a phase rho m : Nat)
    (pre gap : Word α) (h : Period s n q) (hq : 0<q)
    (hs : decideFormula (formula P s n q a phase rho pre gap) [(m:Int)]=true) :
    SourceOK P (pre++segment s 0 a++gap) (keyWord (segment s phase q) rho m) := by
  obtain ⟨hl,hr,ho,ht,hA,hC⟩ := (formula_correct P s n q a phase rho m pre gap h hq).mp hs
  let l := start q a phase
  let env := [(m:Int)]
  have han : a≤n := by
    have hh := hr.2.2
    rwa [end_pos] at hh
  have horder : l.pos q env≤(endEndpoint q a).pos q env := by rwa [end_pos]
  have hcount := source_count q n a phase m hq hl han ho
  have he := P1Target.key_factor s q n h l (endEndpoint q a) env hl hr horder hq m rho hcount ht
  rw [end_pos] at he
  change factor s (l.pos q env) a=keyWord (segment s phase q) rho m at he
  refine ⟨pre++factor s 0 (l.pos q env),gap,?_,hA,hC⟩
  change pre++factor s 0 a++gap=_
  rw [factor_split s 0 (l.pos q env) a (Nat.zero_le _) ho,he]
  simp only [List.append_assoc]

/-- Join two independently compressed periodic factors by an exact
    phase-word key and a common free exponent. The source is allowed
    to lie in a different earlier run. No claim of efficient enumeration
    of source events or of an amortized index is made here. -/
theorem join_sources [DecidableEq α] (P : SevenDFA α)
    (source target : Nat→α) (nS nT q a p phase rho m : Nat)
    (preS gap preT postT : Word α) (ph : P1Target.Layout Nat)
    (hS : Period source nS q) (hT : LeastPeriod target nT q) (hp : p≤nT)
    (htext : preT++factor target 0 p=preS++segment source 0 a++gap)
    (hkey : segment source phase q=segment target ph.j q)
    (hs : decideFormula (formula P source nS q a phase rho preS gap) [(m:Int)]=true)
    (ht : decideFormula (P1Target.projection P target nT q p rho postT ph) [(m:Int)]=true) :
    MatchesWithin P.nested1 (preT++segment target 0 nT++postT) 2 := by
  apply P1Target.projected_join_sound P target nT q p rho m hT hp preT postT ph ht
  rw [htext,← hkey]
  exact source_sound P source nS q a phase rho m preS gap hS hT.1 hs

end REWB.P1Source
