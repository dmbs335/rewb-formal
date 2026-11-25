import REWB.MaskedPeriodicBatch

/-! The complete generated run list pays for every visited source and
every immutable target-mask prefix array. Cubic spans are charged to the
proved primitive-square mass; spans of arbitrary runs are never summed.
The query-ledger scope is inherited from `MaskedPeriodicBatchQueryCost`.
-/
namespace REWB.MaskedPeriodic.Batch
open REWB.Spec REWB.RunGeometry REWB.MaskedCut REWB.MaskedCut.DFAIndex
variable {α : Type} {σ : Nat}

theorem totalSpan_mass (Rs : List Bounds)
    (hc : ∀ R,R∈Rs → 3*R.period≤R.hi-R.lo) :
    totalSpan Rs≤3*RunBudget.totalMass Rs := by
  induction Rs with
  | nil => simp [totalSpan,RunBudget.totalMass]
  | cons R Rs ih =>
    have hh:=GlobalCoverage.cubic_length_mass R (hc R List.mem_cons_self)
    have ht:=ih (fun S hS=>hc S (List.mem_cons_of_mem R hS))
    change span R+totalSpan Rs≤3*(RunBudget.mass R+RunBudget.totalMass Rs)
    unfold span
    rw [Nat.mul_add]
    omega

theorem totalSpan_bound (f : Nat → α) (n : Nat) (Rs : List Bounds) (hd : Rs.Nodup)
    (hv : ∀ R,R∈Rs → R.Valid f n) (hc : ∀ R,R∈Rs → 3*R.period≤R.hi-R.lo) :
    totalSpan Rs≤6*n*(n.log2+1) := by
  have hs:=totalSpan_mass Rs hc
  have hm:=Nat.mul_le_mul_left 3 (RunBudget.totalMass_bound f n Rs hd hv)
  have he : 3*(2*n*DyadicIndex.heightFor n)=6*n*(n.log2+1) := by
    unfold DyadicIndex.heightFor
    rw [←Nat.mul_assoc,←Nat.mul_assoc]
  rw [he] at hm
  exact Nat.le_trans hs hm

theorem enumerated_span (text : Array (Fin σ)) (fallback : Fin σ) :
    totalSpan (MaskedOrdered.Owner.enumerateAuto text fallback).runs≤
      6*text.size*(text.size.log2+1) :=
  totalSpan_bound (ArrayText.read text fallback) text.size _
    (MaskedOrdered.Owner.enumerateAuto_nodup text fallback)
    (fun R hR=>((MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mp hR).1)
    (fun R hR=>((MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mp hR).2)

def preparationLimit (n : Nat) : Nat := n.log2+21

theorem one_work (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w : Word α) (source target : Array Bool) (R : Bounds) (hn : R.hi≤w.length) (out : State) :
    let result:=one b c e prepared (DFAIndex.build b c e w).1 w.length source target R out
    result.calls≤out.calls+span R ∧
    result.queryWork≤out.queryWork+queryLimit b c e w.length*span R ∧
    result.scanWork≤out.scanWork+6*span R ∧
    result.preparationWork≤out.preparationWork+preparationLimit w.length*span R := by
  dsimp only
  have hc:=scan_calls
    (fun s=>Text.query b c e prepared (DFAIndex.build b c e w).1
      (Text.prepareTail b c e (DFAIndex.build b c e w).1 R.hi w.length).map
      s R.hi R.period (MaskedProgression.build target R.lo (span R) (prepared.K*R.period)).counts R.lo)
    source (span R) R.lo
    {out with preparationWork:=out.preparationWork+
      (MaskedProgression.build target R.lo (span R) (prepared.K*R.period)).slots+
      (MaskedProgression.build target R.lo (span R) (prepared.K*R.period)).arithmetic+
      (Text.prepareTail b c e (DFAIndex.build b c e w).1 R.hi w.length).products+
      (Text.prepareTail b c e (DFAIndex.build b c e w).1 R.hi w.length).visits+5}
  refine ⟨hc,?_,?_,?_⟩
  · unfold one
    exact scan_query_work _ _ _ _ _ _
      (fun _ _ _=>query_work b c e prepared w _ _ R.hi R.period _ R.lo hn)
  · unfold one
    exact scan_work _ _ _ _ _
  · unfold one
    rw [scan_preparation]
    dsimp only
    have hp:=MaskedProgression.build_work target R.lo (span R) (prepared.K*R.period)
    have ht:=Text.prepareTail_bounds b c e w R.hi hn
    have hs : 1≤span R := by unfold span; omega
    have hm:=Nat.mul_le_mul_left (w.length.log2+8) hs
    simp only [Nat.mul_one] at hm
    have he : preparationLimit w.length*span R=13*span R+(w.length.log2+8)*span R := by
      unfold preparationLimit
      rw [show w.length.log2+21=13+(w.length.log2+8) by omega,Nat.add_mul]
    rw [he]
    omega

theorem runs_work (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w : Word α) (source target : Array Bool) (Rs : List Bounds)
    (hn : ∀ R,R∈Rs → R.hi≤w.length) (out : State) :
    let result:=runs b c e prepared (DFAIndex.build b c e w).1 w.length source target Rs out
    result.calls≤out.calls+totalSpan Rs ∧
    result.queryWork≤out.queryWork+queryLimit b c e w.length*totalSpan Rs ∧
    result.scanWork≤out.scanWork+6*totalSpan Rs ∧
    result.preparationWork≤out.preparationWork+preparationLimit w.length*totalSpan Rs := by
  induction Rs generalizing out with
  | nil => simp [runs,totalSpan]
  | cons R Rs ih =>
    have hh:=one_work b c e prepared w source target R (hn R List.mem_cons_self) out
    have ht:=ih (fun S hS=>hn S (List.mem_cons_of_mem R hS))
      (one b c e prepared (DFAIndex.build b c e w).1 w.length source target R out)
    dsimp only at hh ht
    dsimp only [runs,totalSpan]
    rw [Nat.mul_add,Nat.mul_add,Nat.mul_add]
    exact ⟨by omega,by omega,by omega,by omega⟩

/-- Every source call and every prefix-array cell in the actual solver
is included. This is a component-ledger theorem, retaining the existing
finite-compiler exclusions rather than a full matcher time claim. -/
theorem solve_work (b c e : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    let result:=solve b c e text fallback source target
    let mass:=6*text.size*(text.size.log2+1)
    result.output.calls≤mass ∧
    result.output.queryWork≤queryLimit b c e text.size*mass ∧
    result.output.scanWork≤6*mass ∧
    result.output.preparationWork≤text.size+1+preparationLimit text.size*mass ∧
    result.enumerationWork≤MaskedRunEnumerationCost.coefficient σ*(text.size+1)*
      ((text.size+1).log2+1)^2 ∧
    result.indexProducts=(text.size.log2+1)*text.size := by
  have hn : ∀ R,R∈(MaskedOrdered.Owner.enumerateAuto text fallback).runs → R.hi≤text.toList.length := by
    intro R hR
    simpa using ((MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mp hR).1.2.1
  have hh:=runs_work b c e (preparePattern b.stateCount c.stateCount e.stateCount)
    text.toList source target (MaskedOrdered.Owner.enumerateAuto text fallback).runs hn
    {hits:=Array.replicate (text.size+1) false,preparationWork:=text.size+1}
  have hs:=enumerated_span text fallback
  have hq:=Nat.mul_le_mul_left (queryLimit b c e text.size) hs
  have hw:=Nat.mul_le_mul_left 6 hs
  have hp:=Nat.mul_le_mul_left (preparationLimit text.size) hs
  have he:=MaskedRunEnumerationCost.enumerate_work text fallback
  have hi:=DFAIndex.build_products b c e text.toList
  simp only [Array.length_toList] at hh hi
  dsimp only [solve]
  exact ⟨by omega,by omega,by omega,by omega,he,hi⟩

end REWB.MaskedPeriodic.Batch
