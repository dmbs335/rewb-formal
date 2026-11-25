import REWB.BoundaryBorderRegularOrbit

/-! Counted construction and existential solving of the actual two-orbit
formula. No mask is needed: the formula already bounds the candidate
exponent. Literal values change with text endpoints, while every list
and affine traversal is bounded by the two fixed state dimensions. -/
namespace REWB.BoundaryBorder.Regular.Counted
open REWB.FiniteOrbit REWB.MaskedPeriodic REWB.MaskedCluster
open REWB.AffineProjection REWB.PhaseSolver REWB.UniformProjection
variable {m n : Nat}

def descriptor (D : Descriptor) (t : Aff) : Formula×Nat :=
  let initial:=filter (fun k=>(decide (k<D.threshold),1)) D.initialCounts
  let a:=CountedProjection.map (fun k=>(exactCount t k,10)) initial.1
  let b:=CountedProjection.map (fun r=>(progression t (D.threshold+r) D.period,11)) D.residues
  let out:=CountedProjection.append a.1 b.1
  (out.1,initial.2+a.2+b.2+out.2+1)

theorem descriptor_value (D : Descriptor) (t : Aff) :
    (descriptor D t).1=descriptorFormula D t := by
  simp only [descriptor,filter_value,CountedProjection.append_value,CountedProjection.map_value,
    descriptorFormula]

theorem descriptor_work (D : Descriptor) (t : Aff) :
    (descriptor D t).2≤20*(D.initialCounts.length+D.residues.length)+10 := by
  have hf:=filter_work (fun k=>(decide (k<D.threshold),1)) D.initialCounts 1
    (fun _ _=>Nat.le_refl _)
  have hl:=List.length_filter_le (fun k=>decide (k<D.threshold)) D.initialCounts
  simp only [descriptor,CountedProjection.append_steps,CountedProjection.map_plain_steps,
    CountedProjection.map_value,List.length_map,filter_value]
  omega

def formula (o : Orbit m) (t : Aff) : Formula×Nat :=
  let d:=compress o
  let out:=descriptor d.1 t
  (out.1,d.2+out.2+1)

theorem formula_value (o : Orbit m) (t : Aff) : (formula o t).1=o.data.formula t := by
  simp only [formula,descriptor_value,compress_value,OrbitData.formula]

theorem formula_work (o : Orbit m) (t : Aff) :
    (formula o t).2≤orbitBudget m+20*m+11 := by
  have hc:=compress_work o
  have hd:=descriptor_work (compress o).1 t
  rw [compress_value] at hd
  have hs:=o.data.descriptor_spec.2.2.1
  simp only [formula,compress_value]
  omega

def both (F G : Formula) : Formula×Nat :=
  CountedProjection.flatMap
    (fun C=>CountedProjection.map (fun D=>CountedProjection.append C D) G) F

theorem both_value (F G : Formula) : (both F G).1=PhaseSolver.both F G := by
  simp only [both,CountedProjection.flatMap_value,CountedProjection.map_value,
    CountedProjection.append_value,PhaseSolver.both]

theorem both_work (F G : Formula) (c : Nat) (hc : ∀C,C∈F→C.length≤c) :
    (both F G).2≤F.length*(G.length*(c+3)+3)+1 := by
  induction F with
  | nil => simp [both,CountedProjection.flatMap]
  | cons C F ih =>
    have hh:=hc C List.mem_cons_self
    have ht:=ih (fun D hD=>hc D (List.mem_cons_of_mem _ hD))
    have hm:=CountedProjection.map_steps_constant (fun D=>CountedProjection.append C D)
      G (C.length+1) (fun _ _=>CountedProjection.append_steps _ _)
    have hl : (CountedProjection.map (fun D=>CountedProjection.append C D) G).1.length=G.length := by
      rw [CountedProjection.map_value,List.length_map]
    have hb:=Nat.mul_le_mul_left G.length (show C.length+1+1≤c+2 by omega)
    have he : G.length*(c+2)+G.length=G.length*(c+3) := by
      simp only [Nat.mul_add]
      omega
    change (CountedProjection.map (fun D=>CountedProjection.append C D) G).2+
      (both F G).2+(CountedProjection.append
        (CountedProjection.map (fun D=>CountedProjection.append C D) G).1 (both F G).1).2+1≤_
    rw [hm,CountedProjection.append_steps,hl]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem descriptor_conj (D : Descriptor) (t : Aff) (C : Conj) (hc : C∈descriptorFormula D t) :
    C.length=2 := by
  rcases List.mem_append.mp hc with ha|hb
  · obtain ⟨k,_,rfl⟩:=List.mem_map.mp ha
    rfl
  · obtain ⟨r,_,rfl⟩:=List.mem_map.mp hb
    rfl

def pair (before : Orbit m) (after : Orbit n) (lo hi : Nat) : Formula×Nat :=
  let a:=formula before (leftExpr lo)
  let b:=formula after (rightExpr hi)
  let orbits:=both a.1 b.1
  let out:=both (MaskedCluster.bounds lo hi) orbits.1
  (out.1,a.2+b.2+orbits.2+out.2+25)

theorem pair_value (before : Orbit m) (after : Orbit n) (lo hi : Nat) :
    (pair before after lo hi).1=pairFormula before.data after.data lo hi := by
  simp only [pair,both_value,formula_value,pairFormula]

def pairBudget (m n : Nat) : Nat :=
  orbitBudget m+orbitBudget n+20*m+20*n+m*(n*5+3)+(m*n)*5+52

theorem pair_work (before : Orbit m) (after : Orbit n) (lo hi : Nat) :
    (pair before after lo hi).2≤pairBudget m n := by
  let F:=(formula before (leftExpr lo)).1
  let G:=(formula after (rightExpr hi)).1
  have ha:=formula_work before (leftExpr lo)
  have hb:=formula_work after (rightExpr hi)
  have hla : F.length≤m := by
    dsimp only [F]
    rw [formula_value]
    exact orbitFormula_length before.data _
  have hlb : G.length≤n := by
    dsimp only [G]
    rw [formula_value]
    exact orbitFormula_length after.data _
  have hc:=both_work F G 2 (by
    intro C hC
    dsimp only [F] at hC
    rw [formula_value] at hC
    exact Nat.le_of_eq (descriptor_conj _ _ C hC))
  change (both F G).2≤F.length*(G.length*5+3)+1 at hc
  have hm:=Nat.mul_le_mul hla (Nat.add_le_add_right (Nat.mul_le_mul_right 5 hlb) 3)
  have hlen : (both F G).1.length≤m*n := by
    rw [both_value,MaskedCluster.both_length]
    exact Nat.mul_le_mul hla hlb
  have hd:=both_work (MaskedCluster.bounds lo hi) (both F G).1 2 (by
    intro C hC
    have he : C=[.le ((Aff.lit lo).sub (.var 0)),.le ((Aff.var 0).sub (.lit hi))] :=
      List.mem_singleton.mp hC
    rw [he]
    exact Nat.le_refl _)
  have hbl : (MaskedCluster.bounds lo hi).length=1 := rfl
  rw [hbl,Nat.one_mul] at hd
  change (both (MaskedCluster.bounds lo hi) (both F G).1).2≤(both F G).1.length*5+4 at hd
  have hp:=Nat.mul_le_mul_right 5 hlen
  change (formula before (leftExpr lo)).2+(formula after (rightExpr hi)).2+
    (both F G).2+(both (MaskedCluster.bounds lo hi) (both F G).1).2+25≤_
  unfold pairBudget
  omega

def family (m n : Nat) : Family :=
  combine [LiteralShape.formula (MaskedCluster.bounds 0 0)]
    (combine (descriptors m (LiteralShape.aff (leftExpr 0)))
      (descriptors n (LiteralShape.aff (rightExpr 0))))

theorem pair_covered (before : Orbit m) (after : Orbit n) (lo hi : Nat) :
    Covered (pairFormula before.data after.data lo hi) (family m n) := by
  unfold pairFormula family
  apply covered_both
  · exact List.mem_cons_self
  · apply covered_both
    · exact before.data.formula_covered (leftExpr lo)
    · exact after.data.formula_covered (rightExpr hi)

theorem pair_good (before : Orbit m) (after : Orbit n) (lo hi : Nat) :
    FormulaGood (pairFormula before.data after.data lo hi) := by
  apply both_good
  · exact both_good _ _ (le_good _ _) (le_good _ _)
  · exact both_good _ _ (before.data.formula_good _) (after.data.formula_good _)

def solve (before : Orbit m) (after : Orbit n) (lo hi : Nat) : Bool×Nat :=
  let F:=pair before after lo hi
  let out:=CountedProjection.solve 1 F.1 []
  (out.1,F.2+out.2+1)

theorem solve_correct (before : Orbit m) (after : Orbit n) (lo hi : Nat) :
    (solve before after lo hi).1=true ↔∃k,PairAccepts before.data after.data lo hi k := by
  simp only [solve,pair_value,CountedProjection.solve_value]
  rw [AffineProjection.solve_correct 1 _ [] (pair_good before after lo hi)]
  change (∃x : Int,Satisfies (pairFormula before.data after.data lo hi) [x])↔_
  constructor
  · rintro ⟨x,hx⟩
    have hb:=(both_correct _ _ _).mp hx |>.1
    have hl:=(both_correct _ _ _).mp hb |>.1
    have hn : (lo:Int)≤x := by
      simpa only [le_correct,Aff.eval,List.getElem?_cons_zero,Option.getD_some] using hl
    have he : (x.toNat:Int)=x := Int.toNat_of_nonneg (by omega)
    refine ⟨x.toNat,(pairFormula_correct before.data after.data lo hi x.toNat).mp ?_⟩
    simpa only [he] using hx
  · rintro ⟨k,hk⟩
    exact ⟨(k:Int),(pairFormula_correct before.data after.data lo hi k).mpr hk⟩

def solveBudget (m n : Nat) : Nat := pairBudget m n+CountedProjection.stepsBudget 1 0 (family m n)+1

theorem solve_work (before : Orbit m) (after : Orbit n) (lo hi : Nat) :
    (solve before after lo hi).2≤solveBudget m n := by
  have hp:=pair_work before after lo hi
  have hs:=CountedProjection.solve_uniform_steps 1 (pairFormula before.data after.data lo hi)
    (family m n) [] (pair_covered before after lo hi)
  simp only [solve,pair_value,solveBudget]
  exact Nat.add_le_add_right (Nat.add_le_add hp hs) 1

end REWB.BoundaryBorder.Regular.Counted
