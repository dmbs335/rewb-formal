import REWB.IndexedGlobalCoverage

/-! Packing for distinct maximal equality strips. The lists of equality
cells below are specifications used only in proofs. The executable
schedule never enumerates these cells or scans a strip's characters. -/
namespace REWB.ResidualStripSchedule
open REWB.IndexedGrid REWB.GlobalCoverage
variable {α : Type}

def span (R : Strip) : Nat := R.hi-R.lo

def totalSpan : List Strip→Nat
  | [] => 0
  | R::Rs => span R+totalSpan Rs

def cells (R : Strip) : List (Nat×Nat) := RunBudget.starts R.lo R.distance (span R)

def allCells : List Strip→List (Nat×Nat)
  | [] => []
  | R::Rs => cells R++allCells Rs

theorem cells_length (R : Strip) : (cells R).length=span R :=
  RunBudget.starts_length _ _ _

theorem cells_mem (R : Strip) (x : Nat×Nat) :
    x∈cells R ↔ R.lo≤x.1 ∧ x.1<R.hi ∧ x.2=R.distance := by
  rw [cells,RunBudget.starts_mem]
  simp only [span]
  omega

theorem allCells_length (Rs : List Strip) : (allCells Rs).length=totalSpan Rs := by
  induction Rs with
  | nil => rfl
  | cons R Rs ih => rw [allCells,List.length_append,cells_length,ih,totalSpan]

theorem allCells_mem (Rs : List Strip) (x : Nat×Nat) :
    x∈allCells Rs ↔ ∃R,R∈Rs ∧ x∈cells R := by
  induction Rs with
  | nil => simp [allCells]
  | cons R Rs ih =>
    simp only [allCells,List.mem_append,ih,List.mem_cons]
    constructor
    · rintro (hx|⟨S,hS,hx⟩)
      · exact ⟨R,Or.inl rfl,hx⟩
      · exact ⟨S,Or.inr hS,hx⟩
    · rintro ⟨S,(he|hS),hx⟩
      · subst S; exact Or.inl hx
      · exact Or.inr ⟨S,hS,hx⟩

theorem eq_of_shared_cell (f : Nat→α) (n : Nat) (R S : Strip)
    (hR : MaximalStrip f n R.lo R.hi R.distance)
    (hS : MaximalStrip f n S.lo S.hi S.distance)
    (x : Nat×Nat) (hxR : x∈cells R) (hxS : x∈cells S) : R=S := by
  obtain ⟨ha,hb,hq⟩:=(cells_mem R x).mp hxR
  obtain ⟨hc,hd,hq'⟩:=(cells_mem S x).mp hxS
  have he : R.distance=S.distance := hq.symm.trans hq'
  rw [←he] at hS
  obtain ⟨hl,hr⟩:=IndexedGlobalCoverage.strip_unique f n R.lo R.hi S.lo S.hi R.distance x.1
    hR hS ha hb hc hd
  cases R
  cases S
  simp_all only [Strip.mk.injEq]

theorem allCells_nodup (f : Nat→α) (n : Nat) (Rs : List Strip)
    (hv : ∀R,R∈Rs→MaximalStrip f n R.lo R.hi R.distance) (hn : Rs.Nodup) :
    (allCells Rs).Nodup := by
  induction Rs with
  | nil => exact List.nodup_nil
  | cons R Rs ih =>
    obtain ⟨hf,ht⟩:=List.nodup_cons.mp hn
    change (cells R++allCells Rs).Pairwise (·≠·)
    apply List.pairwise_append.mpr
    refine ⟨RunBudget.starts_nodup _ _ _,ih (fun S hS=>hv S (List.mem_cons_of_mem R hS)) ht,?_⟩
    intro x hx y hy he
    subst y
    obtain ⟨S,hS,hxS⟩:=(allCells_mem Rs x).mp hy
    have hRS:=eq_of_shared_cell f n R S (hv R List.mem_cons_self)
      (hv S (List.mem_cons_of_mem R hS)) x hx hxS
    exact hf (hRS.symm ▸ hS)

private theorem subset_length (xs ys : List (Nat×Nat)) (hd : xs.Nodup)
    (hs : ∀x,x∈xs→x∈ys) : xs.length≤ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hf,ht⟩:=List.nodup_cons.mp hd
    have hx:=hs x List.mem_cons_self
    have hh:=ih (ys.erase x) ht (fun y hy=>
      (List.mem_erase_of_ne (show y≠x from fun he=>hf (he ▸ hy))).mpr
        (hs y (List.mem_cons_of_mem x hy)))
    rw [List.length_erase_of_mem hx] at hh
    simp only [List.length_cons]
    have hp : 0<ys.length := List.length_pos_iff.mpr (by intro he; simp only [he,List.not_mem_nil] at hx)
    omega

private def square (n : Nat) : List (Nat×Nat) :=
  (List.range n).flatMap (fun i=>(List.range n).map (fun d=>(i,d)))

private theorem square_length (n : Nat) : (square n).length=n*n := by
  have aux : ∀xs : List Nat,
      (xs.flatMap (fun i=>(List.range n).map (fun d=>(i,d)))).length=xs.length*n := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.flatMap_cons,List.length_append,List.length_map,
        List.length_range,ih,List.length_cons,Nat.add_mul,Nat.one_mul]; omega
  rw [square,aux,List.length_range]

private theorem square_mem (n : Nat) (x : Nat×Nat) :
    x∈square n ↔ x.1<n ∧ x.2<n := by
  simp only [square,List.mem_flatMap,List.mem_range,List.mem_map]
  constructor
  · rintro ⟨i,hi,d,hd,he⟩
    cases he
    exact ⟨hi,hd⟩
  · rintro ⟨hi,hd⟩
    exact ⟨x.1,hi,x.2,hd,Prod.eta x⟩

/-- Distinct maximal strips occupy disjoint (position, displacement)
cells, even when strips of different displacements overlap in text. -/
theorem totalSpan_bound (f : Nat→α) (n : Nat) (Rs : List Strip)
    (hv : ∀R,R∈Rs→MaximalStrip f n R.lo R.hi R.distance) (hn : Rs.Nodup) :
    totalSpan Rs≤n^2 := by
  have hh:=subset_length (allCells Rs) (square n) (allCells_nodup f n Rs hv hn) (by
    intro x hx
    obtain ⟨R,hR,hx⟩:=(allCells_mem Rs x).mp hx
    obtain ⟨ha,hb,hq⟩:=(cells_mem R x).mp hx
    obtain ⟨hd,hlr,hrn,_⟩:=hv R hR
    apply (square_mem n x).mpr
    omega)
  simpa only [allCells_length,square_length,Nat.pow_two] using hh

theorem long_mass (L : Nat) (Rs : List Strip) (hl : ∀R,R∈Rs→L≤span R) :
    L*Rs.length≤totalSpan Rs := by
  induction Rs with
  | nil => simp [totalSpan]
  | cons R Rs ih =>
    have ha:=hl R List.mem_cons_self
    have hb:=ih (fun S hS=>hl S (List.mem_cons_of_mem R hS))
    simp only [List.length_cons,Nat.mul_succ,totalSpan]
    omega

theorem long_count (f : Nat→α) (n L : Nat) (Rs : List Strip) (hL : 0<L)
    (hv : ∀R,R∈Rs→MaximalStrip f n R.lo R.hi R.distance) (hn : Rs.Nodup)
    (hl : ∀R,R∈Rs→L≤span R) : Rs.length≤n^2/L := by
  apply (Nat.le_div_iff_mul_le hL).mpr
  rw [Nat.mul_comm]
  exact Nat.le_trans (long_mass L Rs hl) (totalSpan_bound f n Rs hv hn)

end REWB.ResidualStripSchedule
