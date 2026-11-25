import REWB.MaskedCutDFA
import REWB.MaskedCutRotations

/-! Executable constrained joint tuples.  The C component continues to
the period end, while E stops at the run-end residue.  Both suffixes and
the B prefix retain one common cut.  The implementation obtains the tail
transformation from a range query on the shared index, without copying or
scanning that tail for each phase.
-/
namespace REWB.MaskedCut.DFAIndex
open REWB.FiniteRelation
open REWB.RangeProducts (product)
open REWB.MaskedFiniteAction.Maps
open REWB.Spec (slice)
variable {α : Type}

structure ConstrainedOutput (b c e : DFA α) where
  cuts : MatrixTable.Matrix (jointEnum b c e)
  tail : Joint b c e

def ConstrainedOutput.contains (b c e : DFA α) (out : ConstrainedOutput b c e)
    (target : Joint b c e) : Bool :=
  any (jointEnum b c e) (fun p=>any (jointEnum b c e) (fun s=>
    MatrixTable.denote out.cuts p s && decide (constrained b c e p s out.tail=target)))

theorem ConstrainedOutput.contains_true (b c e : DFA α) (out : ConstrainedOutput b c e)
    (target : Joint b c e) :
    out.contains b c e target=true ↔ ∃ p s,
      MatrixTable.denote out.cuts p s=true ∧ constrained b c e p s out.tail=target := by
  simp only [ConstrainedOutput.contains,any_true,Bool.and_eq_true,decide_eq_true_eq]

structure ConstrainedResult (b c e : DFA α) where
  answer : Option (ConstrainedOutput b c e)
  products : Nat
  visits : Nat

def queryConstrained (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start lower eta q : Nat) : ConstrainedResult b c e :=
  if lower≤eta then
    let cuts := Index.query (jointOps b c e) (jointEnum b c e) idx
      start (start+lower) (start+eta) (start+eta)
    let tail := DyadicIndex.query (ops (jointOps b c e) (jointEnum b c e)) idx
      (start+eta) (start+q)
    ⟨cuts.answer.bind (fun cuts=>tail.answer.map (fun tail=>⟨cuts,tail.total⟩)),
      cuts.products+tail.products,cuts.visits+tail.visits⟩
  else ⟨none,0,0⟩

theorem queryConstrained_value (b c e : DFA α) (w : Word α)
    (start lower eta q : Nat) (hl : lower≤eta) (he : eta≤q) (hn : start+q≤w.length) :
    (queryConstrained b c e (build b c e w).1 start lower eta q).answer=some
      ⟨Index.window (jointOps b c e) (jointEnum b c e)
        (trace (jointOps b c e) (jointEnum b c e) (letters b c e (slice w start (start+lower))))
        (trace (jointOps b c e) (jointEnum b c e) (letters b c e (slice w (start+lower) (start+eta))))
        (trace (jointOps b c e) (jointEnum b c e) (letters b c e (slice w (start+eta) (start+eta)))),
       jointWord b c e (slice w (start+eta) (start+q))⟩ := by
  have hn' : start+q≤(letters b c e w).length := by simpa only [letters_length] using hn
  simp only [queryConstrained,hl,if_true,build]
  rw [Index.query_value (jointOps b c e) (jointEnum b c e) (letters b c e w)
    start (start+lower) (start+eta) (start+eta) (by omega) (by omega) (Nat.le_refl _) (by omega),
    Index.range_value (jointOps b c e) (jointEnum b c e) (letters b c e w)
      (start+eta) (start+q) (by omega) hn']
  simp only [Option.bind,Option.map,trace_total,letters_slice,letters_product]

theorem queryConstrained_correct (b c e : DFA α) (w : Word α)
    (start lower eta q : Nat) (he : eta≤q) (hn : start+q≤w.length) (target : Joint b c e) :
    (queryConstrained b c e (build b c e w).1 start lower eta q).answer.map
      (fun out=>out.contains b c e target)=some true ↔
        ∃ rho,lower≤rho ∧ rho≤eta ∧
          (wordMap b (slice w start (start+rho)),
           wordMap c (slice w (start+rho) (start+q)),
           wordMap e (slice w (start+rho) (start+eta)))=target := by
  by_cases hl : lower≤eta
  · have cut (p s : Joint b c e) :=
      query_correct b c e w start (start+lower) (start+eta) (start+eta) p s
        (by omega) (by omega) (Nat.le_refl _) (by omega)
    have hn' : start+q≤(letters b c e w).length := by simpa only [letters_length] using hn
    have cutValue := Index.query_value (jointOps b c e) (jointEnum b c e) (letters b c e w)
      start (start+lower) (start+eta) (start+eta) (by omega) (by omega) (Nat.le_refl _) (by omega)
    simp only [letters_slice] at cutValue
    simp only [build,cutValue,Option.map,Option.some.injEq] at cut
    rw [queryConstrained_value b c e w start lower eta q hl he hn]
    simp only [Option.map,Option.some.injEq,ConstrainedOutput.contains_true,cut]
    constructor
    · rintro ⟨p,s,⟨i,hi,hj,hp,hs⟩,ht⟩
      subst p
      subst s
      rw [constrained_exact b c e w start i (start+eta) (start+q) hj (by omega)] at ht
      have hsi : start≤i := by omega
      exact ⟨i-start,by omega,by omega,by simpa only [Nat.add_sub_of_le hsi] using ht⟩
    · rintro ⟨rho,hlr,hr,ht⟩
      refine ⟨jointWord b c e (slice w start (start+rho)),
        jointWord b c e (slice w (start+rho) (start+eta)),
        ⟨start+rho,by omega,by omega,rfl,rfl⟩,?_⟩
      rw [constrained_exact b c e w start (start+rho) (start+eta) (start+q) (by omega) (by omega)]
      exact ht
  · simp only [queryConstrained,hl,if_false,Option.map]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨rho,hlo,hhi,_⟩
      omega

theorem queryConstrained_bounds (b c e : DFA α) (w : Word α)
    (start lower eta q : Nat) (he : eta≤q) (hn : start+q≤w.length) :
    (queryConstrained b c e (build b c e w).1 start lower eta q).products≤4 ∧
    (queryConstrained b c e (build b c e w).1 start lower eta q).visits≤4*(Nat.log2 w.length+2) := by
  by_cases hl : lower≤eta
  · have hn' : start+q≤(letters b c e w).length := by simpa only [letters_length] using hn
    have hc := Index.query_bounds (jointOps b c e) (jointEnum b c e) (letters b c e w)
      start (start+lower) (start+eta) (start+eta) (by omega) (by omega) (Nat.le_refl _) (by omega)
    have ht := Index.range_bounds (jointOps b c e) (jointEnum b c e) (letters b c e w)
      (start+eta) (start+q) (by omega) hn'
    simp only [letters_length] at hc ht
    simp only [queryConstrained,hl,if_true,build]
    constructor <;> omega
  · simp only [queryConstrained,hl,if_false,Nat.zero_le,and_self]

/-- A fully materialized tuple list has pattern-only length.  It is a
filter of the fixed transformation universe, not of text cut positions. -/
def ConstrainedOutput.tuples (b c e : DFA α) (out : ConstrainedOutput b c e) :
    Array (Joint b c e) :=
  ((jointEnum b c e).elems.filter (out.contains b c e)).toArray

theorem ConstrainedOutput.tuples_mem (b c e : DFA α) (out : ConstrainedOutput b c e)
    (target : Joint b c e) : target∈(out.tuples b c e).toList ↔ out.contains b c e target=true := by
  simp only [ConstrainedOutput.tuples,List.toList_toArray,List.mem_filter]
  exact and_iff_right ((jointEnum b c e).complete target)

theorem ConstrainedOutput.tuples_size (b c e : DFA α) (out : ConstrainedOutput b c e) :
    (out.tuples b c e).size≤
      b.stateCount^b.stateCount*(c.stateCount^c.stateCount*e.stateCount^e.stateCount) := by
  rw [← jointEnum_length]
  exact List.length_filter_le _ _

end REWB.MaskedCut.DFAIndex
