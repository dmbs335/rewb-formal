import REWB.MaskedProgressionAP

/-! Semantic reference and executable regressions for the immutable-mask
    progression index.  The reference enumerates k and is used only in
    proofs/tests. The production query calls no reference enumerator. -/
namespace REWB.MaskedProgression.Regression

def direct (mask : Array Bool) (base len q K s lo hi r : Nat) : Bool :=
  (List.range (hi+1)).any fun k =>
    decide (lo≤k ∧ k%K=r ∧ base≤s+k*q ∧ s+k*q<base+len) &&
      readMask mask (s+k*q)

theorem direct_correct (mask : Array Bool) (base len q K s lo hi r : Nat) :
    direct mask base len q K s lo hi r=true ↔
      ∃ k, lo≤k ∧ k≤hi ∧ k%K=r ∧ base≤s+k*q ∧ s+k*q<base+len ∧
        readMask mask (s+k*q)=true := by
  simp only [direct,List.any_eq_true,List.mem_range,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨k,hhi,⟨hlo,hmod,hbase,hbound⟩,hm⟩
    exact ⟨k,hlo,by omega,hmod,hbase,hbound,hm⟩
  · rintro ⟨k,hlo,hhi,hmod,hbase,hbound,hm⟩
    exact ⟨k,by omega,⟨hlo,hmod,hbase,hbound⟩,hm⟩

theorem ap_eq_direct (mask : Array Bool) (base len q K s lo hi r : Nat)
    (hq : 0<q) (hK : 0<K) :
    (ap (build mask base len (K*q)).counts base q K s lo hi r).answer=
      direct mask base len q K s lo hi r := by
  apply Bool.eq_iff_iff.mpr
  rw [ap_build_correct mask base len q K s lo hi r hq hK,direct_correct]

/-- Marked locations are 1,4,6,10,12,15. In particular this mask is not
    q-periodic for the q=2 and q=3 regression queries. -/
def arbitraryMask : Array Bool :=
  #[false,true,false,false,true,false,true,false,false,false,true,false,true,false,false,true,false]

def exampleBuild := build arbitraryMask 3 11 6

theorem example_counts :
    exampleBuild.counts=#[0,1,0,1,0,0,0,2,0,2,0] ∧
    exampleBuild.slots=38 ∧ exampleBuild.arithmetic=93 := by decide

def exampleQuery := ap exampleBuild.counts 3 2 3 0 0 8 2
def subtractQuery := ap exampleBuild.counts 3 2 3 0 3 8 2
def unmarkedQuery := ap exampleBuild.counts 3 2 3 0 0 8 1

theorem example_queries :
    exampleQuery.answer=true ∧ exampleQuery.slots=1 ∧ exampleQuery.arithmetic=36 ∧
    subtractQuery.answer=true ∧ subtractQuery.slots=2 ∧ subtractQuery.arithmetic=37 ∧
    unmarkedQuery.answer=false ∧ unmarkedQuery.slots=1 ∧ unmarkedQuery.arithmetic=36 := by
  decide

theorem endpoint_and_empty_queries :
    (ap exampleBuild.counts 3 2 3 0 2 2 2).answer=true ∧
    (ap exampleBuild.counts 3 2 3 0 7 7 1).answer=false ∧
    (ap exampleBuild.counts 3 2 3 0 3 4 2).answer=false ∧
    (ap exampleBuild.counts 3 2 3 0 10 2 2).answer=false ∧
    (ap exampleBuild.counts 3 2 3 20 0 10 0).answer=false ∧
    (ap exampleBuild.counts 3 2 3 0 0 8 3).answer=false ∧
    (ap #[] 3 2 3 0 0 8 2).answer=false ∧
    (ap exampleBuild.counts 3 0 3 0 0 8 2).answer=false ∧
    (ap exampleBuild.counts 3 2 0 0 0 8 0).answer=false := by decide

theorem large_step_and_outer_window :
    (build arbitraryMask 3 4 25).counts=#[0,1,0,1] ∧
    (build arbitraryMask 3 4 25).slots=12 ∧
    (ap (build arbitraryMask 3 4 25).counts 3 5 5 4 0 7 0).answer=true ∧
    (ap (build arbitraryMask 14 10 2).counts 14 2 1 0 0 20 0).answer=false ∧
    (ap (build arbitraryMask 14 10 1).counts 14 1 1 0 0 20 0).answer=true := by decide

end REWB.MaskedProgression.Regression
