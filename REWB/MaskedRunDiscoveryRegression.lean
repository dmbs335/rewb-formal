import REWB.MaskedRunDiscoveryEvents
import REWB.MaskedRunDiscoveryLocus

/-! Regression certificates distinguish a full occurrence-class adjacency
from a temporary partial-merge adjacency, and skip equal-depth nodes. -/
namespace REWB.MaskedRunDiscovery.Regression
open REWB.Periodic REWB.RunGeometry REWB.MaskedEventBudget REWB.LCEIndex

def alternating (i : Nat) : Fin 2 := ⟨i%2,Nat.mod_lt _ (by decide)⟩

theorem full_occurrences : Complete alternating 10 0 4 [0,2,4,6] := by
  intro k
  constructor
  · intro hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> exact ⟨by decide,by decide⟩
  · intro hk
    have he:=(segment_eq_points alternating k 0 4).mp hk.2 0 (by decide)
    have hz:=congrArg Fin.val he
    simp only [alternating,Nat.add_zero,Nat.zero_mod] at hz
    have hb:=hk.1
    have hm : k=0 ∨ k=2 ∨ k=4 ∨ k=6 := by omega
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hm

theorem full_adjacent : Adjacent [0,2,4,6] 2 4 := by
  refine ⟨by decide,by decide,by decide,?_⟩
  intro k hk hleft hright
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  omega

theorem true_gap_least : LeastPeriod (shift alternating 2) 4 2 :=
  dense_least _ _ _ (by decide) (by decide)
    (complete_consecutive alternating 10 0 4 [0,2,4,6] 2 4 full_occurrences full_adjacent)

theorem found_cubic :
    ∃R,(discover (prepare alternating 10) (prepareReverse alternating 10) 10 2 4 4).1=some R ∧
      R.Valid alternating 10 ∧ R.period=2 ∧ R.lo≤2 ∧ 8≤R.hi ∧ 3*R.period≤R.hi-R.lo :=
  complete_discovery alternating 10 0 4 [0,2,4,6] 2 4 full_occurrences full_adjacent (by decide)

def left : MergeTree := .node (.leaf 0) (.leaf 4)
def right : MergeTree := .node (.leaf 2) (.leaf 6)
def program : MergeTree := .node left right

theorem actual_new_generation :
    (2,4)∈(joined left right).fresh ∧ (2,4)∈edges (build program).positions := by decide

theorem prior_children_separate : ¬Coexists left 2 4 ∧ ¬Coexists right 2 4 := by
  unfold Coexists
  decide

def constantText (_ : Nat) : Fin 1 := 0

/-- The temporary pair (0,2) omits the occurrence at 1. Its gap is not
the least period, even though it passes the numerical density guard. -/
theorem partial_pair_not_consecutive : ¬Consecutive constantText 4 2 := by
  intro h
  exact h.2 1 (by decide) (by decide) (fun _ _=>rfl)

theorem partial_gap_not_least : ¬LeastPeriod constantText 4 2 := by
  intro h
  have hh:=h.2.2 1 (by decide) (fun _ _=>rfl)
  omega

theorem equal_depth_is_skipped (F B : RankIndex.Index) :
    discoverClass F B 10 2 4 4 (some 4)=(none,2) := equal_depth_skipped F B 10 2 4 4

theorem strict_boundary_enabled : classBoundary (some 3) 4=true := by decide

end REWB.MaskedRunDiscovery.Regression
