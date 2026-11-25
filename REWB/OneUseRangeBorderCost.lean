import REWB.OneUseRangeBorderCorrect

/-! Actual counters for the midpoint query and its two short-block
scans. Constants depend only on the four fixed DFAs. No source-end or
capture-length scan is hidden in these bounds. -/
namespace REWB.OneUseRange.Border
open REWB.BoundaryApplication REWB.BoundaryRange
variable {σ : Nat}

def stateBudget (B C : DFA (Fin σ)) (n : Nat) : Nat :=
  (2*BoundaryBorder.Regular.fixedBudget C B C+521)*((n+1).log2+1)^2+24

def innerBudget (B C : DFA (Fin σ)) (n : Nat) : Nat :=
  C.stateCount*(stateBudget B C n+3)+NearIndex.rangeBudget C n+7

def atBudget (A B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  innerBudget B C n+NearIndex.rangeBudget A n+NearIndex.rangeBudget E n+13

def queryBudget (A B C E : DFA (Fin σ)) (n leftSpan rightSpan : Nat) : Nat :=
  leftSpan*(rightSpan*(atBudget A B C E n+3)+4)+1

theorem state_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (i : Fin (w.toArray.size+1)) (t : Nat) (hi : i.val≤t) (ht : t≤w.length)
    (q : Fin C.stateCount) :
    (state (build A B C E w fallback) i t q).2≤stateBudget B C w.length := by
  have hm:=middle_bounds i.val t hi
  have hh:=Regular.dyadic_work_closed (Automata.start C q) B (Automata.stop C q) w fallback
    (middle i.val t) t i (middle i.val t) hm.2.2 ht (by omega)
  exact Nat.add_le_add_right hh 24

theorem inner_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (i : Fin (w.toArray.size+1)) (t : Nat) (hi : i.val≤t) (ht : t≤w.length) :
    (inner (build A B C E w fallback) i t).2≤innerBudget B C w.length := by
  have hp:=any_work (state (build A B C E w fallback) i t) (List.finRange C.stateCount)
    (stateBudget B C w.length) (fun q _=>state_work A B C E w fallback i t hi ht q)
  have he:=NearIndex.regular_work C w i.val t hi ht
  rw [List.length_finRange] at hp
  change (any (state (build A B C E w fallback) i t) (List.finRange C.stateCount)).2+
    (NearIndex.regular C (Range.build C w) i.val t).2+4≤_
  unfold innerBudget
  omega

theorem queryAt_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right i t : Nat) :
    (queryAt (build A B C E w fallback) left right i t).2≤atBudget A B C E w.length := by
  unfold queryAt
  split
  · rename_i h
    have hn : (build A B C E w fallback).size=w.length := List.size_toArray
    rw [hn] at h
    have hc:=inner_work A B C E w fallback ⟨i,by rw [List.size_toArray]; omega⟩ t h.2.1 (by omega)
    have ha:=NearIndex.regular_work A w left i h.1 (by omega)
    have he:=NearIndex.regular_work E w t right h.2.2.1 h.2.2.2
    change (inner (build A B C E w fallback) ⟨i,_⟩ t).2+
      (NearIndex.regular A (Range.build A w) left i).2+
      (NearIndex.regular E (Range.build E w) t right).2+9≤_
    unfold atBudget
    omega
  · dsimp only
    unfold atBudget
    omega

theorem row_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right rightGrid i : Nat) :
    (row (build A B C E w fallback) left right rightGrid i).2≤
      (right-rightGrid)*(atBudget A B C E w.length+3)+1 := by
  apply NearIndex.scan_work
  intro t _ _
  exact queryAt_work A B C E w fallback left right i t

theorem query_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right leftGrid rightGrid : Nat) :
    (query (build A B C E w fallback) left right leftGrid rightGrid).2≤
      queryBudget A B C E w.length (leftGrid-left) (right-rightGrid) := by
  exact NearIndex.scan_work _ _ _ ((right-rightGrid)*(atBudget A B C E w.length+3)+1)
    (fun i _ _=>row_work A B C E w fallback left right rightGrid i)

def buildBound (A B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  (32*(σ+2)+836)*(n+1)*((n+1).log2+1)^2+
    StartIndex.rangeBound A n+StartIndex.rangeBound B n+StartIndex.rangeBound C n+
    StartIndex.rangeBound E n+2*n+C.stateCount+14

theorem build_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) :
    (build A B C E w fallback).work≤buildBound A B C E w.length := by
  have hc:=BoundaryBorder.WindowIndex.prepare_work_closed w.toArray fallback
  conv at hc => rhs; rw [List.size_toArray]
  change (BoundaryBorder.WindowIndex.prepare w.toArray fallback).work+
    StartIndex.rangeBuildWork A (Range.build A w)+StartIndex.rangeBuildWork B (Range.build B w)+
    StartIndex.rangeBuildWork C (Range.build C w)+StartIndex.rangeBuildWork E (Range.build E w)+
    2*w.length+C.stateCount+14≤_
  rw [StartIndex.rangeBuildWork_build,StartIndex.rangeBuildWork_build,
    StartIndex.rangeBuildWork_build,StartIndex.rangeBuildWork_build]
  unfold buildBound
  omega

private theorem range_height (d : DFA (Fin σ)) (n : Nat) :
    NearIndex.rangeBudget d n≤(d.stateCount+17)*((n+1).log2+1)^2 := by
  let H:=(n+1).log2+1
  have hp : 1≤H := by dsimp [H]; omega
  have hq : 1≤H^2 := by have hh:=Nat.mul_le_mul hp hp; simpa only [Nat.one_mul,Nat.pow_two] using hh
  have hH : H≤H^2 := by have hh:=Nat.mul_le_mul_left H hp; simpa only [Nat.mul_one,Nat.pow_two] using hh
  have hl:=BoundaryBorder.Dyadic.log_height n
  change n.log2+1≤H at hl
  have hn : n.log2+2≤2*H := by omega
  have hs:=Nat.mul_le_mul_left (d.stateCount+1) hq
  have hn8:=Nat.mul_le_mul_left 8 hn
  have h16:=Nat.mul_le_mul_left 16 hH
  change d.stateCount+8*(n.log2+2)+1≤(d.stateCount+17)*H^2
  simp only [Nat.mul_one,Nat.add_mul] at hs ⊢
  omega

def fixedBudget (A B C E : DFA (Fin σ)) : Nat :=
  C.stateCount*(2*BoundaryBorder.Regular.fixedBudget C B C+521)+
    28*C.stateCount+A.stateCount+E.stateCount+74

theorem atBudget_height (A B C E : DFA (Fin σ)) (n : Nat) :
    atBudget A B C E n+3≤fixedBudget A B C E*((n+1).log2+1)^2 := by
  let H:=(n+1).log2+1
  have hp : 1≤H := by dsimp [H]; omega
  have hq : 1≤H^2 := by have hh:=Nat.mul_le_mul hp hp; simpa only [Nat.one_mul,Nat.pow_two] using hh
  have ha:=range_height A n
  have hc:=range_height C n
  have he:=range_height E n
  have hk:=Nat.mul_le_mul_left (27*C.stateCount+23) hq
  change _≤fixedBudget A B C E*H^2
  change _≤(A.stateCount+17)*H^2 at ha
  change _≤(C.stateCount+17)*H^2 at hc
  change _≤(E.stateCount+17)*H^2 at he
  unfold atBudget innerBudget stateBudget fixedBudget
  change C.stateCount*((2*BoundaryBorder.Regular.fixedBudget C B C+521)*H^2+24+3)+
    NearIndex.rangeBudget C n+7+NearIndex.rangeBudget A n+NearIndex.rangeBudget E n+13+3≤_
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.mul_assoc] at ha hc he hk ⊢
  omega

theorem query_work_height (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right leftGrid rightGrid : Nat) :
    (query (build A B C E w fallback) left right leftGrid rightGrid).2≤
      (leftGrid-left)*((right-rightGrid)*(fixedBudget A B C E*((w.length+1).log2+1)^2)+4)+1 := by
  have h:=query_work A B C E w fallback left right leftGrid rightGrid
  have hs:=Nat.mul_le_mul_left (right-rightGrid) (atBudget_height A B C E w.length)
  have ho:=Nat.mul_le_mul_left (leftGrid-left) (Nat.add_le_add_right hs 4)
  unfold queryBudget at h
  omega

end REWB.OneUseRange.Border
