import REWB.BoundaryRangeNearIndexBorderCorrect

/-! Measured construction and same-block query work. The finite gap
compiler runs only during construction. Query costs charge actual
shared range calls, dyadic/regular AP calls, and two bounded scans. -/
namespace REWB.BoundaryRange.NearIndex.Border
open REWB.BoundaryApplication
variable {σ : Nat}

def gapBudget (C K D : DFA (Fin σ)) (n : Nat) : Nat :=
  rangeBudget C n+rangeBudget K n+rangeBudget (Automata.gap C K D C.initial K.initial) n+8

def copyBudget (A B E : DFA (Fin σ)) (n : Nat) : Nat :=
  (2*BoundaryBorder.Regular.fixedBudget A B E+521)*((n+1).log2+1)^2+
    rangeBudget A n+rangeBudget E n+8

def atBudget (A B C K D E : DFA (Fin σ)) (n : Nat) : Nat :=
  copyBudget A B E n+gapBudget C K D n+3

theorem gap_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left a j : Nat) (haj : a≤j) (hlj : left≤j) (hj : j≤w.length) :
    (gap (build A B C K D E w fallback) left a j).2≤gapBudget C K D w.length := by
  have hC : (build A B C K D E w fallback).cranges=Range.build C w := rfl
  have hK : (build A B C K D E w fallback).kranges=Range.build K w := rfl
  have hc:=Range.query_work C w a (max a left) (Nat.le_max_left _ _) (by omega)
  have hk:=Range.query_work K w left (max a left) (Nat.le_max_right _ _) (by omega)
  let c:=(Range.query C (Range.build C w) a (max a left)).map.get C.initial
  let k:=(Range.query K (Range.build K w) left (max a left)).map.get K.initial
  have hg:=NearIndex.regular_work (Automata.gap C K D c k) w (max a left) j (by omega) hj
  change (NearIndex.regular (Automata.gap C K D c k) (Range.build (Automata.gap C K D c k) w)
    (max a left) j).2≤rangeBudget (Automata.gap C K D C.initial K.initial) w.length+2 at hg
  simp only [gap,hC,hK,build_gap]
  simp only [GapCell.query,buildGap]
  change (Range.query C (Range.build C w) a (max a left)).work+
    (Range.query K (Range.build K w) left (max a left)).work+
    (NearIndex.regular (Automata.gap C K D c k) (Range.build (Automata.gap C K D c k) w)
      (max a left) j).2+6≤_
  unfold gapBudget
  unfold rangeBudget at hg ⊢
  dsimp only [c,k] at hg ⊢
  omega

theorem copy_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (a : Nat) (j : Fin (w.toArray.size+1)) (right : Nat)
    (ha : a≤w.length) (hjr : j.val≤right) (hr : right≤w.length) :
    (copy (build A B C K D E w fallback) a j right).2≤copyBudget A B E w.length := by
  have hp:=BoundaryBorder.Regular.dyadic_work_closed A B E w fallback a j right ha hr
  have ha':=NearIndex.regular_work A w 0 a (Nat.zero_le _) ha
  have he:=NearIndex.regular_work E w j.val right hjr hr
  change (BoundaryBorder.Regular.dyadic A B E (BoundaryBorder.WindowIndex.prepare w.toArray fallback)
    (Range.build A w) (Range.build B w) (Range.build E w) a j right).2+
    (NearIndex.regular A (Range.build A w) 0 a).2+
    (NearIndex.regular E (Range.build E w) j.val right).2+4≤_
  unfold copyBudget
  omega

theorem queryAt_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right a j : Nat) (haj : a≤j) (hlj : left≤j) (hjr : j≤right) (hr : right≤w.length) :
    (queryAt (build A B C K D E w fallback) left right a j).2≤atBudget A B C K D E w.length := by
  have hj : j≤(build A B C K D E w fallback).length := by change j≤w.length; omega
  have hp:=copy_work A B C K D E w fallback a ⟨j,by rw [List.size_toArray]; omega⟩ right (by omega) hjr hr
  have hg:=gap_work A B C K D E w fallback left a j haj hlj (by omega)
  unfold queryAt
  rw [dif_pos hj]
  dsimp only
  unfold atBudget
  omega

theorem row_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right g0 g a : Nat) (h0a : g0≤a) (hr : right≤w.length) :
    (row (build A B C K D E w fallback) left right g a).2≤
      (g-g0)*(atBudget A B C K D E w.length+3)+1 := by
  have hs:=NearIndex.scan_work
    (queryAt (build A B C K D E w fallback) left right a)
    (max a left) (min g (right+1)-max a left) (atBudget A B C K D E w.length)
    (by
      intro j hj he
      exact queryAt_work A B C K D E w fallback left right a j (by omega) (by omega) (by omega) hr)
  have hm:=Nat.mul_le_mul_right (atBudget A B C K D E w.length+3)
    (show min g (right+1)-max a left≤g-g0 by omega)
  change (NearIndex.scan _ _ _).2≤_
  omega

def queryBudget (A B C K D E : DFA (Fin σ)) (n span : Nat) : Nat :=
  span*(span*(atBudget A B C K D E n+3)+4)+1

theorem query_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right g0 g : Nat) (hr : right≤w.length) :
    (query (build A B C K D E w fallback) left right g0 g).2≤
      queryBudget A B C K D E w.length (g-g0) := by
  have hs:=NearIndex.scan_work
    (row (build A B C K D E w fallback) left right g) (g0+1) (g-(g0+1))
    ((g-g0)*(atBudget A B C K D E w.length+3)+1)
    (by intro a ha he; exact row_work A B C K D E w fallback left right g0 g a (by omega) hr)
  have hm:=Nat.mul_le_mul_right ((g-g0)*(atBudget A B C K D E w.length+3)+4)
    (show g-(g0+1)≤g-g0 by omega)
  change (NearIndex.scan _ _ _).2≤_
  unfold queryBudget
  simp only [Nat.add_assoc,Nat.reduceAdd] at hs
  omega

private theorem range_height (d : DFA (Fin σ)) (n : Nat) :
    rangeBudget d n≤(d.stateCount+17)*((n+1).log2+1)^2 := by
  let H:=(n+1).log2+1
  have hH : 1≤H := by dsimp [H]; omega
  have hlog:=BoundaryBorder.Dyadic.log_height n
  change n.log2+1≤H at hlog
  have hstep : n.log2+2≤2*H := by omega
  have hm:=Nat.mul_le_mul_left 8 hstep
  have hd:=Nat.mul_le_mul_left d.stateCount hH
  have h17:=Nat.mul_le_mul_left 17 hH
  have hs : rangeBudget d n≤(d.stateCount+17)*H := by
    unfold rangeBudget
    simp only [Nat.add_mul,Nat.mul_one] at *
    omega
  have hsq : H≤H^2 := by
    have hh:=Nat.mul_le_mul_right H hH
    simpa only [Nat.one_mul,Nat.pow_two] using hh
  exact Nat.le_trans hs (Nat.mul_le_mul_left _ hsq)

/-- This coefficient depends only on the six fixed automata. -/
def fixedBudget (A B C K D E : DFA (Fin σ)) : Nat :=
  2*BoundaryBorder.Regular.fixedBudget A B E+A.stateCount+E.stateCount+
    C.stateCount+K.stateCount+(Automata.gap C K D C.initial K.initial).stateCount+628

theorem atBudget_height (A B C K D E : DFA (Fin σ)) (n : Nat) :
    atBudget A B C K D E n+3≤fixedBudget A B C K D E*((n+1).log2+1)^2 := by
  have ha:=range_height A n
  have he:=range_height E n
  have hc:=range_height C n
  have hk:=range_height K n
  have hg:=range_height (Automata.gap C K D C.initial K.initial) n
  have hs : 1≤((n+1).log2+1)^2 := by
    have h : 1≤(n+1).log2+1 := by omega
    have hh:=Nat.mul_le_mul h h
    simpa only [Nat.one_mul,Nat.pow_two] using hh
  have h22:=Nat.mul_le_mul_left 22 hs
  unfold atBudget copyBudget gapBudget fixedBudget
  simp only [Nat.add_mul,Nat.mul_one] at *
  omega

theorem query_work_height (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right g0 g : Nat) (hr : right≤w.length) :
    (query (build A B C K D E w fallback) left right g0 g).2≤
      (g-g0)*((g-g0)*(fixedBudget A B C K D E*((w.length+1).log2+1)^2)+4)+1 := by
  have hq:=query_work A B C K D E w fallback left right g0 g hr
  have hi:=Nat.mul_le_mul_left (g-g0) (atBudget_height A B C K D E w.length)
  have ho:=Nat.mul_le_mul_left (g-g0) (Nat.add_le_add_right hi 4)
  unfold queryBudget at hq
  omega

def gapBuildBound (C K D : DFA (Fin σ)) (n : Nat) : Nat :=
  StartIndex.rangeBound (Automata.gap C K D C.initial K.initial) n+
    (Automata.gap C K D C.initial K.initial).stateCount+3

theorem buildGap_work (C K D : DFA (Fin σ)) (w : Word (Fin σ))
    (c : Fin C.stateCount) (k : Fin K.stateCount) :
    (buildGap C K D w c k).work=gapBuildBound C K D w.length := by
  simp only [buildGap,StartIndex.rangeBuildWork_build]
  rfl

def buildBound (A B C K D E : DFA (Fin σ)) (n : Nat) : Nat :=
  (32*(σ+2)+836)*(n+1)*((n+1).log2+1)^2+
    StartIndex.rangeBound A n+StartIndex.rangeBound B n+StartIndex.rangeBound C n+
    StartIndex.rangeBound K n+StartIndex.rangeBound E n+
    (C.stateCount*(K.stateCount*(gapBuildBound C K D n+3)+4)+1)+2*n+14

theorem build_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) :
    (build A B C K D E w fallback).work≤buildBound A B C K D E w.length := by
  let idx:=build A B C K D E w fallback
  have hc:=BoundaryBorder.WindowIndex.prepare_work_closed w.toArray fallback
  conv at hc => rhs; rw [List.size_toArray]
  have hg : idx.gaps.work≤C.stateCount*(K.stateCount*(gapBuildBound C K D w.length+3)+4)+1 := by
    apply Table.build_work_le
    intro c
    apply Table.build_work_le
    intro k
    exact Nat.le_of_eq (buildGap_work C K D w c k)
  change (BoundaryBorder.WindowIndex.prepare w.toArray fallback).work+
    StartIndex.rangeBuildWork A (Range.build A w)+StartIndex.rangeBuildWork B (Range.build B w)+
    StartIndex.rangeBuildWork C (Range.build C w)+StartIndex.rangeBuildWork K (Range.build K w)+
    StartIndex.rangeBuildWork E (Range.build E w)+idx.gaps.work+2*w.length+14≤_
  rw [StartIndex.rangeBuildWork_build,StartIndex.rangeBuildWork_build,StartIndex.rangeBuildWork_build,
    StartIndex.rangeBuildWork_build,StartIndex.rangeBuildWork_build]
  unfold buildBound
  omega

end REWB.BoundaryRange.NearIndex.Border
