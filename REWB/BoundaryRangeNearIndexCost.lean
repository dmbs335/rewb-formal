import REWB.BoundaryRangeNearIndexCorrect

/-! Factory work and query work of the eager near-boundary table. Counts
are inherited scalar/map/matrix operations, with every factory call and
every examined subset row charged. Pattern sizes are fixed; these are
not bit-operation or allocator bounds. -/
namespace REWB.BoundaryRange.NearIndex
open REWB.BoundaryApplication
variable {σ : Nat}

def rangeBudget (D : DFA (Fin σ)) (n : Nat) : Nat := D.stateCount+8*(n.log2+2)+1
def cBudget (C : DFA (Fin σ)) (n : Nat) : Nat := rangeBudget C n+TableColor.budget C+2
def dBudget (D : DFA (Fin σ)) (n : Nat) : Nat := rangeBudget D n+2

def separatedBudget (C D E : DFA (Fin σ)) (n : Nat) : Nat :=
  cBudget C n+dBudget D n+
    ((n+1).log2+2)*BoundaryIndex.Tree.queryBudget 1 E.stateCount+E.stateCount+5

def endBudget (A D E : DFA (Fin σ)) (n : Nat) : Nat :=
  dBudget D n+((n+2).log2+1)*(HeavyIndex.probeBudget A D E n+4)+7

def startBudget (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  cBudget C n+6*StartIndex.levels n+StartStep.budget B C E n+E.stateCount+12

theorem cKey_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (p : Nat) (h0p : g0≤p) (hp : p≤w.length) :
    (cKey (build A B C K D E w fallback g0 g h0g hg) p).2≤cBudget C w.length := by
  have hr:=Range.query_work C w g0 p h0p hp
  have hc:=TableColor.choose_work C (fun q=>C.final ((Range.query C (Range.build C w) g0 p).map.get q))
  change (Range.query C (Range.build C w) g0 p).work+
    (TableColor.choose C (TableColor.build C)
      (fun q=>C.final ((Range.query C (Range.build C w) g0 p).map.get q))).2+2≤_
  unfold cBudget rangeBudget
  omega

theorem dKey_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (p : Nat) (hpg : p≤g) :
    (dKey (build A B C K D E w fallback g0 g h0g hg) p).2≤dBudget D w.length := by
  have hr:=Range.query_work D w p g hpg hg
  exact Nat.add_le_add_right hr 2

theorem separated_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (p right : Nat) (h0p : g0≤p) (hpg : p≤g) :
    (separated (build A B C K D E w fallback g0 g h0g hg) p right).2≤
      separatedBudget C D E w.length := by
  let idx:=build A B C K D E w fallback g0 g h0g hg
  have hc:=cKey_work A B C K D E w fallback g0 g h0g hg p h0p (by omega)
  have hd:=dKey_work A B C K D E w fallback g0 g h0g hg p hpg
  have hq:=Separated.query_build_work A B (cVariant C (cKey idx p).1)
    (dVariant D (dKey idx p).1) E w fallback g0 g hg right
  simp only [separated,build_separated]
  unfold separatedBudget
  change (cKey idx p).2≤_ at hc
  change (dKey idx p).2≤_ at hd
  dsimp only [idx] at *
  omega

theorem fixedEnd_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (p : Nat) (hpg : p≤g) (a : Fin (w.length+1)) (right : Nat) :
    (fixedEnd (build A B C K D E w fallback g0 g h0g hg) p a right).2≤
      endBudget A D E w.length := by
  let idx:=build A B C K D E w fallback g0 g h0g hg
  have hd:=dKey_work A B C K D E w fallback g0 g h0g hg p hpg
  have hq:=(HeavyIndex.query_bound A B (dVariant D (dKey idx p).1) E w fallback g hg a right).2
  change (HeavyIndex.query A B (dVariant D (dKey idx p).1) E w
    (HeavyIndex.build A B (dVariant D (dKey idx p).1) E w fallback g hg) a right).work≤
      ((w.length+2).log2+1)*(HeavyIndex.probeBudget A D E w.length+4)+5 at hq
  simp only [fixedEnd,build_end]
  unfold endBudget
  change (dKey idx p).2≤_ at hd
  dsimp only [idx] at *
  omega

theorem fixedStart_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (p : Nat) (h0p : g0≤p) (hp : p≤w.length) (j : Fin (w.length+1))
    (h0j : g0≤j.val) (right : Nat) (hr : right≤w.length) :
    (fixedStart (build A B C K D E w fallback g0 g h0g hg) p j right).2≤
      startBudget B C E w.length := by
  let idx:=build A B C K D E w fallback g0 g h0g hg
  have hc:=cKey_work A B C K D E w fallback g0 g h0g hg p h0p hp
  have hq:=StartIndex.query_work A B (cVariant C (cKey idx p).1) E w fallback g0
    (by omega) j h0j right hr
  change (StartIndex.query B (cVariant C (cKey idx p).1) E
    (StartIndex.build A B (cVariant C (cKey idx p).1) E w fallback g0 _) j right).work≤
      6*StartIndex.levels w.length+StartStep.budget B C E w.length+E.stateCount+10 at hq
  simp only [fixedStart,build_start]
  unfold startBudget
  change (cKey idx p).2≤_ at hc
  dsimp only [idx] at *
  omega

def buildBound (A B C K D E : DFA (Fin σ)) (n : Nat) : Nat :=
  (TableColor.build C).work+
    (TableColor.count C*(D.stateCount*(Separated.bound A B C D E n+3)+4)+1)+
    (D.stateCount*(HeavyIndex.bound A B D E n+3)+1)+
    (TableColor.count C*(StartIndex.bound A B C E n+3)+1)+
    StartIndex.rangeBound C n+StartIndex.rangeBound K n+StartIndex.rangeBound D n+2*n+12

theorem build_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) :
    (build A B C K D E w fallback g0 g h0g hg).work≤buildBound A B C K D E w.length := by
  let idx:=build A B C K D E w fallback g0 g h0g hg
  have hs : idx.separated.work≤
      TableColor.count C*(D.stateCount*(Separated.bound A B C D E w.length+3)+4)+1 := by
    apply Table.build_work_le
    intro c
    apply Table.build_work_le
    intro d
    exact Separated.build_work A B (cVariant C c) (dVariant D d) E w fallback g0 g h0g hg
  have he : idx.ends.work≤D.stateCount*(HeavyIndex.bound A B D E w.length+3)+1 := by
    apply Table.build_work_le
    intro d
    exact HeavyIndex.build_work A B (dVariant D d) E w fallback g hg
  have ht : idx.starts.work≤TableColor.count C*(StartIndex.bound A B C E w.length+3)+1 := by
    apply Table.build_work_le
    intro c
    exact StartIndex.build_work A B (cVariant C c) E w fallback g0 (by omega)
  change (TableColor.build C).work+idx.separated.work+idx.ends.work+idx.starts.work+
    StartIndex.rangeBuildWork C (Range.build C w)+StartIndex.rangeBuildWork K (Range.build K w)+
    StartIndex.rangeBuildWork D (Range.build D w)+2*w.length+12≤_
  rw [StartIndex.rangeBuildWork_build,StartIndex.rangeBuildWork_build,StartIndex.rangeBuildWork_build]
  unfold buildBound
  omega

end REWB.BoundaryRange.NearIndex
