import REWB.ResidualDispatchQueries

/-! Bounds for the actual residual list and its construction. The query
count is ready to multiply by the finite G-state universe. DFA index
preparation and executing P1Query/P2Query remain separate obligations. -/
namespace REWB.ResidualDispatch
variable {σ : Nat}

def runMassBudget (n : Nat) : Nat := 2*n*DyadicIndex.heightFor n
def stripBudget (n L D : Nat) : Nat := (2*n^2)/D+3*(n^2/L)
def lowBudget (n D : Nat) : Nat := (D+1)*runMassBudget n
def largeBudget (n Q : Nat) : Nat := (3*n*runMassBudget n)/(Q+1)
def selectorBudget (n L D Q : Nat) : Nat := stripBudget n L D+lowBudget n D+largeBudget n Q

theorem prepare_selectors (f : Nat→Fin σ) (n s L D Q : Nat) (hD : 0<D) (hL : 0<L) :
    (prepare f n s L D Q).selectors≤selectorBudget n L D Q := by
  have hs:=ResidualStripSchedule.prepare_queries f n s L D hD hL
  have hl:=RankIndexSchedule.low_bound f n s D
  have hg:=RankIndexSchedule.large_bound f n s Q
  have hls:=(select_counts (lowRows D (RankIndexSchedule.generate f n s).runs).1).2.1
  have hgs:=(select_counts (largeRows Q (RankIndexSchedule.generate f n s).runs).1).2.1
  have hlowlen : (lowRows D (RankIndexSchedule.generate f n s).runs).1.length=
      (RankIndexSchedule.low f n s D).length := by rw [lowRows_value,List.length_map]; rfl
  have hlargelen : (largeRows Q (RankIndexSchedule.generate f n s).runs).1.length=
      (RankIndexSchedule.large f n s Q).length := by rw [largeRows_value]; rfl
  rw [hlowlen] at hls
  rw [hlargelen] at hgs
  change (ResidualStripSchedule.prepare f n s L D).batch.queries+
    (select (lowRows D (RankIndexSchedule.generate f n s).runs).1).count+
    (select (largeRows Q (RankIndexSchedule.generate f n s).runs).1).count≤_
  simp only [selectorBudget,stripBudget,lowBudget,largeBudget,runMassBudget]
  omega

theorem prepare_windows (f : Nat→Fin σ) (n s L D Q : Nat) (hD : 0<D) (hL : 0<L) :
    (prepare f n s L D Q).windows.length≤selectorBudget n L D Q := by
  rw [←prepare_count]
  exact prepare_selectors f n s L D Q hD hL

def selectorWorkBudget (n L D Q : Nat) : Nat :=
  5*stripBudget n L D+31*lowBudget n D+34*largeBudget n Q+12*runMassBudget n+15

theorem prepare_selectorWork (f : Nat→Fin σ) (n s L D Q : Nat) (hD : 0<D) (hL : 0<L) :
    (prepare f n s L D Q).selectorWork≤selectorWorkBudget n L D Q := by
  have hc:=compile_selector_work D Q (ResidualStripSchedule.prepare f n s L D) (RankIndexSchedule.generate f n s)
  have hs:=ResidualStripSchedule.prepare_length f n s L D hD hL
  have hl:=RankIndexSchedule.low_bound f n s D
  have hg:=RankIndexSchedule.large_bound f n s Q
  have hr:=RankIndexSchedule.generate_length f n s
  rw [largeRows_value] at hc
  change _≤5*(ResidualStripSchedule.prepare f n s L D).batch.jobs.length+
    31*(RankIndexSchedule.low f n s D).length+34*(RankIndexSchedule.large f n s Q).length+
    12*(RankIndexSchedule.generate f n s).runs.length+15 at hc
  change (compile D Q (ResidualStripSchedule.prepare f n s L D) (RankIndexSchedule.generate f n s)).selectorWork≤_
  simp only [selectorWorkBudget,stripBudget,lowBudget,largeBudget,runMassBudget]
  omega

def runPreparationBudget (σ n s : Nat) : Nat :=
  2*((n+1)*((n.log2+1)*(16*RankIndex.width σ n+4)+1))+
  3*(n*(n.log2+1))+
  (n/s+1)*((26*(n.log2+1)+2)*(n+1))+
  (n/s+1)*((n*(n.log2+1))*(13*(n.log2+1)+6))+
  (26*((n+1).log2+1)+5)*((n/s+1)*(n+1))+
  6*((n/s+1)*(n+1))

theorem runWork_bound (f : Nat→Fin σ) (n s : Nat) :
    runWork (RankIndexSchedule.generate f n s)≤runPreparationBudget σ n s := by
  have hh:=RankIndexSchedule.generate_counts f n s
  simp only [runWork,runPreparationBudget]
  rw [hh.1]
  omega

def preparationBudget (σ n s L D Q : Nat) : Nat :=
  ResidualStripSchedule.scheduleBudget σ n s L D+runPreparationBudget σ n s+selectorWorkBudget n L D Q+5

theorem prepare_work (f : Nat→Fin σ) (n s L D Q : Nat) (hD : 0<D) (hL : 0<L) :
    (prepare f n s L D Q).work≤preparationBudget σ n s L D Q := by
  have hs:=ResidualStripSchedule.prepare_work f n s L D hD hL
  have hr:=runWork_bound f n s
  have hc:=prepare_selectorWork f n s L D Q hD hL
  change (ResidualStripSchedule.prepare f n s L D).work+runWork (RankIndexSchedule.generate f n s)+
    (prepare f n s L D Q).selectorWork+5≤_
  simp only [preparationBudget]
  omega

/-- One finite state query for each window/state pair. This is a query
budget, not a claim that either predicate has been implemented here. -/
def stateQueries (P : SevenDFA (Fin σ)) (plan : Plan) : Nat := P.G.stateCount*plan.selectors

theorem stateQueries_bound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n s L D Q : Nat)
    (hD : 0<D) (hL : 0<L) :
    stateQueries P (prepare f n s L D Q)≤P.G.stateCount*selectorBudget n L D Q :=
  Nat.mul_le_mul_left _ (prepare_selectors f n s L D Q hD hL)

end REWB.ResidualDispatch
