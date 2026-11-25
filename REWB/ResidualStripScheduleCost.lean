import REWB.ResidualStripScheduleCoverage

/-! Complete returned schedule counters: shared rank preparation, raw
grid probes, exact-key deduplication, long-strip filtering, cut-grid
construction and emitted jobs. Matcher/DFA query work is not included;
prepare_queries is the budget available for those subsequent calls. -/
namespace REWB.ResidualStripSchedule
variable {σ : Nat}

def preparationBudget (σ n : Nat) : Nat :=
  2*((n+1)*((n.log2+1)*(16*RankIndex.width σ n+4)+1))

def probeBudget (n s : Nat) : Nat := (n/s+1)*(n+1)

def generationBudget (σ n s : Nat) : Nat := preparationBudget σ n+
  (26*(n.log2+1)+26*((n+1).log2+1)+23)*probeBudget n s+8

theorem generate_work (f : Nat→Fin σ) (n s L : Nat) :
    (generate f n s L).work≤generationBudget σ n s := by
  have hg:=IndexedGrid.generate_counts f n s
  have hd:=dedup_work n L (IndexedGrid.generate f n s).strips
  have hm:=Nat.mul_le_mul_left (26*((n+1).log2+1)+15) hg.2.1
  have hp : (IndexedGrid.generate f n s).preparation≤preparationBudget σ n := hg.2.2.2
  have hq : (IndexedGrid.generate f n s).queryWork≤(26*(n.log2+1)+2)*probeBudget n s := hg.2.2.1
  have hu : (dedup n L (IndexedGrid.generate f n s).strips).work≤
      (26*((n+1).log2+1)+15)*probeBudget n s+5 := Nat.le_trans hd (Nat.add_le_add_right hm 5)
  simp only [generate,generationBudget]
  rw [hg.1]
  change (IndexedGrid.generate f n s).preparation+(IndexedGrid.generate f n s).queryWork+
    6*probeBudget n s+(dedup n L (IndexedGrid.generate f n s).strips).work+3≤_
  rw [show 26*(n.log2+1)+26*((n+1).log2+1)+23=
    (26*(n.log2+1)+2)+(26*((n+1).log2+1)+15)+6 by omega,Nat.add_mul,Nat.add_mul]
  omega

def scheduleBudget (σ n s L D : Nat) : Nat :=
  generationBudget σ n s+13*((2*n^2)/D)+38*(n^2/L)+4

theorem prepare_work (f : Nat→Fin σ) (n s L D : Nat) (hD : 0<D) (hL : 0<L) :
    (prepare f n s L D).work≤scheduleBudget σ n s L D := by
  have hg:=generate_work f n s L
  have hc:=collect_work f n D L (generate f n s L).strips hD hL
    (fun R hR=>(generate_sound f n s L R hR).1) (generate_nodup f n s L)
    (fun R hR=>(generate_sound f n s L R hR).2)
  simp only [prepare,scheduleBudget]
  omega

/-- The number of later language queries is independent of the raw
sampling stride s; it is paid by distinct long strips and cut windows. -/
theorem prepare_query_length (f : Nat→Fin σ) (n s L D : Nat) :
    (prepare f n s L D).batch.queries=(prepare f n s L D).batch.jobs.length :=
  (collect_counts D L _).1

end REWB.ResidualStripSchedule
