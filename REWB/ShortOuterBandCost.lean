import REWB.ShortOuterBandSound

/-! Counts for all actual keys, chronological events, DFA-vector
transports, bit writes and shared preparations.  With b=min(L,n+1),
the explicit budget is O_{sigma,G,H}((n+1)(b²+b log(n+1)+log(n+1))). -/
namespace REWB.ShortOuter.Band
open REWB.BoundaryApplication
variable {σ : Nat}

def stageBudget (k n width : Nat) : Nat := width*(2*Sweep.stepBudget k n+17)+4

theorem run_bounds (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (fuel : Nat) (st : State G.stateCount)
    (hk : KeyBound keys) (hf : fuel≤keys.length+1) (hsize : st.cells.size=keys.registry.next)
    (hgood : Sweep.Good G w (marks keys suffix fuel) (fuel-1) st.cells) :
    (run G (Range.build G w) keys suffix fuel st).touches≤st.touches+2*fuel*keys.width ∧
    (run G (Range.build G w) keys suffix fuel st).work≤
      st.work+fuel*stageBudget G.stateCount w.length keys.width := by
  induction fuel generalizing st with
  | zero => simp [run]
  | succ x ih =>
    rw [run]
    have hgi:=inserts_stage G w keys suffix x st hk (by omega) hsize hgood
    have hgp:=probes_good G w keys (marks keys suffix x) x keys.width
      (inserts G (Range.build G w) keys suffix x keys.width st) hk (by omega) (Nat.le_refl _)
      (by simpa using hsize) hgi
    have hbi:=inserts_bounds G w keys suffix _ x keys.width st hk (by omega)
      (Nat.le_refl _) hsize hgood
    have hbp:=probes_bounds G w keys (marks keys suffix x) x keys.width
      (inserts G (Range.build G w) keys suffix x keys.width st) hk (by omega) (Nat.le_refl _)
      (by simpa using hsize) hgi
    have hrec:=ih (charge 4 (probes G (Range.build G w) keys x keys.width
      (inserts G (Range.build G w) keys suffix x keys.width st))) (by omega)
      (by simpa using hsize) (by simpa using hgp.weaken (show x-1≤x by omega))
    simp only [charge_touches,charge_work] at hrec
    have he : keys.width*(Sweep.stepBudget G.stateCount w.length+8)+
        keys.width*(Sweep.stepBudget G.stateCount w.length+9)+4=
        stageBudget G.stateCount w.length keys.width := by
      unfold stageBudget
      rw [show 2*Sweep.stepBudget G.stateCount w.length=
        Sweep.stepBudget G.stateCount w.length+Sweep.stepBudget G.stateCount w.length by omega]
      simp only [Nat.mul_add]
      omega
    constructor
    · have hh : 2*(x+1)*keys.width=2*x*keys.width+2*keys.width := by
        simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul]
      rw [hh]
      omega
    · rw [Nat.add_mul,Nat.one_mul]
      omega

def budget (σ g h n width : Nat) : Nat :=
  ((n+1)*width)*Keys.stepBudget σ width+4+
  (6*h+11)*(n+1)+(g+8)*((n.log2+1)*n)+n*g+8*(n+1)+
  (2*((n+1)*width)+g+3)+(n+1)*stageBudget g n width+n+5

theorem build_work (G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (build G H text fallback limit).work≤
      budget σ G.stateCount H.stateCount text.size (min limit (text.size+1)) := by
  have hi:=initial_correct G text.toList (Keys.build text fallback limit) (Suffix.build H text).1
    (by simp only [Keys.build_length,Array.length_toList])
  have hr:=run_bounds G text.toList (Keys.build text fallback limit) (Suffix.build H text).1
    (text.size+1) (initial G (Keys.build text fallback limit))
    (build_keyBound text fallback limit) (by simp only [Keys.build_length]; omega)
    (by simp [initial,Sweep.initial]) hi.1
  have hk:=Keys.build_work text fallback limit
  have hn:=Keys.build_next text fallback limit
  have hs:=Suffix.build_work H text
  simp only [initial,Array.size_replicate,Keys.build_length,Keys.build_width,Array.length_toList] at hr
  have hcells : (Range.build G text.toList).letterCells=text.size*G.stateCount := by
    simp only [Range.build,Array.length_toList]
  simp only [build,Range.build_products,hcells,Array.length_toList,initial,
    Array.size_replicate,Keys.build_length,Keys.build_width]
  unfold budget
  omega

theorem build_touches (G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (build G H text fallback limit).touches≤2*(text.size+1)*min limit (text.size+1) := by
  have hi:=initial_correct G text.toList (Keys.build text fallback limit) (Suffix.build H text).1
    (by simp only [Keys.build_length,Array.length_toList])
  have hr:=run_bounds G text.toList (Keys.build text fallback limit) (Suffix.build H text).1
    (text.size+1) (initial G (Keys.build text fallback limit))
    (build_keyBound text fallback limit) (by simp only [Keys.build_length]; omega)
    (by simp [initial,Sweep.initial]) hi.1
  simpa only [build,initial,Keys.build_width,Nat.zero_add] using hr.1

theorem build_bits_size (G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (build G H text fallback limit).bits.size=(text.size+1)*min limit (text.size+1) := by
  simp only [build,run_bits_size,initial,Array.size_replicate,Keys.build_width,Keys.build_length]

end REWB.ShortOuter.Band
