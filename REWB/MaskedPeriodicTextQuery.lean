import REWB.MaskedPeriodicTextSlices

/-! The executable three-branch query is now an actual finite-text
    matcher on a periodic interval. The source is its absolute position
    in the one shared word index; quotient/remainder parameters are
    computed from the real right endpoint. No factor-word answer oracle
    is supplied. These theorems are local correctness results; they do
    not construct the global run schedule or bound its total cost.
-/
namespace REWB.MaskedPeriodic.Text
open REWB.Periodic REWB.Spec
open REWB.MaskedFiniteAction.Maps REWB.MaskedCut REWB.MaskedCut.DFAIndex
variable {α : Type}

/-- Charge the fixed endpoint work: two comparisons, one addition,
    conjunction, subtraction, quotient, and remainder. This extends the
    inherited scalar counter; the inherited compiler exclusions remain. -/
def chargeEndpoints (answer : IndexedAnswer) : IndexedAnswer :=
  ⟨⟨answer.result.answer,answer.result.slots,answer.result.arithmetic+7⟩,
    answer.products,answer.visits⟩

/-- A guarded actual-source query. The immutable stepped count array
    and the shared cut index are prepared inputs. The tail map is either
    the identity (in-run suffix) or an actual shared suffix range query. -/
def query (b c e : DFA α) (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (idx : Index.Tree (jointEnum b c e)) (tail : Map e.stateCount)
    (s R q : Nat) (counts : Array Nat) (base : Nat) : IndexedAnswer :=
  if 0<q ∧ s+q≤R then
    let n := R-s
    chargeEndpoints (phaseQuery b c e prepared idx tail s (n%q) q (n/q) counts base s)
  else ⟨⟨false,0,4⟩,0,0⟩

theorem query_active (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (idx : Index.Tree (jointEnum b c e)) (tail : Map e.stateCount)
    (s R q : Nat) (counts : Array Nat) (base : Nat) (hq : 0<q) (hs : s+q≤R) :
    query b c e prepared idx tail s R q counts base=
      chargeEndpoints
        (phaseQuery b c e prepared idx tail s ((R-s)%q) q ((R-s)/q) counts base s) := by
  have hg : 0<q ∧ s+q≤R := ⟨hq,hs⟩
  simp only [query,if_pos hg]

theorem query_correct (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w tail : Word α) (fallback : α) (s R q : Nat)
    (mask : Array Bool) (base len : Nat) (hq : 0<q) (hn : R≤w.length)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q) :
    (query b c e prepared (DFAIndex.build b c e w).1 (wordMap e tail) s R q
      (MaskedProgression.build mask base len (prepared.K*q)).counts base).result.answer=true ↔
        Witness b c e w tail s R q mask base len := by
  by_cases hs : s+q≤R
  · rw [query_active b c e prepared _ _ s R q _ base hq hs]
    change (phaseQuery b c e prepared (DFAIndex.build b c e w).1 (wordMap e tail)
      s ((R-s)%q) q ((R-s)/q)
      (MaskedProgression.build mask base len (prepared.K*q)).counts base s).result.answer=true ↔ _
    have he : (R-s)%q<q := Nat.mod_lt _ hq
    have hdecomp := quotient_length q (R-s)
    have hper := (RunGeometry.on_iff _ s R q).mp hp
    have hper' : Period (shift (ArrayText.read w.toArray fallback) s)
        (((R-s)/q)*q+(R-s)%q) q := by simpa only [hdecomp] using hper
    rw [phaseQuery_correct b c e prepared w tail s ((R-s)%q) q ((R-s)/q)
      mask base len s hq he (by omega),
      phase_families b c e w tail fallback s ((R-s)%q) q ((R-s)/q)
        mask base len he (by omega),
      families_iff b c e _ tail q ((R-s)/q) ((R-s)%q) mask base len s hq he hper',
      hdecomp,local_witness_iff b c e w tail fallback s R q mask base len hp (by omega) hn]
  · have hguard : ¬(0<q ∧ s+q≤R) := by omega
    simp only [query,if_neg hguard,Bool.false_eq_true,false_iff]
    rintro ⟨L,k,hl,hd,hb,_⟩
    omega

/-- The direct run entry point needs only a valid run and source
    membership. In particular, phases need not align with the run start.
    The run's existing least-period/maximality certificate supplies its
    real character periodicity; no new semantic oracle is assumed. -/
theorem query_run_correct (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w tail : Word α) (fallback : α) (l R q s : Nat)
    (mask : Array Bool) (base len : Nat)
    (hr : Run (ArrayText.read w.toArray fallback) w.length l R q) (hs : l≤s) :
    (query b c e prepared (DFAIndex.build b c e w).1 (wordMap e tail) s R q
      (MaskedProgression.build mask base len (prepared.K*q)).counts base).result.answer=true ↔
        Witness b c e w tail s R q mask base len := by
  apply query_correct b c e prepared w tail fallback s R q mask base len
    hr.2.2.2.1.1 hr.2.1
  exact RunGeometry.on_restrict _ l R q s R (RunGeometry.run_on _ _ l R q hr) hs (Nat.le_refl _)

/-- A convenience query whose E automaton ends at the run boundary. -/
def inRun (b c e : DFA α) (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (idx : Index.Tree (jointEnum b c e)) (s R q : Nat) (counts : Array Nat) (base : Nat) :
    IndexedAnswer := query b c e prepared idx (wordMap e []) s R q counts base

theorem inRun_correct (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w : Word α) (fallback : α) (s R q : Nat) (mask : Array Bool) (base len : Nat)
    (hq : 0<q) (hn : R≤w.length)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q) :
    (inRun b c e prepared (DFAIndex.build b c e w).1 s R q
      (MaskedProgression.build mask base len (prepared.K*q)).counts base).result.answer=true ↔
        Witness b c e w [] s R q mask base len :=
  query_correct b c e prepared w [] fallback s R q mask base len hq hn hp

theorem witness_window (b c e : DFA α) (w tail : Word α) (s R q : Nat)
    (mask : Array Bool) (base len : Nat) (hq : 0<q) (hs : base≤s) (hr : R≤base+len) :
    Witness b c e w tail s R q mask base len ↔
      ∃ L k,2*q≤L ∧ s+L≤s+k*q ∧ s+k*q+L≤R ∧
        slice w s (s+L)=slice w (s+k*q) (s+k*q+L) ∧
        b.accepts (slice w s (s+L)) ∧ c.accepts (slice w (s+L) (s+k*q)) ∧
        e.accepts (slice w (s+k*q+L) R++tail) ∧
        MaskedProgression.readMask mask (s+k*q)=true := by
  constructor
  · rintro ⟨L,k,hl,hd,hb,he,hB,hC,hE,hm⟩
    exact ⟨L,k,hl,hd,hb,he,hB,hC,hE,hm.2.2⟩
  · rintro ⟨L,k,hl,hd,hb,he,hB,hC,hE,hm⟩
    exact ⟨L,k,hl,hd,hb,he,hB,hC,hE,by omega,by omega,hm⟩

end REWB.MaskedPeriodic.Text
