import REWB.Specifications
import REWB.MarkedDP

/-! The endpoint-anchored outer-copy column, independent of periodicity and
    suffix-tree indexes. The common-suffix limit is initially computed by a
    finite reference search. Its faster implementation is a separate task. -/
namespace REWB.OuterColumn
open REWB.Spec (slice)
variable {α : Type}

private theorem take_sum (w : Word α) (a b : Nat) :
    w.take (a+b) = w.take a ++ (w.drop a).take b := by
  induction a generalizing w with
  | zero => simp
  | succ a ih =>
    cases w with
    | nil => simp
    | cons c cs =>
      simp [Nat.succ_add, List.take, List.drop, ih]

private theorem drop_sum (w : Word α) (a b : Nat) :
    w.drop (a+b) = (w.drop a).drop b := by
  induction a generalizing w with
  | zero => simp
  | succ a ih =>
    cases w with
    | nil => simp
    | cons c cs => simp [Nat.succ_add, List.drop, ih]

@[simp] theorem slice_self (w : Word α) (a : Nat) :
    slice w a a = [] := by simp [slice]

theorem slice_split (w : Word α) (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) :
    slice w a c = slice w a b ++ slice w b c := by
  unfold slice
  have h1 : c-a = (b-a)+(c-b) := by omega
  have h2 : a+(b-a)=b := by omega
  rw [h1, take_sum, ← drop_sum, h2]

theorem slice_length (w : Word α) (a b : Nat) (hab : a ≤ b)
    (hb : b ≤ w.length) :
    (slice w a b).length = b-a := by
  unfold slice
  rw [List.length_take, List.length_drop]
  omega

private theorem equal_split {x y z t : Word α}
    (he : x ++ y = z ++ t) (hl : x.length = z.length) :
    x = z ∧ y = t := by
  induction x generalizing z with
  | nil =>
    cases z with
    | nil => exact ⟨rfl,he⟩
    | cons c cs => simp at hl
  | cons c cs ih =>
    cases z with
    | nil => simp at hl
    | cons d ds =>
      have hh : c=d ∧ cs++y=ds++t := by simpa using he
      have hlen : cs.length=ds.length := by simpa using hl
      obtain ⟨h1,h2⟩ := ih (z := ds) hh.2 hlen
      exact ⟨by rw [hh.1,h1],h2⟩

/-- Equal suffixes of two ends, with nonoverlap included. -/
abbrev Common (w : Word α) (e f d : Nat) : Prop :=
  d ≤ e ∧ d ≤ f-e ∧ slice w (e-d) e = slice w (f-d) f

/-- Certificate for min(LCS(e,f), f-e). -/
def IsMaxCommon (w : Word α) (e f d : Nat) : Prop :=
  Common w e f d ∧ ∀ k, Common w e f k → k ≤ d

/-- Slow but executable reference maximum. No fast LCS claim here. -/
def maxCommon [DecidableEq α] (w : Word α) (e f : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => if Common w e f (k+1) then k+1 else maxCommon w e f k

theorem maxCommon_spec [DecidableEq α] (w : Word α) (e f limit : Nat) :
    Common w e f (maxCommon w e f limit) ∧
    maxCommon w e f limit ≤ limit ∧
    ∀ k, k ≤ limit → Common w e f k → k ≤ maxCommon w e f limit := by
  induction limit with
  | zero =>
    refine ⟨?_,Nat.le_refl 0,?_⟩
    · simp [maxCommon, Common]
    · intro k hk hc
      exact hk
  | succ limit ih =>
    by_cases h : Common w e f (limit+1)
    · simp only [maxCommon, if_pos h]
      exact ⟨h,Nat.le_refl _,fun k hk _ => hk⟩
    · simp only [maxCommon, if_neg h]
      refine ⟨ih.1,Nat.le_trans ih.2.1 (Nat.le_succ limit),?_⟩
      intro k hk hc
      by_cases hk' : k ≤ limit
      · exact ih.2.2 k hk' hc
      · have he : k = limit+1 := by omega
        subst k
        exact False.elim (h hc)

theorem maxCommon_isMax [DecidableEq α] (w : Word α) (e f : Nat) :
    IsMaxCommon w e f (maxCommon w e f e) := by
  have h := maxCommon_spec w e f e
  exact ⟨h.1,fun k hk => h.2.2 k hk.1 hk⟩

/-- Shorten the same aligned suffix in both copies. The removed part is
    transported into the gap following the first copy. -/
theorem common_transport (w : Word α) (e f d k : Nat)
    (hef : e ≤ f) (hf : f ≤ w.length)
    (hd : Common w e f d) (hk : k ≤ d) :
    Common w e f k ∧
      slice w e (f-k) = slice w e (f-d) ++ slice w (e-d) (e-k) := by
  rcases hd with ⟨hde,hdf,heq⟩
  have hx := slice_split w (e-d) (e-k) e (by omega) (by omega)
  have hy := slice_split w (f-d) (f-k) f (by omega) (by omega)
  have hlen : (slice w (e-d) (e-k)).length =
      (slice w (f-d) (f-k)).length := by
    rw [slice_length w (e-d) (e-k) (by omega) (by omega),
      slice_length w (f-d) (f-k) (by omega) (by omega)]
    omega
  obtain ⟨hp,hs⟩ := equal_split (hx.symm.trans (heq.trans hy)) hlen
  refine ⟨⟨by omega,by omega,hs⟩,?_⟩
  calc
    slice w e (f-k) =
      slice w e (f-d) ++ slice w (f-d) (f-k) :=
        slice_split w e (f-d) (f-k) (by omega) (by omega)
    _ = _ := by rw [← hp]

/-- Exact match of the two outer copies with both ends fixed. -/
def Anchored (g h : DFA α) (w : Word α) (p e f : Nat) : Prop :=
  p ≤ e ∧ e ≤ f ∧ f ≤ w.length ∧ e-p ≤ f-e ∧
  slice w p e = slice w (f-(e-p)) f ∧
  g.accepts (slice w e (f-(e-p))) ∧
  h.accepts (slice w f w.length)

/-- The core column reduction: one injection at e-d accounts for every
    shorter equal capture ending at e and f, including the empty one. -/
theorem anchored_iff (g h : DFA α) (w : Word α) (p e f d : Nat)
    (hp : p ≤ e) (hef : e ≤ f) (hf : f ≤ w.length)
    (hd : IsMaxCommon w e f d) :
    Anchored g h w p e f ↔
      e-d ≤ p ∧
      g.final (g.run (g.run g.initial (slice w e (f-d)))
        (slice w (e-d) p)) = true ∧ h.accepts (slice w f w.length) := by
  have ep : e-(e-p)=p := by omega
  constructor
  · rintro ⟨_,_,_,hn,heq,hg,hh⟩
    have hc : Common w e f (e-p) := by
      refine ⟨by omega,hn,?_⟩
      rw [ep]
      exact heq
    have hk := hd.2 (e-p) hc
    have hgap := (common_transport w e f d (e-p) hef hf hd.1 hk).2
    rw [ep] at hgap
    refine ⟨by omega,?_,hh⟩
    simpa [DFA.accepts, hgap, DFA.run_append] using hg
  · rintro ⟨hp0,hg,hh⟩
    have hde := hd.1.1
    have hk : e-p ≤ d := by omega
    obtain ⟨⟨_,hn,heq⟩,hgap⟩ := common_transport w e f d (e-p) hef hf hd.1 hk
    rw [ep] at heq hgap
    refine ⟨hp,hef,hf,hn,heq,?_,hh⟩
    simpa [DFA.accepts, hgap, DFA.run_append] using hg

/-- A generic seeded scan of the G automaton. Multiple witnesses are merged
    only when they reach the same DFA state. -/
def Active (g : DFA α) (w : Word α)
    (seed : Nat → Fin g.stateCount → Prop) (p : Nat)
    (q : Fin g.stateCount) : Prop :=
  ∃ a q0, a ≤ p ∧ seed a q0 ∧ g.run q0 (slice w a p) = q

theorem active_zero (g : DFA α) (w : Word α)
    (seed : Nat → Fin g.stateCount → Prop) (q : Fin g.stateCount) :
    Active g w seed 0 q ↔ seed 0 q := by
  constructor
  · rintro ⟨a,q0,ha,hs,hr⟩
    have he : a=0 := by omega
    subst a
    simp [DFA.run] at hr
    rwa [hr] at hs
  · intro hs
    exact ⟨0,q,Nat.le_refl 0,hs,by simp [DFA.run]⟩

/-- The forward DP invariant; the last factor is a single character when
    p is a valid character index (see slice_length). -/
theorem active_succ (g : DFA α) (w : Word α)
    (seed : Nat → Fin g.stateCount → Prop) (p : Nat)
    (q : Fin g.stateCount) :
    Active g w seed (p+1) q ↔
      seed (p+1) q ∨
      ∃ prev, Active g w seed p prev ∧
        g.run prev (slice w p (p+1)) = q := by
  constructor
  · rintro ⟨a,q0,ha,hs,hr⟩
    by_cases he : a=p+1
    · subst a
      simp [DFA.run] at hr
      exact Or.inl (hr ▸ hs)
    · have hap : a ≤ p := by omega
      refine Or.inr ⟨g.run q0 (slice w a p),⟨a,q0,hap,hs,rfl⟩,?_⟩
      rw [slice_split w a p (p+1) hap (by omega), DFA.run_append] at hr
      exact hr
  · intro h
    rcases h with hs | ⟨prev,⟨a,q0,ha,hs,hr⟩,hp⟩
    · exact ⟨p+1,q,Nat.le_refl _,hs,by simp [DFA.run]⟩
    · refine ⟨a,q0,by omega,hs,?_⟩
      rw [slice_split w a p (p+1) ha (by omega), DFA.run_append, hr]
      exact hp

/-- A seed is induced by any eligible second-copy end. -/
def Seed [DecidableEq α] (g h : DFA α) (w : Word α) (e a : Nat)
    (q : Fin g.stateCount) : Prop :=
  ∃ f, e ≤ f ∧ f ≤ w.length ∧
    a = e-maxCommon w e f e ∧
    q = g.run g.initial (slice w e (f-maxCommon w e f e)) ∧
    h.accepts (slice w f w.length)

/-- Pointwise correctness of the outer-copy column via a seeded scan. -/
theorem column_correct [DecidableEq α] (g h : DFA α)
    (w : Word α) (e p : Nat) (hp : p ≤ e) :
    (∃ f, Anchored g h w p e f) ↔
      ∃ q, Active g w (Seed g h w e) p q ∧ g.final q = true := by
  constructor
  · rintro ⟨f,ho⟩
    have hef := ho.2.1
    have hf := ho.2.2.1
    let d := maxCommon w e f e
    obtain ⟨ha,hg,hh⟩ :=
      (anchored_iff g h w p e f d hp hef hf (maxCommon_isMax w e f)).mp ho
    let q0 := g.run g.initial (slice w e (f-d))
    exact ⟨g.run q0 (slice w (e-d) p),
      ⟨e-d,q0,ha,⟨f,hef,hf,rfl,rfl,hh⟩,rfl⟩,hg⟩
  · rintro ⟨q,⟨a,q0,ha,⟨f,hef,hf,he,hq0,hh⟩,hr⟩,hq⟩
    subst a
    subst q0
    refine ⟨f,(anchored_iff g h w p e f (maxCommon w e f e)
      hp hef hf (maxCommon_isMax w e f)).mpr ⟨ha,?_,hh⟩⟩
    rw [hr]
    exact hq

end REWB.OuterColumn
