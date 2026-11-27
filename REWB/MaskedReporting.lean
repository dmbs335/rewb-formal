import REWB.DyadicIndex

/-! Output extraction from a measured interval-existence query.

    The query returns both its answer and its own operation count.  The
    reporting traversal never modifies a target mask: the mask is captured
    by the query.  Its correctness hypothesis is an explicit subroutine
    contract, not a construction of the missing fast masked index.

    False interval queries are counted as well as successful ones.  With k
    reported sources in a height-h tree, at most 1+2*h*k queries are issued.
    The separate query-work counter is retained in the final bound; it is
    never silently charged as a constant-time operation. -/
namespace REWB.MaskedReporting

abbrev Query := Nat → Nat → Bool × Nat

def QueryCorrect (ask : Query) (good : Nat → Prop) : Prop :=
  ∀ l r, (ask l r).1 = true ↔ ∃ s, l ≤ s ∧ s < r ∧ good s

structure Result where
  starts : List Nat
  count : Nat
  calls : Nat
  queryWork : Nat
  copies : Nat
  deriving Repr

/-- The two children represent disjoint half-open intervals.  A negative
    answer prunes the entire interval, including at height zero. -/
def report (ask : Query) : Nat → Nat → Result
  | 0, lo =>
    let q := ask lo (lo+1)
    if q.1 then ⟨[lo],1,1,q.2,0⟩ else ⟨[],0,1,q.2,0⟩
  | h+1, lo =>
    let q := ask lo (lo+2^(h+1))
    if q.1 then
      let a := report ask h lo
      let b := report ask h (lo+2^h)
      ⟨a.starts++b.starts,a.count+b.count,1+a.calls+b.calls,
        q.2+a.queryWork+b.queryWork,a.copies+b.copies+a.count⟩
    else ⟨[],0,1,q.2,0⟩

/-- Cached output size avoids traversing the output just to compute the
    append-work counter. -/
theorem report_count (ask : Query) (h lo : Nat) :
    (report ask h lo).count = (report ask h lo).starts.length := by
  induction h generalizing lo with
  | zero => simp only [report]; split <;> rfl
  | succ h ih =>
    simp only [report]
    split
    · simp only [ih,List.length_append]
    · rfl

theorem report_sublist (ask : Query) (h lo : Nat) :
    List.Sublist (report ask h lo).starts (List.range' lo (2^h)) := by
  induction h generalizing lo with
  | zero =>
    simp only [report,Nat.pow_zero]
    split <;> simp
  | succ h ih =>
    simp only [report]
    split
    · have ha := (ih lo).append (ih (lo+2^h))
      simpa only [List.range'_append_1,Nat.pow_succ,Nat.mul_two] using ha
    · exact List.nil_sublist _

theorem report_nodup (ask : Query) (h lo : Nat) :
    (report ask h lo).starts.Nodup :=
  (report_sublist ask h lo).nodup (List.nodup_range' 1)

theorem report_length (ask : Query) (h lo : Nat) :
    (report ask h lo).starts.length ≤ 2^h := by
  have hh := (report_sublist ask h lo).length_le
  simpa only [List.length_range'] using hh

theorem report_correct (ask : Query) (good : Nat → Prop)
    (hq : QueryCorrect ask good) (h lo s : Nat) :
    s ∈ (report ask h lo).starts ↔ lo ≤ s ∧ s < lo+2^h ∧ good s := by
  induction h generalizing lo with
  | zero =>
    simp only [report,Nat.pow_zero]
    split
    next hp =>
      obtain ⟨x,hl,hr,hg⟩ := (hq lo (lo+1)).mp hp
      have he : x=lo := by omega
      subst x
      simp only [List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨Nat.le_refl _,by omega,hg⟩
      · intro hs
        omega
    next hp =>
      simp only [List.not_mem_nil,false_iff]
      intro hs
      exact hp ((hq lo (lo+1)).mpr ⟨s,hs⟩)
  | succ h ih =>
    simp only [report]
    split
    next hp =>
      simp only [List.mem_append,ih,Nat.pow_succ,Nat.mul_two]
      constructor
      · rintro (ha | hb)
        · exact ⟨ha.1,by omega,ha.2.2⟩
        · exact ⟨by omega,by omega,hb.2.2⟩
      · intro hs
        by_cases hm : s<lo+2^h
        · exact Or.inl ⟨hs.1,hm,hs.2.2⟩
        · exact Or.inr ⟨by omega,by omega,hs.2.2⟩
    next hp =>
      simp only [List.not_mem_nil,false_iff]
      intro hs
      exact hp ((hq lo (lo+2^(h+1))).mpr ⟨s,hs⟩)

theorem report_positive (ask : Query) (good : Nat → Prop)
    (hq : QueryCorrect ask good) (h lo : Nat)
    (hp : (ask lo (lo+2^h)).1 = true) :
    0 < (report ask h lo).starts.length := by
  obtain ⟨s,hs⟩ := (hq lo (lo+2^h)).mp hp
  have hm := (report_correct ask good hq h lo s).mpr hs
  exact List.length_pos_of_mem hm

/-- Successful internal queries each lead to at least one output.  This
    bounds the negative queries reached by those internal nodes as well. -/
theorem report_calls (ask : Query) (good : Nat → Prop)
    (hq : QueryCorrect ask good) (h lo : Nat) :
    (report ask h lo).calls ≤ 1+2*h*(report ask h lo).starts.length := by
  induction h generalizing lo with
  | zero => simp only [report]; split <;> simp
  | succ h ih =>
    have ha := ih lo
    have hb := ih (lo+2^h)
    by_cases hp : (ask lo (lo+2^(h+1))).1 = true
    · have hk := report_positive ask good hq (h+1) lo hp
      simp only [report,hp,if_true,List.length_append] at hk ⊢
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at ⊢
      omega
    · simp only [report,hp,if_false,List.length_nil,Nat.mul_zero,Nat.add_zero]
      exact Nat.le_refl _

/-- Output concatenation copies each reported cell at most once per
    ancestor.  Query work is counted separately. -/
theorem report_copies (ask : Query) (h lo : Nat) :
    (report ask h lo).copies ≤ h*(report ask h lo).starts.length := by
  induction h generalizing lo with
  | zero => simp only [report]; split <;> simp
  | succ h ih =>
    have ha := ih lo
    have hb := ih (lo+2^h)
    simp only [report]
    split
    · simp only [report_count,List.length_append,Nat.mul_add,Nat.add_mul,Nat.one_mul]
      omega
    · simp

/-- A per-query bound is used only when independently supplied.  The
    query's measured cost is accumulated on every visited interval. -/
theorem report_queryWork (ask : Query) (A : Nat)
    (hA : ∀ l r, (ask l r).2 ≤ A) (h lo : Nat) :
    (report ask h lo).queryWork ≤ A*(report ask h lo).calls := by
  induction h generalizing lo with
  | zero =>
    have hx := hA lo (lo+1)
    simp only [report]
    split <;> simpa using hx
  | succ h ih =>
    have hx := hA lo (lo+2^(h+1))
    have ha := ih lo
    have hb := ih (lo+2^h)
    simp only [report]
    split
    · simp only [Nat.mul_add,Nat.mul_one]
      omega
    · simpa using hx

def totalWork (r : Result) : Nat := r.calls+r.queryWork+r.copies

theorem report_totalWork (ask : Query) (good : Nat → Prop)
    (hq : QueryCorrect ask good) (A : Nat)
    (hA : ∀ l r, (ask l r).2 ≤ A) (h lo : Nat) :
    totalWork (report ask h lo) ≤
      (A+1)+(2*A+3)*h*(report ask h lo).starts.length := by
  have hc := report_calls ask good hq h lo
  have hp := report_copies ask h lo
  have hw := report_queryWork ask A hA h lo
  have hm := Nat.mul_le_mul_left A hc
  simp only [totalWork]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,
    Nat.mul_assoc,Nat.mul_left_comm A 2] at hc hp hw hm ⊢
  omega

/-- The output list removes only sources.  Evaluating this function can
    inspect the list; its cost is part of any later query that reads it. -/
def eraseSources (source : Nat → Bool) (found : List Nat) : Nat → Bool :=
  fun s => source s && !found.contains s

theorem eraseSources_true (source : Nat → Bool) (found : List Nat) (s : Nat) :
    eraseSources source found s = true ↔ source s = true ∧ s ∉ found := by
  simp [eraseSources]

theorem eraseSources_preserves (source : Nat → Bool) (found : List Nat)
    (s : Nat) (hs : s ∉ found) : eraseSources source found s = source s := by
  simp [eraseSources,hs]

theorem eraseSources_removes (source : Nat → Bool) (found : List Nat)
    (s : Nat) (hs : s ∈ found) : eraseSources source found s = false := by
  simp [eraseSources,hs]

variable {α : Type}

/-- The target mask is immutable input.  The source mask represents starts
    that have not yet been reported by another family. -/
def MaskedQueryCorrect (B C E : DFA α) (w : Word α)
    (target source : Nat → Bool) (ask : Query) : Prop :=
  QueryCorrect ask (fun s => source s = true ∧ Spec.maskedStart B C E w target s)

def reportMasked (ask : Query) (n : Nat) : Result :=
  report ask (DyadicIndex.heightFor (n+1)) 0

theorem maskedStart_bound (B C E : DFA α) (w : Word α)
    (target : Nat → Bool) (s : Nat) (hs : Spec.maskedStart B C E w target s) :
    s ≤ w.length := by
  obtain ⟨a,j,t,hsa,haj,hjt,ht,_⟩ := hs
  omega

/-- The terminal boundary n is included.  Padding leaves beyond n cannot
    be reported by a correct query. -/
theorem reportMasked_correct (B C E : DFA α) (w : Word α)
    (target source : Nat → Bool) (ask : Query)
    (hq : MaskedQueryCorrect B C E w target source ask) (s : Nat) :
    s ∈ (reportMasked ask w.length).starts ↔
      source s = true ∧ Spec.maskedStart B C E w target s := by
  rw [reportMasked,report_correct ask _ hq]
  constructor
  · exact fun hs => hs.2.2
  · intro hs
    have hb := maskedStart_bound B C E w target s hs.2
    have hc := DyadicIndex.capacity (w.length+1)
    exact ⟨Nat.zero_le _,by omega,hs⟩

theorem reportMasked_sublist (B C E : DFA α) (w : Word α)
    (target source : Nat → Bool) (ask : Query)
    (hq : MaskedQueryCorrect B C E w target source ask) :
    List.Sublist (reportMasked ask w.length).starts (List.range (w.length+1)) := by
  let N := w.length+1
  let cap := 2^(DyadicIndex.heightFor N)
  have hcap : N ≤ cap := DyadicIndex.capacity N
  have hs := report_sublist ask (DyadicIndex.heightFor N) 0
  have he : List.range' 0 N ++ List.range' N (cap-N) = List.range' 0 cap := by
    simpa only [Nat.zero_add,Nat.add_sub_of_le hcap] using
      (List.range'_append_1 (s:=0) (m:=N) (n:=cap-N))
  have hbig : List.Sublist (reportMasked ask w.length).starts
      (List.range' 0 N ++ List.range' N (cap-N)) := by
    rw [he]
    exact hs
  have hp : List.Sublist (reportMasked ask w.length).starts (List.range' 0 N) := by
    apply List.Sublist.of_sublist_append_left ?_ hbig
    intro s hmem hright
    have hb := maskedStart_bound B C E w target s
      ((reportMasked_correct B C E w target source ask hq s).mp hmem).2
    have hr : N ≤ s := (List.mem_range'_1.mp hright).1
    dsimp [N] at hr
    omega
  simpa only [List.range_eq_range'] using hp

theorem reportMasked_length (B C E : DFA α) (w : Word α)
    (target source : Nat → Bool) (ask : Query)
    (hq : MaskedQueryCorrect B C E w target source ask) :
    (reportMasked ask w.length).starts.length ≤ w.length+1 := by
  have hh := (reportMasked_sublist B C E w target source ask hq).length_le
  simpa only [List.length_range] using hh

/-- Removing all reported sources leaves no eligible source for the
    current family.  The exact same target mask appears in the conclusion. -/
theorem reportMasked_exhausts (B C E : DFA α) (w : Word α)
    (target source : Nat → Bool) (ask : Query)
    (hq : MaskedQueryCorrect B C E w target source ask) (s : Nat) :
    ¬ (eraseSources source (reportMasked ask w.length).starts s = true ∧
      Spec.maskedStart B C E w target s) := by
  rintro ⟨hm,hw⟩
  obtain ⟨hs,hnot⟩ := (eraseSources_true _ _ s).mp hm
  exact hnot ((reportMasked_correct B C E w target source ask hq s).mpr ⟨hs,hw⟩)

theorem reportMasked_calls (B C E : DFA α) (w : Word α)
    (target source : Nat → Bool) (ask : Query)
    (hq : MaskedQueryCorrect B C E w target source ask) :
    (reportMasked ask w.length).calls ≤
      1+2*(Nat.log2 (w.length+1)+1)*(reportMasked ask w.length).starts.length :=
  report_calls ask _ hq _ _

theorem reportMasked_totalWork (B C E : DFA α) (w : Word α)
    (target source : Nat → Bool) (ask : Query)
    (hq : MaskedQueryCorrect B C E w target source ask)
    (A : Nat) (hA : ∀ l r, (ask l r).2 ≤ A) :
    totalWork (reportMasked ask w.length) ≤
      (A+1)+(2*A+3)*(Nat.log2 (w.length+1)+1)*
        (reportMasked ask w.length).starts.length :=
  report_totalWork ask _ hq A hA _ _

namespace SharedTargetRegression

def singleton : DFA Unit :=
  ⟨3,⟨0,by decide⟩,
    fun q _ => if q.val=0 then ⟨1,by decide⟩ else ⟨2,by decide⟩,
    fun q => decide (q.val=1)⟩

def arbitrary : DFA Unit :=
  ⟨1,⟨0,by decide⟩,fun _ _ => ⟨0,by decide⟩,fun _ => true⟩

def word : Word Unit := [(),(),(),()]
def target : Nat → Bool := fun j => decide (j=3)

/-- One target occurrence simultaneously witnesses three distinct source
    starts.  This is proved from the original masked-start specification. -/
theorem three_sources :
    Spec.maskedStart singleton arbitrary arbitrary word target 0 ∧
    Spec.maskedStart singleton arbitrary arbitrary word target 1 ∧
    Spec.maskedStart singleton arbitrary arbitrary word target 2 := by
  constructor
  · refine ⟨1,3,4,by decide,by decide,by decide,by decide,by decide,?_,?_,?_,?_⟩
    all_goals rfl
  · constructor
    · refine ⟨2,3,4,by decide,by decide,by decide,by decide,by decide,?_,?_,?_,?_⟩
      all_goals rfl
    · refine ⟨3,3,4,by decide,by decide,by decide,by decide,by decide,?_,?_,?_,?_⟩
      all_goals rfl

theorem exact_sources (s : Nat) :
    Spec.maskedStart singleton arbitrary arbitrary word target s ↔ s<3 := by
  constructor
  · rintro ⟨a,j,t,hsa,haj,_,_,hm,_,hb,_⟩
    have hj : j=3 := by simpa [target] using hm
    subst j
    by_cases hs : s<3
    · exact hs
    · have he : s=3 := by omega
      have ha : a=3 := by omega
      subst s
      subst a
      simp [Spec.slice,DFA.accepts,DFA.run,singleton] at hb
  · intro hs
    have he : s=0 ∨ s=1 ∨ s=2 := by omega
    rcases he with rfl | rfl | rfl
    · exact three_sources.1
    · exact three_sources.2.1
    · exact three_sources.2.2

/-- Deleting the shared target destroys every witness, including starts
    that have not yet been reported. -/
theorem deleting_target_loses_all (s : Nat) :
    ¬ Spec.maskedStart singleton arbitrary arbitrary word (eraseSources target [3]) s := by
  rintro ⟨a,j,t,_,_,_,_,hm,_⟩
  obtain ⟨ht,hn⟩ := (eraseSources_true target [3] j).mp hm
  have he : j=3 := by simpa [target] using ht
  exact hn (by simp [he])

/-- Deleting only the first source preserves the remaining two witnesses. -/
theorem deleting_source_preserves_others :
    (eraseSources (fun _ => true) [0] 1 = true ∧
      Spec.maskedStart singleton arbitrary arbitrary word target 1) ∧
    (eraseSources (fun _ => true) [0] 2 = true ∧
      Spec.maskedStart singleton arbitrary arbitrary word target 2) := by
  exact ⟨⟨by decide,three_sources.2.1⟩,⟨by decide,three_sources.2.2⟩⟩

end SharedTargetRegression

end REWB.MaskedReporting
