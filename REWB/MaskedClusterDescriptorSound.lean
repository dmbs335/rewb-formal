import REWB.MaskedClusterDescriptor

/-! The descriptor queries recover exact occurrence/leader intervals.
These ownership facts require only the maintained tree invariant, not
periodicity or completeness, and are suitable for locating one dirty bank
after a source-mask erase. -/
namespace REWB.MaskedClusterDescriptor
open REWB.MaskedOrdered
variable {h : Nat}

theorem pred_some_iff (xs : List Nat) (p : Nat) (answer : Option Nat)
    (hs : Tree.PredSpec xs p answer) (q : Nat) :
    answer=some q ↔ q∈xs ∧ q<p ∧ ∀r,r∈xs→r<p→r≤q := by
  cases answer with
  | none =>
    simp only [reduceCtorEq,false_iff]
    rintro ⟨hq,hqp,_⟩
    have hh:=hs q hq
    omega
  | some a =>
    simp only [Option.some.injEq]
    constructor
    · intro he; subst q; exact hs
    · rintro ⟨hq,hqp,hm⟩
      exact Nat.le_antisymm (hm a hs.1 hs.2.1) (hs.2.2 q hq hqp)

def Owns (s : MaskedClusterLeaders.State h) (p first : Nat) : Prop :=
  p∈s.occurrences.entries ∧ first∈s.leaders.entries ∧ first≤p ∧
    ∀q,q∈s.leaders.entries→q≤p→q≤first

theorem locate_correct (s : MaskedClusterLeaders.State h) (capacity length p first : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h) :
    (locate s capacity p).1=some first ↔ Owns s p first := by
  have hm:=Tree.contains_correct s.occurrences capacity p hi.occFits hc
  have hp:=Tree.pred_correct s.leaders capacity (p+1) hi.leadGood hi.leadFits hc
  simp only [locate]
  split
  next hmem =>
    rw [pred_some_iff _ _ _ hp]
    simp only [Nat.lt_succ_iff]
    exact ⟨fun hh=>⟨hm.mp hmem,hh⟩,And.right⟩
  next hmem =>
    simp only [reduceCtorEq,false_iff]
    intro hh
    exact hmem (hm.mpr hh.1)

theorem locate_unique (s : MaskedClusterLeaders.State h) (p a b : Nat)
    (ha : Owns s p a) (hb : Owns s p b) : a=b :=
  Nat.le_antisymm (hb.2.2.2 a ha.2.1 ha.2.2.1) (ha.2.2.2 b hb.2.1 hb.2.2.1)

structure Sound (s : MaskedClusterLeaders.State h) (capacity : Nat) (d : Descriptor) : Prop where
  firstLeader : d.first∈s.leaders.entries
  firstMember : d.first∈s.occurrences.entries
  lastMember : d.last∈s.occurrences.entries
  first_le_last : d.first≤d.last
  nextSpec : Tree.SuccSpec s.leaders.entries d.first d.next
  lastSpec : match d.next with
    | none => Tree.MaxSpec s.occurrences.entries (some d.last)
    | some p => Tree.PredSpec s.occurrences.entries p (some d.last)
  materialized : d=(finish s.occurrences capacity d.first d.last d.next).1

theorem finish_sound (s : MaskedClusterLeaders.State h) (capacity first last : Nat) (next : Option Nat)
    (hfl : first∈s.leaders.entries) (hfm : first∈s.occurrences.entries)
    (hn : Tree.SuccSpec s.leaders.entries first next)
    (hl : match next with
      | none => Tree.MaxSpec s.occurrences.entries (some last)
      | some p => Tree.PredSpec s.occurrences.entries p (some last)) :
    Sound s capacity (finish s.occurrences capacity first last next).1 := by
  cases next with
  | none => exact ⟨hfl,hfm,hl.1,hl.2 first hfm,hn,hl,rfl⟩
  | some p => exact ⟨hfl,hfm,hl.1,hl.2.2 first hfm hn.2.1,hn,hl,rfl⟩

theorem describeLeader_exists (s : MaskedClusterLeaders.State h) (capacity length first : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h)
    (hf : first∈s.leaders.entries) :
    ∃d,(describeLeader s capacity first).1=some d ∧ d.first=first ∧ Sound s capacity d := by
  have hm : (Tree.contains s.leaders capacity first).1=true :=
    (Tree.contains_correct s.leaders capacity first hi.leadFits hc).mpr hf
  have hfm:=((hi.represented first).mp hf).1
  have hn:=Tree.succ_correct s.leaders capacity first hi.leadGood hi.leadFits hc
  cases he : (Tree.succ s.leaders capacity first).1 with
  | none =>
    rw [he] at hn
    have hl:=Tree.last_spec s.occurrences 0 hi.occGood hi.occFits
    cases ho : s.occurrences.last with
    | none =>
      rw [ho] at hl
      change s.occurrences.entries=[] at hl
      rw [hl] at hfm
      cases hfm
    | some last =>
      rw [ho] at hl
      refine ⟨(finish s.occurrences capacity first last none).1,?_,rfl,
        finish_sound s capacity first last none hf hfm hn hl⟩
      simp only [describeLeader,hm,if_true,he,ho]
  | some next =>
    rw [he] at hn
    have hl:=Tree.pred_correct s.occurrences capacity next hi.occGood hi.occFits hc
    cases ho : (Tree.pred s.occurrences capacity next).1 with
    | none =>
      rw [ho] at hl
      have hh:=hl first hfm
      have hfnext:=hn.2.1
      omega
    | some last =>
      rw [ho] at hl
      refine ⟨(finish s.occurrences capacity first last (some next)).1,?_,rfl,
        finish_sound s capacity first last (some next) hf hfm hn hl⟩
      simp only [describeLeader,hm,if_true,he,ho]

theorem describeLeader_sound (s : MaskedClusterLeaders.State h) (capacity length first : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h) (d : Descriptor)
    (hd : (describeLeader s capacity first).1=some d) : d.first=first ∧ Sound s capacity d := by
  have hf : first∈s.leaders.entries := by
    cases hm : (Tree.contains s.leaders capacity first).1 with
    | false => simp only [describeLeader,hm,Bool.false_eq_true,if_false,reduceCtorEq] at hd
    | true => exact (Tree.contains_correct s.leaders capacity first hi.leadFits hc).mp hm
  obtain ⟨e,he,hef,hes⟩:=describeLeader_exists s capacity length first hi hc hf
  have heq : e=d := Option.some.inj (he.symm.trans hd)
  subst e
  exact ⟨hef,hes⟩

theorem Sound.locate_interval (s : MaskedClusterLeaders.State h) (capacity length : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h) (d : Descriptor)
    (hd : Sound s capacity d) (p : Nat) (hp : p∈s.occurrences.entries)
    (hfirst : d.first≤p) (hlast : p≤d.last) : (locate s capacity p).1=some d.first := by
  apply (locate_correct s capacity length p d.first hi hc).mpr
  refine ⟨hp,hd.firstLeader,hfirst,?_⟩
  intro q hq hqp
  by_cases hqf : q≤d.first
  · exact hqf
  · have hn:=hd.nextSpec
    have hl:=hd.lastSpec
    cases he : d.next with
    | none => rw [he] at hn; exact hn q hq
    | some next =>
      rw [he] at hn hl
      have hh:=hn.2.2 q hq (by omega)
      have hb:=hl.2.1
      omega

theorem locate_descriptor (s : MaskedClusterLeaders.State h) (capacity length first : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h) (d : Descriptor)
    (hd : (describeLeader s capacity first).1=some d) (p : Nat)
    (hp : p∈s.occurrences.entries) (hfirst : d.first≤p) (hlast : p≤d.last) :
    (locate s capacity p).1=some first := by
  obtain ⟨he,hs⟩:=describeLeader_sound s capacity length first hi hc d hd
  rw [←he]
  exact hs.locate_interval s capacity length hi hc d p hp hfirst hlast

theorem locate_none_outside (s : MaskedClusterLeaders.State h) (capacity length p first : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h) (d : Descriptor)
    (hd : (describeLeader s capacity first).1=some d) (hn : (locate s capacity p).1=none) :
    ¬(p∈s.occurrences.entries ∧ d.first≤p ∧ p≤d.last) := by
  rintro ⟨hp,hf,hl⟩
  have hh:=locate_descriptor s capacity length first hi hc d hd p hp hf hl
  rw [hn] at hh
  cases hh

/-- The first occurrence is always a leader. This existence proof only
reads the cached-minimum specification; it adds no query traversal. -/
theorem leader_before (s : MaskedClusterLeaders.State h) (length p : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hp : p∈s.occurrences.entries) :
    ∃first,first∈s.leaders.entries ∧ first≤p := by
  have hs:=Tree.first_spec s.occurrences 0 hi.occGood hi.occFits
  cases he : s.occurrences.first with
  | none =>
    rw [he] at hs
    change s.occurrences.entries=[] at hs
    rw [hs] at hp
    cases hp
  | some first =>
    rw [he] at hs
    refine ⟨first,(hi.represented first).mpr ⟨hs.1,?_⟩,hs.2 p hp⟩
    intro q hq hqf
    have hh:=hs.2 q hq
    omega

theorem locate_exists (s : MaskedClusterLeaders.State h) (capacity length p : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h)
    (hp : p∈s.occurrences.entries) : ∃first,(locate s capacity p).1=some first := by
  obtain ⟨first,hf,hfp⟩:=leader_before s length p hi hp
  have hm:=(Tree.contains_correct s.occurrences capacity p hi.occFits hc).mpr hp
  have hs:=Tree.pred_correct s.leaders capacity (p+1) hi.leadGood hi.leadFits hc
  cases he : (Tree.pred s.leaders capacity (p+1)).1 with
  | none =>
    rw [he] at hs
    have hh:=hs first hf
    omega
  | some q =>
    exact ⟨q,by simp only [locate,hm,if_true,he]⟩

theorem locate_none_iff (s : MaskedClusterLeaders.State h) (capacity length p : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h) :
    (locate s capacity p).1=none ↔ p∉s.occurrences.entries := by
  constructor
  · intro hn hp
    obtain ⟨first,hf⟩:=locate_exists s capacity length p hi hc hp
    rw [hn] at hf
    cases hf
  · intro hn
    cases he : (locate s capacity p).1 with
    | none => rfl
    | some first => exact False.elim (hn ((locate_correct s capacity length p first hi hc).mp he).1)

theorem Sound.owns_iff (s : MaskedClusterLeaders.State h) (capacity length : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (p : Nat) :
    Owns s p d.first ↔ p∈s.occurrences.entries ∧ d.first≤p ∧ p≤d.last := by
  constructor
  · intro hp
    refine ⟨hp.1,hp.2.2.1,?_⟩
    have hn:=hd.nextSpec
    have hl:=hd.lastSpec
    cases he : d.next with
    | none =>
      rw [he] at hl
      exact hl.2 p hp.1
    | some next =>
      rw [he] at hn hl
      have hpn : p<next := by
        by_cases hh : next≤p
        · have hb:=hp.2.2.2 next hn.1 hh
          have hf:=hn.2.1
          omega
        · omega
      exact hl.2.2 p hp.1 hpn
  · rintro ⟨hp,hf,hl⟩
    exact (locate_correct s capacity length p d.first hi hc).mp
      (hd.locate_interval s capacity length hi hc d p hp hf hl)

theorem describe_sound (s : MaskedClusterLeaders.State h) (capacity length p : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h)
    (d : Descriptor) (hd : (describe s capacity p).1=some d) :
    Sound s capacity d ∧ p∈s.occurrences.entries ∧ d.first≤p ∧ p≤d.last := by
  cases he : (locate s capacity p).1 with
  | none => simp only [describe,he,reduceCtorEq] at hd
  | some first =>
    simp only [describe,he] at hd
    obtain ⟨hf,hs⟩:=describeLeader_sound s capacity length first hi hc d hd
    have hp:=(locate_correct s capacity length p first hi hc).mp he
    rw [←hf] at hp
    exact ⟨hs,(hs.owns_iff s capacity length hi hc d p).mp hp⟩

theorem describe_exists (s : MaskedClusterLeaders.State h) (capacity length p : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h)
    (hp : p∈s.occurrences.entries) : ∃d,(describe s capacity p).1=some d := by
  obtain ⟨first,hf⟩:=locate_exists s capacity length p hi hc hp
  have ho:=(locate_correct s capacity length p first hi hc).mp hf
  obtain ⟨d,hd,_,_⟩:=describeLeader_exists s capacity length first hi hc ho.2.1
  exact ⟨d,by simp only [describe,hf,hd]⟩

theorem describe_none_iff (s : MaskedClusterLeaders.State h) (capacity length p : Nat)
    (hi : MaskedClusterLeaders.Invariant length s) (hc : capacity=2^h) :
    (describe s capacity p).1=none ↔ p∉s.occurrences.entries := by
  constructor
  · intro hn hp
    obtain ⟨d,hd⟩:=describe_exists s capacity length p hi hc hp
    rw [hn] at hd
    cases hd
  · intro hn
    have hh:=(locate_none_iff s capacity length p hi hc).mpr hn
    simp only [describe,hh]

end REWB.MaskedClusterDescriptor
