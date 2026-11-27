import REWB.MaskedPeriodicTextLocal

/-! Transport the periodic-accessor compiler to slices of one finite
    input word. A witness includes the actual equality of its two copies,
    disjointness, and the unchanged absolute-position target mask.
-/
namespace REWB.MaskedPeriodic.Text
open REWB.Periodic REWB.Spec
open REWB.P2Periodic (factor)
variable {α : Type}

theorem segment_slice (w : Word α) (fallback : α) (s L : Nat)
    (h : s+L≤w.length) :
    segment (shift (ArrayText.read w.toArray fallback) s) 0 L=slice w s (s+L) := by
  have hh := ArrayText.shifted_factor w fallback s 0 L (Nat.zero_le _) h
  simpa only [factor,Nat.sub_zero,Nat.add_zero] using hh

theorem phase_families (b c e : DFA α) (w tail : Word α) (fallback : α)
    (s eta q N : Nat) (mask : Array Bool) (base len : Nat)
    (he : eta<q) (hn : s+q≤w.length) :
    PhaseWitness b c e w tail s eta q N mask base len s ↔
      FamilyWitness b c e (shift (ArrayText.read w.toArray fallback) s)
        tail q N eta mask base len s := by
  have hw := segment_slice w fallback s q hn
  have ht := segment_slice w fallback s eta (by omega)
  constructor
  · rintro (⟨a,k,hf,hm⟩|⟨rho,a,k,hr0,hr,hf,hm⟩|⟨rho,a,k,hr0,hr,hf,hm⟩)
    · exact Or.inl ⟨a,k,by simpa only [localFamily,hw,ht] using hf,hm⟩
    · have hp := segment_slice w fallback s rho (by omega)
      have hs := ArrayText.shifted_factor w fallback s rho q (by omega) hn
      exact Or.inr (Or.inl ⟨rho,a,k,hr0,hr,
        by simpa only [localFamily,hw,ht,hp,hs] using hf,hm⟩)
    · have hp := segment_slice w fallback s rho (by omega)
      have hs := ArrayText.shifted_factor w fallback s rho q (by omega) hn
      have hs' := ArrayText.shifted_factor w fallback s rho eta hr (by omega)
      exact Or.inr (Or.inr ⟨rho,a,k,hr0,hr,
        by simpa only [localFamily,hw,hp,hs,hs'] using hf,hm⟩)
  · rintro (⟨a,k,hf,hm⟩|⟨rho,a,k,hr0,hr,hf,hm⟩|⟨rho,a,k,hr0,hr,hf,hm⟩)
    · exact Or.inl ⟨a,k,by simpa only [localFamily,hw,ht] using hf,hm⟩
    · have hp := segment_slice w fallback s rho (by omega)
      have hs := ArrayText.shifted_factor w fallback s rho q (by omega) hn
      exact Or.inr (Or.inl ⟨rho,a,k,hr0,hr,
        by simpa only [localFamily,hw,ht,hp,hs] using hf,hm⟩)
    · have hp := segment_slice w fallback s rho (by omega)
      have hs := ArrayText.shifted_factor w fallback s rho q (by omega) hn
      have hs' := ArrayText.shifted_factor w fallback s rho eta hr (by omega)
      exact Or.inr (Or.inr ⟨rho,a,k,hr0,hr,
        by simpa only [localFamily,hw,hp,hs,hs'] using hf,hm⟩)

/-- The physical text witness. Both capture copies lie in [s,R),
    the gap and suffix are the actual intervening slices, and all mask
    reads use absolute text positions. `tail=[]` is the in-run query;
    `tail=w.drop R` gives acceptance of the complete input suffix. -/
def Witness (b c e : DFA α) (w tail : Word α) (s R q : Nat)
    (mask : Array Bool) (base len : Nat) : Prop :=
  ∃ L k,2*q≤L ∧ s+L≤s+k*q ∧ s+k*q+L≤R ∧
    slice w s (s+L)=slice w (s+k*q) (s+k*q+L) ∧
    b.accepts (slice w s (s+L)) ∧
    c.accepts (slice w (s+L) (s+k*q)) ∧
    e.accepts (slice w (s+k*q+L) R++tail) ∧
    Marked mask base len q s k

theorem actual_equal_copies (w : Word α) (fallback : α) (s R q L k : Nat)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q)
    (hn : R≤w.length) (hb : s+k*q+L≤R) :
    slice w s (s+L)=slice w (s+k*q) (s+k*q+L) := by
  have hper := (RunGeometry.on_iff _ s R q).mp hp
  have heq := equal_copies (shift (ArrayText.read w.toArray fallback) s) (R-s) q k L
    hper (by omega)
  rw [ArrayText.shifted_factor w fallback s 0 L (by omega) (by omega),
    ArrayText.shifted_factor w fallback s (k*q) (k*q+L) (by omega) (by omega)] at heq
  simpa only [Nat.add_zero,Nat.add_assoc] using heq

theorem local_witness_iff (b c e : DFA α) (w tail : Word α) (fallback : α)
    (s R q : Nat) (mask : Array Bool) (base len : Nat)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q)
    (hs : s≤R) (hn : R≤w.length) :
    LocalWitness b c e (shift (ArrayText.read w.toArray fallback) s) tail q (R-s)
      mask base len s ↔ Witness b c e w tail s R q mask base len := by
  have hend : s+(R-s)=R := by omega
  constructor
  · rintro ⟨L,k,hl,hd,hbound,hf,hm⟩
    have hb : s+k*q+L≤R := by omega
    have hc := ArrayText.shifted_factor w fallback s 0 L (by omega) (by omega)
    have hg := ArrayText.shifted_factor w fallback s L (k*q) hd (by omega)
    have ht := ArrayText.shifted_factor w fallback s (k*q+L) (R-s) hbound (by omega)
    refine ⟨L,k,hl,by omega,hb,actual_equal_copies w fallback s R q L k hp hn hb,?_,?_,?_,hm⟩
    · simpa only [Nat.add_zero,hc] using hf.1
    · simpa only [hg] using hf.2.1
    · simpa only [ht,hend,Nat.add_assoc] using hf.2.2
  · rintro ⟨L,k,hl,hd,hbound,_,hb,hc,he,hm⟩
    have hc' := ArrayText.shifted_factor w fallback s 0 L (by omega) (by omega)
    have hg := ArrayText.shifted_factor w fallback s L (k*q) (by omega) (by omega)
    have ht := ArrayText.shifted_factor w fallback s (k*q+L) (R-s) (by omega) (by omega)
    refine ⟨L,k,hl,by omega,by omega,?_,hm⟩
    refine ⟨?_,?_,?_⟩
    · simpa only [hc',Nat.add_zero] using hb
    · simpa only [hg] using hc
    · simpa only [ht,hend,Nat.add_assoc] using he

end REWB.MaskedPeriodic.Text
