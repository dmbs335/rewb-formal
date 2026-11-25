import REWB.ShortOuterBandInsert

/-! Every actual first-copy end query writes its original-coordinate
Boolean cell, and subsequent queries preserve previously written cells.
The statement still uses the exact key and suffix arrays; the final
slice theorem is established separately. -/
namespace REWB.ShortOuter.Band
open REWB.BoundaryApplication
open REWB.Spec (slice)
variable {σ : Nat}

def Answer (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (p len : Nat) : Prop :=
  ∃k,marks keys suffix (p+len) (Keys.get keys p len) k ∧ G.accepts (slice w (p+len) k)

def BitsGood (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (floor : Nat) (bits : Array Bool) : Prop :=
  bits.size=(keys.length+1)*keys.width ∧
  ∀p len,len<keys.width → p+len≤keys.length → floor≤p+len →
    (bits[p*keys.width+len]?.getD false=true ↔ Answer G w keys suffix p len)

def Partial (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x cut : Nat) (bits : Array Bool) : Prop :=
  bits.size=(keys.length+1)*keys.width ∧
  ∀p len,len<keys.width → p+len≤keys.length → (x<p+len ∨ (x=p+len ∧ cut≤len)) →
    (bits[p*keys.width+len]?.getD false=true ↔ Answer G w keys suffix p len)

theorem slot_injective (width p q len other : Nat) (hl : len<width) (ho : other<width)
    (he : p*width+len=q*width+other) : p=q ∧ len=other := by
  have hd:=congrArg (fun i=>i/width) he
  have hm:=congrArg (fun i=>i%width) he
  dsimp only at hd hm
  rw [Keys.slot_div _ _ _ hl,Keys.slot_div _ _ _ ho] at hd
  rw [Keys.slot_mod _ _ _ hl,Keys.slot_mod _ _ _ ho] at hm
  exact ⟨hd,hm⟩

theorem probeOne_good (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (marked : Nat→Nat→Prop) (x len : Nat) (st : State G.stateCount)
    (hk : KeyBound keys) (hx : x≤keys.length) (hl : len<keys.width)
    (hsize : st.cells.size=keys.registry.next) (hgood : Sweep.Good G w marked x st.cells) :
    Sweep.Good G w marked x (probeOne G (Range.build G w) keys x len st).cells := by
  cases st with
  | mk cells bits touches work =>
    simp only [probeOne]
    split
    · apply (Sweep.update_good G w marked x (Keys.get keys (x-len) len) false cells
        (by rw [hsize]; exact hk _ _ (by omega) hl) hgood).congr
      intro r p
      simp [Sweep.added]
    · exact hgood

theorem probes_good (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (marked : Nat→Nat→Prop) (x count : Nat) (st : State G.stateCount)
    (hk : KeyBound keys) (hx : x≤keys.length) (hc : count≤keys.width)
    (hsize : st.cells.size=keys.registry.next) (hgood : Sweep.Good G w marked x st.cells) :
    Sweep.Good G w marked x (probes G (Range.build G w) keys x count st).cells := by
  induction count generalizing st with
  | zero => exact hgood
  | succ count ih =>
    rw [probes]
    exact ih _ (by omega) (by simpa using hsize)
      (probeOne_good G w keys marked x count st hk hx (by omega) hsize hgood)

theorem probeOne_partial (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x len : Nat) (st : State G.stateCount)
    (hk : KeyBound keys) (hx : x≤keys.length) (hl : len<keys.width)
    (hsize : st.cells.size=keys.registry.next) (hgood : Sweep.Good G w (marks keys suffix x) x st.cells)
    (hb : Partial G w keys suffix x (len+1) st.bits) :
    Partial G w keys suffix x len (probeOne G (Range.build G w) keys x len st).bits := by
  refine ⟨by rw [probeOne_bits_size]; exact hb.1,?_⟩
  intro p ell hell hp he
  cases st with
  | mk cells bits touches work =>
    simp only [probeOne]
    split
    · rename_i hle
      rw [Array.getElem?_setIfInBounds]
      by_cases hslot : (x-len)*keys.width+len=p*keys.width+ell
      · obtain ⟨hpx,hellen⟩:=slot_injective keys.width (x-len) p len ell hl hell hslot
        rw [if_pos hslot,if_pos (by rw [hb.1]; exact Keys.slot_bound _ _ _ _ (by omega) hl)]
        have hv:=Sweep.update_value G w (marks keys suffix x) x (Keys.get keys (x-len) len) false cells
          (by rw [hsize]; exact hk _ _ (by omega) hl) hgood
        simp only [Sweep.added,Bool.false_eq_true,false_and,or_false] at hv
        have hxlen : x-len+len=x := by omega
        rw [←hpx,←hellen]
        simpa only [Answer,hxlen] using hv
      · rw [if_neg hslot]
        apply hb.2 p ell hell hp
        rcases he with he|⟨he,hcut⟩
        · exact Or.inl he
        · right
          refine ⟨he,?_⟩
          by_cases heq : len=ell
          · have hpx : x-len=p := by omega
            exact False.elim (hslot (by rw [hpx,heq]))
          · omega
    · rename_i hle
      apply hb.2 p ell hell hp
      rcases he with he|⟨he,hcut⟩
      · exact Or.inl he
      · exact Or.inr ⟨he,by omega⟩

theorem probes_partial (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x count : Nat) (st : State G.stateCount)
    (hk : KeyBound keys) (hx : x≤keys.length) (hc : count≤keys.width)
    (hsize : st.cells.size=keys.registry.next) (hgood : Sweep.Good G w (marks keys suffix x) x st.cells)
    (hb : Partial G w keys suffix x count st.bits) :
    Partial G w keys suffix x 0 (probes G (Range.build G w) keys x count st).bits := by
  induction count generalizing st with
  | zero => exact hb
  | succ count ih =>
    rw [probes]
    exact ih _ (by omega) (by simpa using hsize)
      (probeOne_good G w keys _ x count st hk hx (by omega) hsize hgood)
      (probeOne_partial G w keys suffix x count st hk hx (by omega) hsize hgood hb)

theorem probes_stage (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x : Nat) (st : State G.stateCount)
    (hk : KeyBound keys) (hx : x≤keys.length) (hsize : st.cells.size=keys.registry.next)
    (hgood : Sweep.Good G w (marks keys suffix x) x st.cells)
    (hb : BitsGood G w keys suffix (x+1) st.bits) :
    BitsGood G w keys suffix x (probes G (Range.build G w) keys x keys.width st).bits := by
  have hp : Partial G w keys suffix x keys.width st.bits := by
    refine ⟨hb.1,?_⟩
    intro p len hl hpn he
    exact hb.2 p len hl hpn (by rcases he with he|⟨_,he⟩ <;> omega)
  have hh:=probes_partial G w keys suffix x keys.width st hk hx (Nat.le_refl _) hsize hgood hp
  refine ⟨hh.1,?_⟩
  intro p len hl hpn he
  apply hh.2 p len hl hpn
  by_cases hstrict : x<p+len
  · exact Or.inl hstrict
  · exact Or.inr ⟨by omega,Nat.zero_le _⟩

theorem probeOne_bounds (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (marked : Nat→Nat→Prop) (x len : Nat) (st : State G.stateCount)
    (hk : KeyBound keys) (hx : x≤keys.length) (hl : len<keys.width)
    (hsize : st.cells.size=keys.registry.next) (hgood : Sweep.Good G w marked x st.cells) :
    (probeOne G (Range.build G w) keys x len st).touches≤st.touches+1 ∧
    (probeOne G (Range.build G w) keys x len st).work≤
      st.work+Sweep.stepBudget G.stateCount w.length+9 := by
  cases st with
  | mk cells bits touches work =>
    simp only [probeOne]
    split
    · have hh:=Sweep.update_work G w marked x (Keys.get keys (x-len) len) false cells
        (by rw [hsize]; exact hk _ _ (by omega) hl) hgood
      exact ⟨Nat.le_refl _,by dsimp only; omega⟩
    · exact ⟨by dsimp only; omega,by dsimp only; omega⟩

theorem probes_bounds (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (marked : Nat→Nat→Prop) (x count : Nat) (st : State G.stateCount)
    (hk : KeyBound keys) (hx : x≤keys.length) (hc : count≤keys.width)
    (hsize : st.cells.size=keys.registry.next) (hgood : Sweep.Good G w marked x st.cells) :
    (probes G (Range.build G w) keys x count st).touches≤st.touches+count ∧
    (probes G (Range.build G w) keys x count st).work≤
      st.work+count*(Sweep.stepBudget G.stateCount w.length+9) := by
  induction count generalizing st with
  | zero => simp [probes]
  | succ count ih =>
    rw [probes]
    have hg:=probeOne_good G w keys marked x count st hk hx (by omega) hsize hgood
    have hb:=probeOne_bounds G w keys marked x count st hk hx (by omega) hsize hgood
    have hh:=ih _ (by omega) (by simpa using hsize) hg
    rw [Nat.add_mul,Nat.one_mul]
    exact ⟨by omega,by omega⟩

end REWB.ShortOuter.Band
