import REWB.ShortOuterBandProbe

/-! Full correctness of the constructed short outer-copy band.  The
physical text, exact-key array, suffix DFA rows, range maps and complete
chronological event schedule are all constructed by `Band.build`. -/
namespace REWB.ShortOuter.Band
open REWB.BoundaryApplication REWB.Periodic
open REWB.Spec (slice)
variable {σ : Nat}

theorem run_correct (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (fuel : Nat) (st : State G.stateCount)
    (hk : KeyBound keys) (hf : fuel≤keys.length+1) (hsize : st.cells.size=keys.registry.next)
    (hgood : Sweep.Good G w (marks keys suffix fuel) (fuel-1) st.cells)
    (hb : BitsGood G w keys suffix fuel st.bits) :
    Sweep.Good G w (marks keys suffix 0) 0 (run G (Range.build G w) keys suffix fuel st).cells ∧
    BitsGood G w keys suffix 0 (run G (Range.build G w) keys suffix fuel st).bits := by
  induction fuel generalizing st with
  | zero => exact ⟨hgood,hb⟩
  | succ x ih =>
    rw [run]
    have hgi:=inserts_stage G w keys suffix x st hk (by omega) hsize hgood
    have hgp:=probes_good G w keys (marks keys suffix x) x keys.width
      (inserts G (Range.build G w) keys suffix x keys.width st) hk (by omega) (Nat.le_refl _)
      (by simpa using hsize) hgi
    have hbp:=probes_stage G w keys suffix x
      (inserts G (Range.build G w) keys suffix x keys.width st) hk (by omega)
      (by simpa using hsize) hgi (by simpa using hb)
    exact ih _ (by omega) (by simpa using hsize)
      (by simpa using hgp.weaken (show x-1≤x by omega)) (by simpa using hbp)

theorem initial_correct (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (hn : keys.length=w.length) :
    Sweep.Good G w (marks keys suffix (keys.length+1)) keys.length (initial G keys).cells ∧
    BitsGood G w keys suffix (keys.length+1) (initial G keys).bits := by
  constructor
  · change Sweep.Good G w _ keys.length (Sweep.initial G.stateCount keys.length keys.registry.next)
    have hh:=Sweep.initial_good G w keys.registry.next
    rw [←hn] at hh
    apply hh.congr
    intro r p
    constructor
    · exact False.elim
    · rintro ⟨hp,len,_,⟨hbound,_⟩,_⟩
      omega
  · refine ⟨by simp [initial],?_⟩
    intro p len _ hp he
    omega

@[simp] theorem build_keys (G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (build G H text fallback limit).keys=Keys.build text fallback limit := rfl

theorem build_bits_good (G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    BitsGood G text.toList (Keys.build text fallback limit) (Suffix.build H text).1 0
      (build G H text fallback limit).bits := by
  have hi:=initial_correct G text.toList (Keys.build text fallback limit) (Suffix.build H text).1
    (by simp only [Keys.build_length,Array.length_toList])
  exact (run_correct G text.toList (Keys.build text fallback limit) (Suffix.build H text).1
    (text.size+1) (initial G (Keys.build text fallback limit))
    (build_keyBound text fallback limit) (by simp only [Keys.build_length]; omega)
    (by simp [initial,Sweep.initial]) hi.1 hi.2).2

theorem answer_iff (G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p len : Nat) (hl : len<min limit (text.size+1)) (hp : p+len≤text.size) :
    Answer G text.toList (Keys.build text fallback limit) (Suffix.build H text).1 p len ↔
      ∃k,p+len≤k ∧ k+len≤text.size ∧
        slice text.toList p (p+len)=slice text.toList k (k+len) ∧
        G.accepts (slice text.toList (p+len) k) ∧
        H.accepts (slice text.toList (k+len) text.size) := by
  constructor
  · rintro ⟨k,⟨hpk,other,ho,⟨hkn,hH⟩,he⟩,hG⟩
    have heq:segment (ArrayText.read text fallback) p len=
        segment (ArrayText.read text fallback) k other :=
      (Keys.get_eq_general text fallback limit p k len other (by omega) (by
        change k+other≤text.size at hkn; omega) hl ho).mp he.symm
    have hlen:=congrArg List.length heq
    simp only [segment_length] at hlen
    subst other
    change k+len≤text.size at hkn
    refine ⟨k,hpk,hkn,?_,hG,(Suffix.get_correct H text (k+len) hkn).mp hH⟩
    simpa only [ArrayText.segment_read text fallback p len hp,
      ArrayText.segment_read text fallback k len hkn,slice,Nat.add_sub_cancel_left] using heq
  · rintro ⟨k,hpk,hkn,he,hG,hH⟩
    have heq:segment (ArrayText.read text fallback) p len=
        segment (ArrayText.read text fallback) k len := by
      simpa only [ArrayText.segment_read text fallback p len hp,
        ArrayText.segment_read text fallback k len hkn,slice,Nat.add_sub_cancel_left] using he
    exact ⟨k,⟨hpk,len,hl,⟨hkn,(Suffix.get_correct H text (k+len) hkn).mpr hH⟩,
      ((Keys.get_eq_iff text fallback limit p k len (by omega) (by omega) hl).mpr heq).symm⟩,hG⟩

/-- Every bounded short first copy has a materialized bit.  The second
copy is unrestricted to the right; the gap may be empty. -/
theorem get_correct (G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p len : Nat) (hl : len<limit) (hp : p+len≤text.size) :
    get (build G H text fallback limit) p len=true ↔
      ∃k,p+len≤k ∧ k+len≤text.size ∧
        slice text.toList p (p+len)=slice text.toList k (k+len) ∧
        G.accepts (slice text.toList (p+len) k) ∧
        H.accepts (slice text.toList (k+len) text.size) := by
  have hw : len<min limit (text.size+1) := by omega
  rw [get,if_pos (by simp only [build_keys,Keys.build_width,Keys.build_length]; exact ⟨hw,hp⟩)]
  exact ((build_bits_good G H text fallback limit).2 p len hw hp (Nat.zero_le _)).trans
    (answer_iff G H text fallback limit p len hw hp)

theorem get_iff (G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p len : Nat) :
    get (build G H text fallback limit) p len=true ↔
      len<limit ∧ p+len≤text.size ∧
      ∃k,p+len≤k ∧ k+len≤text.size ∧
        slice text.toList p (p+len)=slice text.toList k (k+len) ∧
        G.accepts (slice text.toList (p+len) k) ∧
        H.accepts (slice text.toList (k+len) text.size) := by
  by_cases hb : len<limit ∧ p+len≤text.size
  · rw [get_correct G H text fallback limit p len hb.1 hb.2]
    simp only [hb.1,hb.2,true_and]
  · have hg : ¬(len<(build G H text fallback limit).keys.width ∧
        p+len≤(build G H text fallback limit).keys.length) := by
      simp only [build_keys,Keys.build_width,Keys.build_length]
      omega
    simp only [get,if_neg hg,Bool.false_eq_true,false_iff]
    rintro ⟨hl,hp,_⟩
    exact hb ⟨hl,hp⟩

end REWB.ShortOuter.Band
