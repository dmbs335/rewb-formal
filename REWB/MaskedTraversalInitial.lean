import REWB.MaskedTraversalAnswers
import REWB.MaskedPeriodicBatchCost

/-! Actual initialization of the all-start traversal. Empty captures and
the enumerated periodic branch are solved once, unioned into a physical
bitmap, and removed once from the prepared mutable source batch. The
immutable target mask is shared by both solvers. No witness list, run
list, or answer oracle is supplied to this entry point.

`accountedWork` retains the explicit component-ledger scope of the
periodic solver; it is not a complete matcher running-time theorem.
-/
namespace REWB.MaskedTraversalInitial
open MaskedProgression (readMask)
variable {σ : Nat}

def unionBits (n : Nat) (left right : Array Bool) : Array Bool :=
  Array.ofFn (fun p : Fin n=>readMask left p.val || readMask right p.val)

theorem union_size (n : Nat) (left right : Array Bool) : (unionBits n left right).size=n :=
  Array.size_ofFn

theorem union_read (n : Nat) (left right : Array Bool) (hl : left.size=n) (hr : right.size=n) (p : Nat) :
    readMask (unionBits n left right) p=true ↔ readMask left p=true ∨ readMask right p=true := by
  by_cases hp : p<n
  · simp only [unionBits,readMask,Array.getElem?_ofFn,dif_pos hp,Option.getD_some,Bool.or_eq_true]
  · have hleft : left.size≤p := by omega
    have hright : right.size≤p := by omega
    have hout : (unionBits n left right).size≤p := by rw [union_size]; omega
    simp only [readMask,Array.getElem?_eq_none hout,Array.getElem?_eq_none hleft,
      Array.getElem?_eq_none hright,Option.getD_none,Bool.false_eq_true,false_or]

def periodicUnits (out : MaskedPeriodic.Batch.Result) : Nat :=
  out.output.queryWork+out.output.scanWork+out.output.preparationWork+out.enumerationWork+out.indexProducts

structure Result where
  empty : MaskedEmpty.Result
  periodic : MaskedPeriodic.Batch.Result
  answers : MaskedTraversalAnswers.State
  sources : MaskedMutableProgression.Batch.State
  accountedWork : Nat

def start (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) : Result :=
  let empty:=MaskedEmpty.solve B C E text.toList source target
  let periodic:=MaskedPeriodic.Batch.solve B C E text fallback source target
  let bits:=unionBits (text.size+1) empty.answers periodic.output.hits
  let answers:=MaskedTraversalAnswers.fromBits bits
  let sources:=MaskedMutableProgression.Batch.run text fallback source K answers.history
  ⟨empty,periodic,answers,sources,
    empty.work+periodicUnits periodic+answers.work+12*(text.size+1)+sources.totalWork⟩

def Handled (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (target : Array Bool) (p : Nat) : Prop :=
  MaskedEmpty.Witness B C E text.toList target p ∨ MaskedPeriodic.Batch.Covered B C E text fallback target p

theorem start_size (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) :
    (start B C E text fallback source target K).answers.bits.size=text.size+1 :=
  union_size _ _ _

theorem start_read (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K p : Nat) :
    readMask (start B C E text fallback source target K).answers.bits p=true ↔
      readMask source p=true ∧ Handled B C E text fallback target p := by
  have hs : (MaskedEmpty.solve B C E text.toList source target).answers.size=text.size+1 := by
    simpa only [Array.length_toList] using MaskedEmpty.solve_size B C E text.toList source target
  change readMask (unionBits _ _ _) p=true ↔ _
  rw [union_read _ _ _ hs (MaskedPeriodic.Batch.solve_size B C E text fallback source target),
    MaskedEmpty.solve_correct,MaskedPeriodic.Batch.solve_correct]
  unfold Handled
  constructor
  · rintro (⟨hm,he⟩|⟨hm,hp⟩)
    · exact ⟨hm,Or.inl he⟩
    · exact ⟨hm,Or.inr hp⟩
  · rintro ⟨hm,he|hp⟩
    · exact Or.inl ⟨hm,he⟩
    · exact Or.inr ⟨hm,hp⟩

theorem start_history (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K p : Nat) :
    p∈(start B C E text fallback source target K).answers.history ↔
      readMask source p=true ∧ Handled B C E text fallback target p := by
  change p∈MaskedEmpty.SourceBatch.positions _ ↔ _
  rw [MaskedEmpty.SourceBatch.positions_mem]
  exact start_read B C E text fallback source target K p

theorem handled_sound (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (target : Array Bool) (p : Nat) (hp : Handled B C E text fallback target p) :
    Spec.maskedStart B C E text.toList (readMask target) p := by
  rcases hp with he|hp
  · exact MaskedEmpty.witness_sound B C E text.toList target p he
  · exact MaskedPeriodic.Batch.covered_sound B C E text fallback target p hp

theorem start_answers_valid (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) :
    MaskedTraversalAnswers.Valid text.size
      (fun p=>readMask source p=true ∧ Spec.maskedStart B C E text.toList (readMask target) p)
      (start B C E text fallback source target K).answers := by
  apply MaskedTraversalAnswers.fromBits_valid text.size _ _ (union_size _ _ _)
  intro p hp
  have hh:=(start_read B C E text fallback source target K p).mp hp
  exact ⟨hh.1,handled_sound B C E text fallback target p hh.2⟩

theorem start_count (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) :
    (start B C E text fallback source target K).answers.count≤text.size+1 :=
  (start_answers_valid B C E text fallback source target K).count_le

theorem start_valid (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (hK : 0<K) :
    MaskedMutableProgression.Batch.Valid source (start B C E text fallback source target K).answers.history
      (start B C E text fallback source target K).sources :=
  MaskedMutableProgression.Batch.run_valid text fallback source K hK _

theorem start_n (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) : (start B C E text fallback source target K).sources.n=text.size :=
  MaskedMutableProgression.Batch.eraseMany_n _ _

theorem start_modulus (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) : (start B C E text fallback source target K).sources.modulus=K :=
  MaskedMutableProgression.Batch.eraseMany_modulus _ _

theorem start_runs (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) : (start B C E text fallback source target K).sources.runs=
      (MaskedMutableProgression.Batch.prepare text fallback source K).runs :=
  MaskedMutableProgression.Batch.eraseMany_runs _ _

theorem start_current (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K p : Nat) :
    MaskedMutableProgression.Batch.Current source (start B C E text fallback source target K).answers.history p ↔
      readMask source p=true ∧ ¬Handled B C E text fallback target p := by
  unfold MaskedMutableProgression.Batch.Current
  rw [start_history]
  constructor
  · rintro ⟨hs,hn⟩
    exact ⟨hs,fun hp=>hn ⟨hs,hp⟩⟩
  · rintro ⟨hs,hn⟩
    exact ⟨hs,fun hp=>hn hp.2⟩

theorem start_member (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (hK : 0<K) (p : Nat) :
    (MaskedMutableProgression.member (start B C E text fallback source target K).sources.singleton p).1=true ↔
      p≤text.size ∧ readMask source p=true ∧ ¬Handled B C E text fallback target p := by
  have hh:=MaskedMutableProgression.Batch.run_member text fallback source K hK
    (start B C E text fallback source target K).answers.history p
  change (MaskedMutableProgression.member (start B C E text fallback source target K).sources.singleton p).1=true ↔
    p≤text.size ∧ MaskedMutableProgression.Batch.Current source
      (start B C E text fallback source target K).answers.history p at hh
  rwa [start_current] at hh

theorem start_partition (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K p : Nat) :
    (readMask source p=true ∧ Spec.maskedStart B C E text.toList (readMask target) p) ↔
      readMask (start B C E text fallback source target K).answers.bits p=true ∨
        (MaskedMutableProgression.Batch.Current source (start B C E text fallback source target K).answers.history p ∧
          MaskedEmpty.PositiveWitness B C E text.toList target p) := by
  rw [start_read,start_current]
  constructor
  · rintro ⟨hs,hm⟩
    by_cases hh : Handled B C E text fallback target p
    · exact Or.inl ⟨hs,hh⟩
    · have hp:=(MaskedEmpty.maskedStart_partition B C E text.toList target p).mp hm
      exact Or.inr ⟨⟨hs,hh⟩,hp.resolve_left (fun he=>hh (Or.inl he))⟩
  · rintro (⟨hs,hh⟩|⟨⟨hs,_⟩,hp⟩)
    · exact ⟨hs,handled_sound B C E text fallback target p hh⟩
    · exact ⟨hs,(MaskedEmpty.maskedStart_partition B C E text.toList target p).mpr (Or.inr hp)⟩

end REWB.MaskedTraversalInitial
