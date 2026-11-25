import REWB.MaskedClusterMutableBatchCorrect
import REWB.Specifications

/-! Physical meaning of chronological cursor paths. These predicates and
their endpoint witnesses are proof-only: a matrix query never enumerates
them. Reading preserves the stage, and each real jump advances it once.
In particular, a final suffix state certifies exactly two ordered copies.
-/
namespace REWB.MaskedTraversalAggregate
open REWB.Spec REWB.MaskedCluster
variable {α : Type}

def Meaning (C E : DFA α) (w : Word α) (L cursor : Nat)
    (source target : Nat→Prop) : MaskedClusterStage.State C.stateCount E.stateCount→Prop
  | .waiting => True
  | .gap q => ∃p,source p ∧ p+L≤cursor ∧ C.run C.initial (slice w (p+L) cursor)=q
  | .suffix q => ∃p j,source p ∧ target j ∧ p+L≤j ∧ j+L≤cursor ∧
      C.accepts (slice w (p+L) j) ∧ E.run E.initial (slice w (j+L) cursor)=q

theorem meaning_read (C E : DFA α) (w : Word α) (L I O : Nat)
    (source target : Nat→Prop) (s : MaskedClusterStage.State C.stateCount E.stateCount)
    (hIO : I≤O) (hs : Meaning C E w L I source target s) :
    Meaning C E w L O source target (MaskedClusterStage.read C E (slice w I O) s) := by
  cases s with
  | waiting => trivial
  | gap q =>
    obtain ⟨p,hp,hpI,hq⟩:=hs
    refine ⟨p,hp,Nat.le_trans hpI hIO,?_⟩
    rw [OuterColumn.slice_split w (p+L) I O hpI hIO,DFA.run_append,hq]
  | suffix q =>
    obtain ⟨p,j,hp,hj,hpj,hjI,hC,hq⟩:=hs
    refine ⟨p,j,hp,hj,hpj,Nat.le_trans hjI hIO,hC,?_⟩
    rw [OuterColumn.slice_split w (j+L) I O hjI hIO,DFA.run_append,hq]

theorem meaning_jump (C E : DFA α) (w : Word α) (L p : Nat)
    (source target : Nat→Prop) (sourceBit targetBit : Bool)
    (s t : MaskedClusterStage.State C.stateCount E.stateCount)
    (hs : Meaning C E w L p source target s)
    (hsource : sourceBit=true→source p) (htarget : targetBit=true→target p)
    (hj : MaskedClusterStage.jump C E sourceBit targetBit s=some t) :
    Meaning C E w L (p+L) source target t := by
  cases s with
  | waiting =>
    simp only [MaskedClusterStage.jump] at hj
    split at hj
    next h =>
      cases Option.some.inj hj
      exact ⟨p,hsource h,Nat.le_refl _,by simp only [OuterColumn.slice_self,DFA.run]⟩
    next h => cases hj
  | gap q =>
    obtain ⟨i,hi,hip,hq⟩:=hs
    simp only [MaskedClusterStage.jump] at hj
    split at hj
    next h =>
      cases Option.some.inj hj
      have hh : targetBit=true ∧ C.final q=true := by simpa only [Bool.and_eq_true] using h
      obtain ⟨ht,hf⟩:=hh
      refine ⟨i,p,hi,htarget ht,hip,Nat.le_refl _,?_,?_⟩
      · change C.final (C.run C.initial (slice w (i+L) p))=true
        rw [hq]
        exact hf
      · simp only [OuterColumn.slice_self,DFA.run]
    next h => cases hj
  | suffix q => cases hj

theorem meaning_direct (C E : DFA α) (w : Word α) (L I p O : Nat)
    (source target : Nat→Prop) (sourceBit targetBit : Bool)
    (s t : MaskedClusterStage.State C.stateCount E.stateCount)
    (hIp : I≤p) (hpO : p+L≤O) (hs : Meaning C E w L I source target s)
    (hsource : sourceBit=true→source p) (htarget : targetBit=true→target p)
    (hj : MaskedClusterStage.direct C E w I p L O sourceBit targetBit s=some t) :
    Meaning C E w L O source target t := by
  unfold MaskedClusterStage.direct at hj
  cases hx : MaskedClusterStage.jump C E sourceBit targetBit
      (MaskedClusterStage.read C E (slice w I p) s) with
  | none => simp only [hx,Option.map_none] at hj; cases hj
  | some u =>
    simp only [hx,Option.map_some] at hj
    have he:=Option.some.inj hj
    rw [←he]
    exact meaning_read C E w L (p+L) O source target u hpO
      (meaning_jump C E w L p source target sourceBit targetBit _ u
        (meaning_read C E w L I p source target s hIp hs) hsource htarget hx)

def outputCursor (s q m H next : Nat) (mode : Bool) : Nat :=
  if mode then s+m*q+H else next

/-- The AP is a genuine class, source history is current, and targets
remain immutable. The only path hypothesis is the literal CursorStep. -/
theorem meaning_cursor (C E : DFA α) (w : Word α) (s q m L H next incoming : Nat)
    (enabled inMode outMode : Bool) (sourceMask : Array Bool) (removed : List Nat)
    (targetMask : Array Bool) (window : SourceWindow) (source target : Nat→Prop)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hLH : L≤H) (henter : cursor s incoming inMode≤next)
    (hsources : ∀k,k≤m→window.allows (s+k*q)=true→
      Mutable.Batch.currentBit sourceMask removed (s+k*q)=true→source (s+k*q))
    (htargets : ∀k,k≤m→MaskedProgression.readMask targetMask (s+k*q)=true→target (s+k*q))
    (hs : Meaning C E w L (cursor s incoming inMode) source target input)
    (step : Mutable.Batch.CursorStep C E w s q m L H next incoming enabled inMode outMode
      sourceMask removed targetMask window input output) :
    Meaning C E w L (outputCursor s q m H next outMode) source target output := by
  have step':=step.2
  cases outMode with
  | false =>
    simp only [Bool.false_eq_true,if_false] at step'
    change Meaning C E w L next source target output
    rcases step' with pass|⟨k,hk,hI,hO,hjump⟩
    · rw [←pass]
      exact meaning_read C E w L _ next source target input henter hs
    · exact meaning_direct C E w L _ _ next source target _ _ input output hI hO hs
        (by
          intro h
          have hh : window.allows (s+k*q)=true ∧ Mutable.Batch.currentBit sourceMask removed (s+k*q)=true := by
            simpa only [Bool.and_eq_true] using h
          exact hsources k hk hh.1 hh.2)
        (htargets k hk) hjump
  | true =>
    simp only [if_true] at step'
    change Meaning C E w L (s+m*q+H) source target output
    obtain ⟨k,hk,hI,_,hjump⟩:=step'
    have hm:=Nat.mul_le_mul_right q hk
    exact meaning_direct C E w L _ _ (s+m*q+H) source target _ _ input output hI (by omega) hs
      (by
          intro h
          have hh : window.allows (s+k*q)=true ∧ Mutable.Batch.currentBit sourceMask removed (s+k*q)=true := by
            simpa only [Bool.and_eq_true] using h
          exact hsources k hk hh.1 hh.2)
      (htargets k hk) hjump

theorem meaning_final (C E : DFA α) (w : Word α) (L : Nat)
    (source target : Nat→Prop) (state : MaskedClusterStage.State C.stateCount E.stateCount)
    (hs : Meaning C E w L w.length source target state)
    (hf : MaskedClusterStage.final E state=true) :
    ∃p j,source p ∧ target j ∧ p+L≤j ∧ j+L≤w.length ∧
      C.accepts (slice w (p+L) j) ∧ E.accepts (slice w (j+L) w.length) := by
  cases state with
  | waiting => cases hf
  | gap q => cases hf
  | suffix q =>
    obtain ⟨p,j,hp,hj,hpj,hjn,hC,hq⟩:=hs
    refine ⟨p,j,hp,hj,hpj,hjn,hC,?_⟩
    change E.final (E.run E.initial (slice w (j+L) w.length))=true
    rw [hq]
    exact hf

end REWB.MaskedTraversalAggregate
