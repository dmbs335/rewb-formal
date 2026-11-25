import REWB.MaskedClusterCursorCorrect

/-! Singleton cursor rows. Incoming overshoot has already passed the
    sole occurrence, so that row can only read to the next boundary.
    The normal row chooses its actual point jump's output mode from the
    certified H/L overlap equivalence. No periodicity premise is used.
-/
namespace REWB.MaskedCluster
open REWB.Spec
variable {α : Type}

def preparePointRow (C E : DFA α) (ci : BoundaryApplication.Range.Index C)
    (ei : BoundaryApplication.Range.Index E) (s H next incoming : Nat)
    (enabled mode : Bool) : Option (RowContext C E)×Nat :=
  if modeAllowed enabled mode then
    let I:=cursor s incoming mode
    let pass:=passContext C E ci ei I next
    let normal:=if !mode && !overMode s 1 0 H next then
      let out:=pointContexts C E ci ei I s H next
      (some out.maps,out.work+1)
      else (none,1)
    let over:=if !mode && overMode s 1 0 H next then
      let out:=pointContexts C E ci ei I s H (s+H)
      (some out.maps,out.work+1)
      else (none,1)
    (some ⟨s,1,I,0,0,s,pass.maps,normal.1,over.1⟩,pass.work+normal.2+over.2+8)
  else (none,1)

def pointRowCell (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : MaskedProgression.Answer :=
  match ctx with
  | none => ⟨false,0,1⟩
  | some ctx =>
    if outMode then
      match ctx.over with
      | none => ⟨false,0,1⟩
      | some maps => filteredPointCell C E maps tail source target ctx.last window input output
    else
      let pass:=passCell C E ctx.pass input output
      match ctx.normal with
      | none => pass
      | some maps => either pass (filteredPointCell C E maps tail source target ctx.last window input output)

theorem pointRowCell_normal (C E : DFA α)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s H next incoming : Nat) (enabled mode : Bool) (h : modeAllowed enabled mode=true)
    (tail : Replay C E) (source target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    pointRowCell C E (preparePointRow C E ci ei s H next incoming enabled mode).1
      tail source target window false input output=
      if !mode && !overMode s 1 0 H next then
        either (passCell C E (passContext C E ci ei (cursor s incoming mode) next).maps input output)
          (filteredPointCell C E (pointContexts C E ci ei (cursor s incoming mode) s H next).maps
            tail source target s window input output)
      else passCell C E (passContext C E ci ei (cursor s incoming mode) next).maps input output := by
  by_cases hn : (!mode && !overMode s 1 0 H next)=true <;>
    simp only [preparePointRow,h,hn,if_true,if_false,pointRowCell,Bool.false_eq_true]

theorem pointRowCell_over (C E : DFA α)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s H next incoming : Nat) (enabled mode : Bool) (h : modeAllowed enabled mode=true)
    (tail : Replay C E) (source target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    pointRowCell C E (preparePointRow C E ci ei s H next incoming enabled mode).1
      tail source target window true input output=
      if !mode && overMode s 1 0 H next then
        filteredPointCell C E (pointContexts C E ci ei (cursor s incoming mode) s H (s+H)).maps
          tail source target s window input output
      else ⟨false,0,1⟩ := by
  by_cases ho : (!mode && overMode s 1 0 H next)=true <;>
    simp only [preparePointRow,h,ho,if_true,if_false,pointRowCell,Bool.false_eq_true]

theorem exists_le_zero (P : Nat→Prop) : (∃ k,k≤0 ∧ P k) ↔ P 0 := by
  constructor
  · rintro ⟨k,hk,h⟩
    have he : k=0 := by omega
    simpa only [he] using h
  · exact fun h=>⟨0,Nat.le_refl _,h⟩

/-- q=1 is only a coordinate convention when m=0: the sole physical
    candidate is s. This statement assumes no unary text periodicity. -/
theorem pointRowCell_correct (C E : DFA α) (w : Word α) (fallback : α)
    (classBase L : Nat) (copies : List Nat) (s H next incoming : Nat) (previous following : Option Nat)
    (enabled inMode outMode : Bool) (source target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies s next previous following H)
    (hsep : s<next) (hnext : next≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (pointRowCell C E
      (preparePointRow C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s H next incoming enabled inMode).1
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) s L H).maps
      source target window outMode input output).answer=true ↔
        CursorStep C E w s 1 0 L H next incoming enabled inMode outMode source target window input output := by
  by_cases ha : modeAllowed enabled inMode=true
  · have hLH:=cert.current
    have hbound:=cert.lastBound
    cases inMode with
    | true =>
      have he:=((modeAllowed_iff enabled true).mp ha) rfl
      have hi:=hin he
      have hnot : ¬incoming≤s := by omega
      cases outMode with
      | false =>
        rw [pointRowCell_normal C E _ _ s H next incoming enabled true ha]
        simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,if_false,cursor,if_true]
        rw [passCell_correct C E w incoming next input output hi.2 hnext]
        simp only [CursorStep,ha,true_and,Bool.false_eq_true,if_false,cursor,if_true,
          exists_le_zero,Nat.zero_mul,Nat.add_zero,hnot,false_and,or_false]
      | true =>
        rw [pointRowCell_over C E _ _ s H next incoming enabled true ha]
        simp only [Bool.not_true,Bool.false_and,Bool.false_eq_true,if_false,CursorStep,ha,true_and,
          if_true,exists_le_zero,cursor,Nat.zero_mul,Nat.add_zero,hnot,false_and]
    | false =>
      have hI : s≤s := Nat.le_refl _
      by_cases ho : next<s+H
      · have hoL:=cert.overlap.mp ho
        have hov : overMode s 1 0 H next=true := by
          simp only [overMode,Nat.zero_mul,Nat.add_zero,ho,decide_true]
        have hnot : ¬s+L≤next := by omega
        cases outMode with
        | false =>
          rw [pointRowCell_normal C E _ _ s H next incoming enabled false ha]
          simp only [hov,Bool.not_false,Bool.not_true,Bool.true_and,Bool.false_eq_true,if_false,cursor]
          rw [passCell_correct C E w s next input output (Nat.le_of_lt hsep) hnext]
          simp only [CursorStep,ha,true_and,Bool.false_eq_true,if_false,exists_le_zero,cursor,
            Nat.zero_mul,Nat.add_zero,Nat.le_refl,hnot,false_and,and_false,or_false]
        | true =>
          rw [pointRowCell_over C E _ _ s H next incoming enabled false ha]
          simp only [hov,Bool.not_false,Bool.true_and,if_true,cursor,Bool.false_eq_true,if_false]
          rw [filteredPointCell_direct C E w s s s L H (s+H) source target window input output
            hI hLH (Nat.le_refl _) hbound hbound rfl]
          simp only [CursorStep,ha,true_and,if_true,exists_le_zero,cursor,Bool.false_eq_true,if_false,
            Nat.zero_mul,Nat.add_zero,Nat.le_refl,hoL,JumpAt]
      · have hHO : s+H≤next := by omega
        have hLO : s+L≤next := by omega
        have hnot : ¬next<s+L := by omega
        have hov : overMode s 1 0 H next=false := by
          simp only [overMode,Nat.zero_mul,Nat.add_zero,ho,decide_false]
        cases outMode with
        | false =>
          rw [pointRowCell_normal C E _ _ s H next incoming enabled false ha]
          simp only [hov,Bool.not_false,Bool.true_and,if_true,cursor,Bool.false_eq_true,if_false]
          rw [either_answer,passCell_correct C E w s next input output (Nat.le_of_lt hsep) hnext,
            filteredPointCell_direct C E w s s s L H next source target window input output
              hI hLH hHO hnext hbound rfl]
          simp only [CursorStep,ha,true_and,Bool.false_eq_true,if_false,exists_le_zero,cursor,
            Nat.zero_mul,Nat.add_zero,Nat.le_refl,hLO,JumpAt]
        | true =>
          rw [pointRowCell_over C E _ _ s H next incoming enabled false ha]
          simp only [hov,Bool.not_false,Bool.true_and,Bool.false_eq_true,if_false,CursorStep,ha,true_and,
            if_true,exists_le_zero,cursor,Nat.zero_mul,Nat.add_zero,Nat.le_refl,hnot,false_and]
  · simp only [preparePointRow,ha,Bool.false_eq_true,if_false,pointRowCell,CursorStep,false_and]

def pointRowMatrix (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (window : SourceWindow) : CursorRow (MaskedClusterStage.dfa C E).stateCount :=
  ⟨materialize (fun i j=>pointRowCell C E ctx tail source target window false
      (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)),
    materialize (fun i j=>pointRowCell C E ctx tail source target window true
      (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j))⟩

theorem pointRowMatrix_get (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (window : SourceWindow) (mode : Bool)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    ((((pointRowMatrix C E ctx tail source target window).get mode).cells.get i).get j)=
      (pointRowCell C E ctx tail source target window mode
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)).answer := by
  cases mode <;> exact materialize_get _ _ _

end REWB.MaskedCluster
