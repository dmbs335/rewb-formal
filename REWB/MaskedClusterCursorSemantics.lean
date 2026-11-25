import REWB.MaskedClusterCursor

/-! Physical semantics for cursor blocks: normal output either reads
    without a jump or makes one eligible real L-skip; overshoot output
    makes one skip crossing the next boundary. Source reporting gates
    only the source bit. These predicates contain no compiled answers.
-/
namespace REWB.MaskedCluster
open REWB.Spec
variable {α : Type}

theorem normal_indices (s q m L H next incoming k : Nat) (enabled mode : Bool)
    (hq : 0<q) (hLH : L≤H) (hp : s+(m-1)*q+H≤next)
    (hover : (next<s+m*q+H ↔ next<s+m*q+L))
    (ha : modeAllowed enabled mode=true) (hin : enabled=true→s<incoming ∧ incoming≤s+q) :
    (lower mode≤k ∧ k≤normalHi s q m H next) ↔
      k≤m ∧ cursor s incoming mode≤s+k*q ∧ s+k*q+L≤next := by
  have hc:=cursor_candidate s q incoming k enabled mode hq ha hin
  have he:=normal_current s q m L H next k hLH hp hover
  constructor
  · rintro ⟨hl,hh⟩
    obtain ⟨hk,hend⟩:=he.mpr hh
    exact ⟨hk,hc.mpr hl,hend⟩
  · rintro ⟨hk,hstart,hend⟩
    exact ⟨hc.mp hstart,he.mp ⟨hk,hend⟩⟩

theorem normal_window (s q m L H next incoming base len : Nat) (enabled mode : Bool)
    (P : Nat→Prop) (hq : 0<q) (hH : 0<H) (hLH : L≤H) (hp : s+(m-1)*q+H≤next)
    (hover : (next<s+m*q+H ↔ next<s+m*q+L))
    (ha : modeAllowed enabled mode=true) (hin : enabled=true→s<incoming ∧ incoming≤s+q)
    (hbase : base≤s) (hend : s+m*q+H≤base+len) :
    (∃ k,lower mode≤k ∧ k≤normalHi s q m H next ∧ base≤s+k*q ∧ s+k*q<base+len ∧ P k) ↔
      ∃ k,k≤m ∧ cursor s incoming mode≤s+k*q ∧ s+k*q+L≤next ∧ P k := by
  constructor
  · rintro ⟨k,hl,hh,_,_,hP⟩
    obtain ⟨hk,hstart,hend⟩:=(normal_indices s q m L H next incoming k enabled mode hq hLH hp hover ha hin).mp ⟨hl,hh⟩
    exact ⟨k,hk,hstart,hend,hP⟩
  · rintro ⟨k,hk,hstart,hend',hP⟩
    obtain ⟨hl,hh⟩:=(normal_indices s q m L H next incoming k enabled mode hq hLH hp hover ha hin).mpr ⟨hk,hstart,hend'⟩
    have hmul:=Nat.mul_le_mul_right q hk
    exact ⟨k,hl,hh,by omega,by omega,hP⟩

theorem overshoot_single (s q m L H next incoming : Nat) (enabled mode : Bool) (P : Nat→Prop)
    (hm : 0<m) (hLH : L≤H) (hp : s+(m-1)*q+H≤next)
    (hover : (next<s+m*q+H ↔ next<s+m*q+L))
    (ha : modeAllowed enabled mode=true) (hin : enabled=true→s<incoming ∧ incoming≤s+q)
    (ho : overMode s q m H next=true) :
    P m ↔ ∃ k,k≤m ∧ cursor s incoming mode≤s+k*q ∧ next<s+k*q+L ∧ P k := by
  constructor
  · intro hP
    have hi:=cursor_before_last s q m incoming enabled mode hm ha hin
    have hh:=(overshoot_current s q m L H next m hLH hp hover).mpr ⟨ho,rfl⟩
    exact ⟨m,Nat.le_refl _,hi,hh.2,hP⟩
  · rintro ⟨k,hk,_,hend,hP⟩
    have he:=((overshoot_current s q m L H next k hLH hp hover).mp ⟨hk,hend⟩).2
    simpa only [he] using hP

def JumpAt (C E : DFA α) (w : Word α) (I s q L O : Nat)
    (source target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) (k : Nat) : Prop :=
  MaskedClusterStage.direct C E w I (s+k*q) L O
    (window.allows (s+k*q) && MaskedProgression.readMask source (s+k*q))
    (MaskedProgression.readMask target (s+k*q)) input=some output

def CursorStep (C E : DFA α) (w : Word α) (s q m L H next incoming : Nat)
    (enabled inMode outMode : Bool) (source target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Prop :=
  modeAllowed enabled inMode=true ∧
    if outMode then
      ∃ k,k≤m ∧ cursor s incoming inMode≤s+k*q ∧ next<s+k*q+L ∧
        JumpAt C E w (cursor s incoming inMode) s q L (s+m*q+H) source target window input output k
    else
      MaskedClusterStage.read C E (slice w (cursor s incoming inMode) next) input=output ∨
      ∃ k,k≤m ∧ cursor s incoming inMode≤s+k*q ∧ s+k*q+L≤next ∧
        JumpAt C E w (cursor s incoming inMode) s q L next source target window input output k

end REWB.MaskedCluster
