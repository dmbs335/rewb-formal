import REWB.MaskedTraversalCompleteStep

/-! A constructive pass through any chronological list of real cursor
interfaces. Empty lists preserve the incoming mode; a nonempty pass
returns to normal mode after its first cluster. -/
namespace REWB.MaskedTraversalComplete
open REWB.Spec REWB.MaskedCluster REWB.MaskedTraversalAggregate
variable {α : Type}

def Admitted : List Part→Bool→Prop
  | [],_=>True
  | p::_,mode=>modeAllowed p.config.incomingEnabled mode=true

theorem admitted_false (parts : List Part) : Admitted parts false := by
  cases parts <;> simp [Admitted,modeAllowed]

def finishMode : List Part→Bool→Bool
  | [],mode=>mode
  | _::_,_=>false

@[simp] theorem finishMode_false (parts : List Part) : finishMode parts false=false := by cases parts <;> rfl

theorem pass_chain (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool)
    (parts : List Part) (entryAt finish : Bool→Nat)
    (continuous : Continuous w.length parts entryAt finish)
    (safe : ∀p,p∈parts→Safe w.length L p)
    (mode : Bool) (admitted : Admitted parts mode)
    (state : MaskedClusterStage.State C.stateCount E.stateCount) :
    entryAt mode≤finish (finishMode parts mode) ∧
      PhysicalChain C E w L source removed target parts (stageCode C E mode state)
        (stageCode C E (finishMode parts mode)
          (MaskedClusterStage.read C E (slice w (entryAt mode) (finish (finishMode parts mode))) state)) := by
  induction continuous generalizing mode state with
  | nil entryAt =>
    simp only [finishMode,OuterColumn.slice_self,MaskedClusterStage.read_nil,PhysicalChain]
    exact ⟨Nat.le_refl _,True.intro⟩
  | cons p ps entryAt finish entry rest ih =>
    have ha : modeAllowed p.config.incomingEnabled mode=true := admitted
    have he:=entry mode ha
    have hI : entryAt mode≤p.output w.length false := by
      rw [←he]
      exact (safe p List.mem_cons_self).2 mode ha
    let middle:=MaskedClusterStage.read C E (slice w (entryAt mode) (p.output w.length false)) state
    have tail:=ih (fun q hq=>safe q (List.mem_cons_of_mem p hq)) false (admitted_false ps) middle
    simp only [finishMode_false] at tail
    have hp:=pass_step C E w L source removed target p mode state ha
    rw [he] at hp
    have hread : MaskedClusterStage.read C E (slice w (p.output w.length false) (finish false)) middle=
        MaskedClusterStage.read C E (slice w (entryAt mode) (finish false)) state := by
      dsimp only [middle]
      rw [←MaskedClusterStage.read_append,←OuterColumn.slice_split w (entryAt mode)
        (p.output w.length false) (finish false) hI tail.1]
    rw [hread] at tail
    exact ⟨Nat.le_trans hI tail.1,stageCode C E false middle,hp,tail.2⟩

theorem continuous_split (n : Nat) (a b : List Part) (entryAt finish : Bool→Nat)
    (hc : Continuous n (a++b) entryAt finish) :
    ∃middle,Continuous n a entryAt middle ∧ Continuous n b middle finish := by
  induction a generalizing entryAt with
  | nil => exact ⟨entryAt,Continuous.nil entryAt,hc⟩
  | cons p ps ih =>
    cases hc with
    | cons _ _ _ _ entry rest =>
      obtain ⟨middle,hleft,hright⟩:=ih _ rest
      exact ⟨middle,Continuous.cons p ps entryAt middle entry hleft,hright⟩

def Enabled (n : Nat) : List Part→Prop
  | []=>True
  | p::ps=>(∀q,ps.head?=some q→p.output n false<p.output n true→q.config.incomingEnabled=true) ∧ Enabled n ps

theorem enabled_append_right (n : Nat) (a b : List Part) (he : Enabled n (a++b)) : Enabled n b := by
  induction a with
  | nil => exact he
  | cons p ps ih => exact ih he.2

theorem admitted_jump (n L : Nat) (p : Part) (ps : List Part) (k : Nat)
    (he : Enabled n (p::ps)) (hk : k≤p.config.descriptor.repetitions) (hL : L≤p.config.anchor) :
    Admitted ps (jumpMode n L p k) := by
  cases ps with
  | nil => trivial
  | cons q qs =>
    by_cases ho : p.config.descriptor.nextAt n<p.config.descriptor.first+k*p.config.descriptor.period+L
    · have hm:=Nat.mul_le_mul_right p.config.descriptor.period hk
      have hO : p.output n false<p.output n true := by
        simp only [Part.output,outputCursor,Bool.false_eq_true,if_false,if_true]
        omega
      have hq:=he.1 q rfl hO
      simp only [Admitted,jumpMode,ho,decide_true,modeAllowed,Bool.not_true,Bool.false_or,hq]
    · simp only [jumpMode,ho,decide_false]
      exact admitted_false (q::qs)

theorem jump_after (n L : Nat) (p : Part) (k : Nat)
    (hk : k≤p.config.descriptor.repetitions) (hL : L≤p.config.anchor) :
    p.config.descriptor.first+k*p.config.descriptor.period+L≤p.output n (jumpMode n L p k) := by
  have hm:=Nat.mul_le_mul_right p.config.descriptor.period hk
  by_cases ho : p.config.descriptor.nextAt n<p.config.descriptor.first+k*p.config.descriptor.period+L <;>
    simp only [jumpMode,ho,decide_true,decide_false,Part.output,outputCursor,Bool.false_eq_true,if_true,if_false] <;> omega

def Incoming (n : Nat) (p : Part) : Prop :=
  p.config.incomingEnabled=true→p.config.descriptor.first<p.config.incoming ∧
    p.config.incoming≤if p.config.descriptor.repetitions=0 then p.config.descriptor.nextAt n
      else p.config.descriptor.first+p.config.descriptor.period

theorem target_entry (n L : Nat) (p q : Part) (sourceIndex targetIndex : Nat)
    (ht : targetIndex≤q.config.descriptor.repetitions)
    (hn : q.input false=p.output n false) (hin : Incoming n q)
    (ha : Admitted [q] (jumpMode n L p sourceIndex))
    (horder : p.config.descriptor.first+sourceIndex*p.config.descriptor.period+L≤
      q.config.descriptor.first+targetIndex*q.config.descriptor.period) :
    q.input (jumpMode n L p sourceIndex)≤q.config.descriptor.first+targetIndex*q.config.descriptor.period := by
  by_cases ho : p.config.descriptor.nextAt n<p.config.descriptor.first+sourceIndex*p.config.descriptor.period+L
  · have en : q.config.incomingEnabled=true := by
      simpa only [Admitted,jumpMode,ho,decide_true,modeAllowed,Bool.not_true,Bool.false_or] using ha
    have hs : q.config.descriptor.first=p.config.descriptor.nextAt n := hn
    have hk : 0<targetIndex := by
      by_cases hz : targetIndex=0
      · simp only [hz,Nat.zero_mul,Nat.add_zero,hs] at horder
        omega
      · omega
    have hm : q.config.descriptor.repetitions≠0 := by omega
    have hi:=hin en
    rw [if_neg hm] at hi
    have hp:=Nat.mul_le_mul_right q.config.descriptor.period hk
    simp only [Nat.one_mul] at hp
    simp only [jumpMode,ho,decide_true,Part.input,cursor,if_true]
    omega
  · simp only [jumpMode,ho,decide_false,Part.input,cursor,Bool.false_eq_true,if_false]
    omega

end REWB.MaskedTraversalComplete
