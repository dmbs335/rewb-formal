import REWB.MaskedTraversalCompleteWindow

/-! A ghost owner key records the source bank after the first jump.
One bank performs at most one jump, so a suffix state certifies two
strictly ordered real owner keys. This strengthens physical soundness
without changing the runtime bank representation. -/
namespace REWB.MaskedTraversalComplete
open REWB.Spec REWB.MaskedCluster REWB.MaskedTraversalAggregate
variable {α : Type}

def Tracked (C E : DFA α) (w : Word α) (L cursor : Nat)
    (owner : Nat→Nat) (source target : Nat→Prop) (bound : Nat→Prop) :
    MaskedClusterStage.State C.stateCount E.stateCount→Prop
  | .waiting=>True
  | .gap q=>∃p,source p ∧ bound (owner p) ∧ p+L≤cursor ∧ C.run C.initial (slice w (p+L) cursor)=q
  | .suffix q=>∃p j,source p ∧ target j ∧ owner p<owner j ∧ p+L≤j ∧ j+L≤cursor ∧
      C.accepts (slice w (p+L) j) ∧ E.run E.initial (slice w (j+L) cursor)=q

theorem tracked_weaken (C E : DFA α) (w : Word α) (L cursor : Nat)
    (owner : Nat→Nat) (source target : Nat→Prop) (a b : Nat→Prop)
    (state : MaskedClusterStage.State C.stateCount E.stateCount)
    (hb : ∀x,a x→b x) (hs : Tracked C E w L cursor owner source target a state) :
    Tracked C E w L cursor owner source target b state := by
  cases state with
  | waiting=>trivial
  | gap q=>obtain ⟨p,hp,hb',hn,hq⟩:=hs; exact ⟨p,hp,hb _ hb',hn,hq⟩
  | suffix q=>exact hs

theorem tracked_read (C E : DFA α) (w : Word α) (L I O : Nat)
    (owner : Nat→Nat) (source target : Nat→Prop) (bound : Nat→Prop)
    (s : MaskedClusterStage.State C.stateCount E.stateCount)
    (hIO : I≤O) (hs : Tracked C E w L I owner source target bound s) :
    Tracked C E w L O owner source target bound (MaskedClusterStage.read C E (slice w I O) s) := by
  cases s with
  | waiting=>trivial
  | gap q=>
    obtain ⟨p,hp,hb,hpI,hq⟩:=hs
    refine ⟨p,hp,hb,Nat.le_trans hpI hIO,?_⟩
    rw [OuterColumn.slice_split w (p+L) I O hpI hIO,DFA.run_append,hq]
  | suffix q=>
    obtain ⟨p,j,hp,hj,hkeys,hpj,hjI,hC,hq⟩:=hs
    refine ⟨p,j,hp,hj,hkeys,hpj,Nat.le_trans hjI hIO,hC,?_⟩
    rw [OuterColumn.slice_split w (j+L) I O hjI hIO,DFA.run_append,hq]

theorem tracked_jump (C E : DFA α) (w : Word α) (L p key : Nat)
    (owner : Nat→Nat) (source target : Nat→Prop) (sourceBit targetBit : Bool)
    (s t : MaskedClusterStage.State C.stateCount E.stateCount)
    (hs : Tracked C E w L p owner source target (fun x=>x<key) s)
    (hsource : sourceBit=true→source p) (htarget : targetBit=true→target p) (hkey : owner p=key)
    (hj : MaskedClusterStage.jump C E sourceBit targetBit s=some t) :
    Tracked C E w L (p+L) owner source target (fun x=>x≤key) t := by
  cases s with
  | waiting=>
    simp only [MaskedClusterStage.jump] at hj
    split at hj
    next h=>
      cases Option.some.inj hj
      exact ⟨p,hsource h,by rw [hkey]; exact Nat.le_refl _,Nat.le_refl _,by simp only [OuterColumn.slice_self,DFA.run]⟩
    next h=>cases hj
  | gap q=>
    obtain ⟨i,hi,howner,hip,hq⟩:=hs
    simp only [MaskedClusterStage.jump] at hj
    split at hj
    next h=>
      cases Option.some.inj hj
      have hh : targetBit=true ∧ C.final q=true := by simpa only [Bool.and_eq_true] using h
      refine ⟨i,p,hi,htarget hh.1,by rw [hkey]; exact howner,hip,Nat.le_refl _,?_,?_⟩
      · change C.final (C.run C.initial (slice w (i+L) p))=true
        rw [hq]; exact hh.2
      · simp only [OuterColumn.slice_self,DFA.run]
    next h=>cases hj
  | suffix q=>cases hj

theorem tracked_direct (C E : DFA α) (w : Word α) (L I p O key : Nat)
    (owner : Nat→Nat) (source target : Nat→Prop) (sourceBit targetBit : Bool)
    (s t : MaskedClusterStage.State C.stateCount E.stateCount)
    (hIp : I≤p) (hpO : p+L≤O) (hs : Tracked C E w L I owner source target (fun x=>x<key) s)
    (hsource : sourceBit=true→source p) (htarget : targetBit=true→target p) (hkey : owner p=key)
    (hj : MaskedClusterStage.direct C E w I p L O sourceBit targetBit s=some t) :
    Tracked C E w L O owner source target (fun x=>x≤key) t := by
  unfold MaskedClusterStage.direct at hj
  cases hx : MaskedClusterStage.jump C E sourceBit targetBit (MaskedClusterStage.read C E (slice w I p) s) with
  | none=>simp only [hx,Option.map_none] at hj; cases hj
  | some u=>
    simp only [hx,Option.map_some] at hj
    rw [←Option.some.inj hj]
    exact tracked_read C E w L (p+L) O owner source target _ u hpO
      (tracked_jump C E w L p key owner source target sourceBit targetBit _ u
        (tracked_read C E w L I p owner source target _ s hIp hs) hsource htarget hkey hx)

theorem tracked_cursor (C E : DFA α) (w : Word α) (s q m L H next incoming key : Nat)
    (enabled inMode outMode : Bool) (sourceMask : Array Bool) (removed : List Nat)
    (targetMask : Array Bool) (window : SourceWindow) (owner : Nat→Nat) (source target : Nat→Prop)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hLH : L≤H) (henter : cursor s incoming inMode≤next)
    (hsources : ∀k,k≤m→window.allows (s+k*q)=true→Mutable.Batch.currentBit sourceMask removed (s+k*q)=true→source (s+k*q))
    (htargets : ∀k,k≤m→MaskedProgression.readMask targetMask (s+k*q)=true→target (s+k*q))
    (hkeys : ∀k,k≤m→owner (s+k*q)=key)
    (hs : Tracked C E w L (cursor s incoming inMode) owner source target (fun x=>x<key) input)
    (step : Mutable.Batch.CursorStep C E w s q m L H next incoming enabled inMode outMode
      sourceMask removed targetMask window input output) :
    Tracked C E w L (outputCursor s q m H next outMode) owner source target (fun x=>x≤key) output := by
  have step':=step.2
  cases outMode with
  | false=>
    simp only [Bool.false_eq_true,if_false] at step'
    change Tracked C E w L next owner source target (fun x=>x≤key) output
    rcases step' with pass|⟨k,hk,hI,hO,hjump⟩
    · rw [←pass]
      exact tracked_weaken C E w L next owner source target _ _ _ (fun _ hh=>Nat.le_of_lt hh)
        (tracked_read C E w L _ next owner source target _ input henter hs)
    · exact tracked_direct C E w L _ _ next key owner source target _ _ input output hI hO hs
        (by intro h; have hh:=Bool.and_eq_true_iff.mp h; exact hsources k hk hh.1 hh.2)
        (htargets k hk) (hkeys k hk) hjump
  | true=>
    simp only [if_true] at step'
    change Tracked C E w L (s+m*q+H) owner source target (fun x=>x≤key) output
    obtain ⟨k,hk,hI,_,hjump⟩:=step'
    have hm:=Nat.mul_le_mul_right q hk
    exact tracked_direct C E w L _ _ (s+m*q+H) key owner source target _ _ input output hI (by omega) hs
      (by intro h; have hh:=Bool.and_eq_true_iff.mp h; exact hsources k hk hh.1 hh.2)
      (htargets k hk) (hkeys k hk) hjump

theorem tracked_chain (C E : DFA α) (w : Word α) (L : Nat)
    (sourceMask : Array Bool) (removed : List Nat) (targetMask : Array Bool)
    (owner : Nat→Nat) (source target : Nat→Prop) (parts : List Part) (entryAt finish : Bool→Nat)
    (continuous : Continuous w.length parts entryAt finish)
    (ordered : parts.Pairwise (fun p q=>p.config.descriptor.first<q.config.descriptor.first))
    (safe : ∀p,p∈parts→Safe w.length L p)
    (marks : ∀p,p∈parts→Marks sourceMask removed targetMask source target p)
    (owners : ∀p,p∈parts→∀k,k≤p.config.descriptor.repetitions→owner (position p k)=p.config.descriptor.first)
    (bound : Nat→Prop) (lower : ∀x,bound x→∀p,p∈parts→x<p.config.descriptor.first)
    (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount))
    (path : PhysicalChain C E w L sourceMask removed targetMask parts i j)
    (initial : Tracked C E w L (entryAt (codeMode _ i)) owner source target bound (decoded C E i)) :
    Tracked C E w L (finish (codeMode _ j)) owner source target (fun _=>True) (decoded C E j) := by
  induction continuous generalizing bound i with
  | nil entryAt=>
    change i=j at path
    subst j
    exact tracked_weaken C E w L _ owner source target _ _ _ (fun _ _=>True.intro) initial
  | cons p ps entryAt finish entry rest ih=>
    obtain ⟨mid,step,tail⟩:=path
    have hp:=safe p List.mem_cons_self
    have hm:=marks p List.mem_cons_self
    have ho:=owners p List.mem_cons_self
    have enabled : modeAllowed p.config.incomingEnabled (codeMode _ i)=true := step.1
    have start : Tracked C E w L (p.input (codeMode _ i)) owner source target
        (fun x=>x<p.config.descriptor.first) (decoded C E i) := by
      rw [entry _ enabled]
      exact tracked_weaken C E w L _ owner source target _ _ _ (fun x hx=>lower x hx p List.mem_cons_self) initial
    have next:=tracked_cursor C E w p.config.descriptor.first p.config.descriptor.period
      p.config.descriptor.repetitions L p.config.anchor (p.config.descriptor.nextAt w.length)
      p.config.incoming p.config.descriptor.first p.config.incomingEnabled (codeMode _ i) (codeMode _ mid)
      sourceMask removed targetMask (p.config.window.gate p.gate) owner source target
      (decoded C E i) (decoded C E mid) hp.1 (hp.2 _ enabled) hm.1 hm.2 ho start step
    have hord:=List.pairwise_cons.mp ordered
    exact ih hord.2 (fun q hq=>safe q (List.mem_cons_of_mem p hq))
      (fun q hq=>marks q (List.mem_cons_of_mem p hq))
      (fun q hq=>owners q (List.mem_cons_of_mem p hq)) (fun x=>x≤p.config.descriptor.first)
      (fun x hx q hq=>Nat.lt_of_le_of_lt hx (hord.1 q hq)) mid tail next

theorem tracked_final (C E : DFA α) (w : Word α) (L : Nat)
    (sourceMask : Array Bool) (removed : List Nat) (targetMask : Array Bool)
    (owner : Nat→Nat) (source target : Nat→Prop) (parts : List Part) (entryAt finish : Bool→Nat)
    (continuous : Continuous w.length parts entryAt finish) (endAt : finish false=w.length)
    (ordered : parts.Pairwise (fun p q=>p.config.descriptor.first<q.config.descriptor.first))
    (safe : ∀p,p∈parts→Safe w.length L p)
    (marks : ∀p,p∈parts→Marks sourceMask removed targetMask source target p)
    (owners : ∀p,p∈parts→∀k,k≤p.config.descriptor.repetitions→owner (position p k)=p.config.descriptor.first)
    (q : Fin E.stateCount) (hf : E.final q=true)
    (path : PhysicalChain C E w L sourceMask removed targetMask parts
      (stageCode C E false .waiting) (stageCode C E false (.suffix q))) :
    ∃p j,source p ∧ target j ∧ owner p<owner j ∧ p+L≤j ∧ j+L≤w.length ∧
      C.accepts (slice w (p+L) j) ∧ E.accepts (slice w (j+L) w.length) := by
  have hh:=tracked_chain C E w L sourceMask removed targetMask owner source target parts entryAt finish
    continuous ordered safe marks owners (fun _=>False) (fun _ hh=>False.elim hh) _ _ path
    (by simp only [stageCode,decoded,codeState_code,MaskedClusterStage.decode_encode,Tracked])
  simp only [stageCode,decoded,codeState_code,MaskedClusterStage.decode_encode,codeMode_code,endAt,Tracked] at hh
  obtain ⟨p,j,hp,hj,hkeys,hpj,hjn,hC,hq⟩:=hh
  refine ⟨p,j,hp,hj,hkeys,hpj,hjn,hC,?_⟩
  change E.final (E.run E.initial (slice w (j+L) w.length))=true
  rw [hq]; exact hf

end REWB.MaskedTraversalComplete
