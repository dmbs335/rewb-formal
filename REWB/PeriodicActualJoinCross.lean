import REWB.PeriodicActualJoinCut

/-! Materialized chronological colors and actual formula/window
expansion at a join cut. Every replacement returns the entire original
CountedJoin batch result and a separately measured construction cost. -/
namespace REWB.PeriodicActual.Join
open REWB.PeriodicConstruction REWB.TimedJoin
variable {α : Type}

def sources (d : DFA α) (idx : DFACut.Index d) (es : List TimedEntry) : Result (List KeyedJoin.Entry) :=
  CountedProjection.map (fun e=>(TimedJoin.source d idx e,8)) es

theorem sources_value (d : DFA α) (idx : DFACut.Index d) (es : List TimedEntry) :
    (sources d idx es).1=TimedJoin.sources d idx es := by
  simp only [sources,CountedProjection.map_value,TimedJoin.sources]

theorem sources_work (d : DFA α) (idx : DFACut.Index d) (es : List TimedEntry) :
    (sources d idx es).2≤9*es.length+1 := by
  simpa only [sources,Nat.mul_comm] using
    map_bound (fun e : TimedEntry=>(TimedJoin.source d idx e,8)) es 8 (fun _ _=>Nat.le_refl _)

def target (d : DFA α) (idx : DFACut.Index d) (e : TimedEntry) : Result (List KeyedJoin.Entry) :=
  let states:=(FiniteRelation.finEnum d.stateCount).elems
  let kept:=CountedJoin.filter (fun q=>DFACut.rightAt d idx e.pos q) states
  let colored:=CountedProjection.map (fun q=>(TimedJoin.color d e.entry q,4)) kept.1
  (colored.1,d.stateCount+5*kept.2+colored.2+4)

theorem target_value (d : DFA α) (idx : DFACut.Index d) (e : TimedEntry) :
    (target d idx e).1=TimedJoin.target d idx e := by
  simp only [target,CountedProjection.map_value,CountedJoin.filter_value,TimedJoin.target]

theorem target_length (d : DFA α) (idx : DFACut.Index d) (e : TimedEntry) :
    (TimedJoin.target d idx e).length≤d.stateCount := by
  unfold TimedJoin.target
  rw [List.length_map]
  simpa only [FiniteRelation.finEnum,List.length_ofFn] using
    List.length_filter_le (fun q=>DFACut.rightAt d idx e.pos q) (FiniteRelation.finEnum d.stateCount).elems

theorem target_work (d : DFA α) (idx : DFACut.Index d) (e : TimedEntry) :
    (target d idx e).2≤20*d.stateCount+8 := by
  have hl:=List.length_filter_le (fun q=>DFACut.rightAt d idx e.pos q)
    (FiniteRelation.finEnum d.stateCount).elems
  simp only [FiniteRelation.finEnum,List.length_ofFn] at hl
  unfold target
  simp only [CountedProjection.map_plain_steps,CountedJoin.filter_value,CountedJoin.filter_steps,
    FiniteRelation.finEnum,List.length_ofFn]
  omega

def targets (d : DFA α) (idx : DFACut.Index d) (es : List TimedEntry) : Result (List KeyedJoin.Entry) :=
  CountedProjection.flatMap (target d idx) es

theorem targets_value (d : DFA α) (idx : DFACut.Index d) (es : List TimedEntry) :
    (targets d idx es).1=TimedJoin.targets d idx es := by
  simp only [targets,CountedProjection.flatMap_value,target_value,TimedJoin.targets]

theorem targets_work (d : DFA α) (idx : DFACut.Index d) (es : List TimedEntry) :
    (targets d idx es).2≤es.length*(21*d.stateCount+10)+1 := by
  have h:=flatMap_bound _ es (20*d.stateCount+8) d.stateCount
    (fun e _=>target_work d idx e)
    (fun e _=>by rw [target_value]; exact target_length d idx e)
  rw [show 20*d.stateCount+8+d.stateCount+2=21*d.stateCount+10 by omega] at h
  exact h

theorem targets_length (d : DFA α) (idx : DFACut.Index d) (es : List TimedEntry) :
    (TimedJoin.targets d idx es).length≤d.stateCount*es.length := by
  induction es with
  | nil=>simp only [TimedJoin.targets,List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.le_refl]
  | cons e es ih=>
    have hh:=target_length d idx e
    simp only [TimedJoin.targets,List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ] at *
    omega

def bounded (es : List TimedEntry) (bound : Nat) : Prop :=
  ∀e,e∈es→UniformProjection.measure e.entry.formula≤bound

theorem sources_bounded (d : DFA α) (idx : DFACut.Index d) (es : List TimedEntry) (bound : Nat)
    (h : bounded es bound) :
    ∀e,e∈TimedJoin.sources d idx es→UniformProjection.measure e.formula≤bound := by
  intro e he
  obtain ⟨f,hf,rfl⟩:=List.mem_map.mp he
  exact h f hf

theorem targets_bounded (d : DFA α) (idx : DFACut.Index d) (es : List TimedEntry) (bound : Nat)
    (h : bounded es bound) :
    ∀e,e∈TimedJoin.targets d idx es→UniformProjection.measure e.formula≤bound := by
  intro e he
  obtain ⟨f,hf,he⟩:=List.mem_flatMap.mp he
  obtain ⟨q,_,rfl⟩:=(TimedJoin.target_mem d idx f e).mp he
  exact h f hf

def keyed (K N : Nat) (es fs : List KeyedJoin.Entry) : Result CountedJoin.BatchResult :=
  let ⟨left,lwork⟩:=PeriodicConstruction.prepare K N es
  let ⟨right,rwork⟩:=PeriodicConstruction.prepare K N fs
  (CountedJoin.batch left right,lwork+rwork+4)

theorem keyed_value (K N : Nat) (es fs : List KeyedJoin.Entry) :
    (keyed K N es fs).1=CountedJoin.keyed K N es fs := by
  simp only [keyed,PeriodicConstruction.prepare_value,CountedJoin.keyed]

theorem keyed_work (K N : Nat) (es fs : List KeyedJoin.Entry) (bound : Nat)
    (he : ∀e,e∈es→UniformProjection.measure e.formula≤bound)
    (hf : ∀f,f∈fs→UniformProjection.measure f.formula≤bound) :
    (keyed K N es fs).2≤(es.length+fs.length)*(41*K*(bound+1)+7)+6 := by
  have hl:=PeriodicConstruction.prepare_work K N es bound he
  have hr:=PeriodicConstruction.prepare_work K N fs bound hf
  unfold keyed
  dsimp only
  rw [Nat.add_mul]
  omega

def cross (d : DFA α) (left right : Word α) (K N : Nat) (es fs : List TimedEntry) :
    Result CountedJoin.BatchResult :=
  let ⟨idx,iwork⟩:=Cut.build d left right
  let ⟨source,swork⟩:=sources d idx es
  let ⟨target,twork⟩:=targets d idx fs
  let ⟨out,work⟩:=keyed K N source target
  (out,iwork+swork+twork+work+8)

theorem cross_value (d : DFA α) (left right : Word α) (K N : Nat) (es fs : List TimedEntry) :
    (cross d left right K N es fs).1=CountedJoin.cross d left right K N es fs := by
  simp only [cross,Cut.build_value,sources_value,targets_value,keyed_value,CountedJoin.cross]

def crossCoefficient (states K bound : Nat) : Nat :=
  Cut.coefficient states+21*states+(states+1)*(41*K*(bound+1)+7)+40

theorem cross_work (d : DFA α) (left right : Word α) (K N : Nat) (es fs : List TimedEntry)
    (bound : Nat) (he : bounded es bound) (hf : bounded fs bound) :
    (cross d left right K N es fs).2≤
      crossCoefficient d.stateCount K bound*(es.length+fs.length+left.length+right.length+1) := by
  let idx:=DFACut.build d left right
  let vol:=es.length+fs.length+left.length+right.length+1
  let keys:=41*K*(bound+1)+7
  have hv : 1≤vol := by dsimp only [vol]; omega
  have hevol : es.length≤vol := by dsimp only [vol]; omega
  have hfvol : fs.length≤vol := by dsimp only [vol]; omega
  have hwvol : left.length+right.length+1≤vol := by dsimp only [vol]; omega
  have hi:=Nat.le_trans (Cut.build_work d left right) (Nat.mul_le_mul_left _ hwvol)
  have hs:=sources_work d idx es
  have hs' : (sources d idx es).2≤10*vol := by
    have hh:=Nat.mul_le_mul_left 9 hevol
    omega
  have ht:=targets_work d idx fs
  have ht' : (targets d idx fs).2≤(21*d.stateCount+11)*vol := by
    have hh:=Nat.mul_le_mul_right (21*d.stateCount+10) hfvol
    rw [Nat.mul_comm vol] at hh
    simp only [Nat.add_mul] at hh ⊢
    omega
  have hl:=targets_length d idx fs
  have hm:=Nat.mul_le_mul_left d.stateCount hfvol
  have hlen : (TimedJoin.sources d idx es).length+(TimedJoin.targets d idx fs).length≤
      (d.stateCount+1)*vol := by
    simp only [TimedJoin.sources,List.length_map,Nat.add_mul,Nat.one_mul]
    omega
  have hk:=keyed_work K N (TimedJoin.sources d idx es) (TimedJoin.targets d idx fs) bound
    (sources_bounded d idx es bound he) (targets_bounded d idx fs bound hf)
  have hk' : (keyed K N (TimedJoin.sources d idx es) (TimedJoin.targets d idx fs)).2≤
      ((d.stateCount+1)*keys+6)*vol := by
    have hh:=Nat.mul_le_mul_right keys hlen
    have hc:=Nat.mul_le_mul_left 6 hv
    change _≤((TimedJoin.sources d idx es).length+(TimedJoin.targets d idx fs).length)*keys+6 at hk
    rw [show ((d.stateCount+1)*vol)*keys=((d.stateCount+1)*keys)*vol by ac_rfl] at hh
    rw [Nat.add_mul]
    simp only [Nat.mul_one] at hc
    omega
  have ho:=Nat.mul_le_mul_left 8 hv
  unfold cross crossCoefficient
  simp only [Cut.build_value,sources_value,targets_value]
  dsimp only [idx,vol,keys] at hi hs' ht' hk' ho
  simp only [Nat.mul_one,Nat.add_mul] at ht' hk' ho ⊢
  omega

end REWB.PeriodicActual.Join
