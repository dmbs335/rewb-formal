import REWB.MaskedMutableProgressionBatchErase

/-! Aggregate cost of the actual source-index batch. Build work is charged
to enumerated cubic-run spans. Deletion work is charged to the reverse
memberships actually delivered once, plus one logarithmic singleton path
per request. Repeated requests do not redeliver run memberships. -/
namespace REWB.MaskedMutableProgression.Batch
open REWB.RunGeometry
open REWB.MaskedPeriodic.Batch (span totalSpan)
variable {σ : Nat}

def requestBudget (n : Nat) : Nat := 12*height (n+1)+22
def rowBudget (n : Nat) : Nat := 12*height (n+1)+19

theorem row_build_work (source : Array Bool) (K n : Nat) (R : Bounds) (hb : R.hi≤n) :
    (build source R.lo (span R) (K*R.period)).work+6≤86*span R*((n+2).log2+1) := by
  let L:=(n+2).log2+1
  have hs : 1≤span R := by unfold span; omega
  have hsn : span R≤n+1 := by unfold span; omega
  have hl:=log_window (span R) (n+1) hsn
  change (span R+1).log2≤(n+2).log2 at hl
  have hw:=build_log_work source R.lo (span R) (K*R.period)
  have hm:=Nat.mul_le_mul (show 40*(span R+1)≤80*span R by omega)
    (show (span R+1).log2+1≤L by dsimp [L]; omega)
  have hL : 1≤L := by dsimp [L]; omega
  have hp : 1≤span R*L := by
    have hm:=Nat.mul_le_mul hs hL
    simpa only [Nat.one_mul] using hm
  change _≤86*span R*L
  have he : 86*span R*L=80*span R*L+6*(span R*L) := by
    rw [show (86:Nat)=80+6 by decide,Nat.add_mul,Nat.add_mul,Nat.mul_assoc 6]
  rw [he]
  omega

theorem rowsCost_bound (source : Array Bool) (K n : Nat) (Rs : List Bounds)
    (hb : ∀R,R∈Rs→R.hi≤n) : rowsCost source K Rs≤86*totalSpan Rs*((n+2).log2+1) := by
  induction Rs with
  | nil => simp [rowsCost,totalSpan]
  | cons R Rs ih =>
    have hh:=row_build_work source K n R (hb R List.mem_cons_self)
    have ht:=ih (fun S hS=>hb S (List.mem_cons_of_mem R hS))
    simp only [rowsCost,totalSpan]
    rw [Nat.mul_add 86 (span R) (totalSpan Rs),Nat.add_mul]
    exact Nat.add_le_add hh ht

theorem prepare_source_work (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) : (prepare text fallback source K).preparationWork≤
      text.size+11+66*text.size*(text.size.log2+1)+
      516*text.size*(text.size.log2+1)*((text.size+2).log2+1)+
      40*(text.size+2)*((text.size+2).log2+1) := by
  have hf:=(MaskedSourceFanout.prepare_work text fallback).1
  have hs:=MaskedPeriodic.Batch.enumerated_span text fallback
  have hr:=rowsCost_bound source K text.size (MaskedOrdered.Owner.enumerateAuto text fallback).runs
    (fun R hR=>(MaskedSourceFanout.enumerated_bounds text fallback R hR).2)
  have hm:=Nat.mul_le_mul_right ((text.size+2).log2+1) (Nat.mul_le_mul_left 86 hs)
  have hg:=build_log_work source 0 (text.size+1) 1
  change (build source 0 (text.size+1) 1).work≤40*(text.size+2)*((text.size+2).log2+1) at hg
  have hrows : (buildRows source K (MaskedSourceFanout.prepare text fallback).runs).work=
      1+rowsCost source K (MaskedOrdered.Owner.enumerateAuto text fallback).runs := by
    rw [buildRows_work]
    rfl
  have he : 86*(6*text.size*(text.size.log2+1))*((text.size+2).log2+1)=
      516*text.size*(text.size.log2+1)*((text.size+2).log2+1) := by
    simp only [←Nat.mul_assoc]
  rw [he] at hm
  change (MaskedSourceFanout.prepare text fallback).preparationWork+
    (buildRows source K (MaskedSourceFanout.prepare text fallback).runs).work+
    (build source 0 (text.size+1) 1).work+7≤_
  rw [hrows]
  omega

theorem prepare_enumeration_work (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) : (prepare text fallback source K).enumerationWork≤
      MaskedRunEnumerationCost.coefficient σ*(text.size+1)*((text.size+1).log2+1)^2 :=
  (MaskedSourceFanout.prepare_work text fallback).2

theorem eraseSource_delivered {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (p : Nat) :
    (eraseSource p st).delivered=st.delivered+(MaskedSourceFanout.take p st.sources).1.count := by
  have hr:=(updateRows_counters p (MaskedSourceFanout.take p st.sources).1.ids st.indexes
    (height (st.n+1)) hv.rowsHeight).1
  have hc:=MaskedSourceFanout.take_count p st.sources hv.sourceGood
  change st.delivered+(updateRows p _ st.indexes).visits=_
  rw [hr,hc]

theorem eraseSource_balance {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (p : Nat) :
    (eraseSource p st).delivered+(eraseSource p st).sources.memberships=
      st.delivered+st.sources.memberships := by
  have hc:=MaskedSourceFanout.take_balance p st.sources hv.sourceGood
  rw [eraseSource_delivered hv p]
  change _+(MaskedSourceFanout.take p st.sources).2.memberships=_
  omega

theorem eraseSource_work {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (p : Nat) :
    (eraseSource p st).updateWork≤st.updateWork+requestBudget st.n+
      (MaskedSourceFanout.take p st.sources).1.count*rowBudget st.n := by
  have hr:=(updateRows_counters p (MaskedSourceFanout.take p st.sources).1.ids st.indexes
    (height (st.n+1)) hv.rowsHeight).2
  have hc:=MaskedSourceFanout.take_count p st.sources hv.sourceGood
  rw [←hc] at hr
  have hg:=erase_work st.singleton p
  rw [hv.singleton.sized,hv.singleton.len_eq] at hg
  change st.updateWork+(updateRows p _ st.indexes).work+(erase st.singleton p).work+8≤_
  unfold requestBudget rowBudget
  omega

theorem eraseSource_charged {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (p : Nat) :
    (eraseSource p st).updateWork+st.delivered*rowBudget st.n≤
      st.updateWork+requestBudget st.n+(eraseSource p st).delivered*rowBudget st.n := by
  have hw:=eraseSource_work hv p
  rw [eraseSource_delivered hv p,Nat.add_mul]
  omega

theorem eraseMany_balance {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (ps : List Nat) :
    (eraseMany ps st).delivered+(eraseMany ps st).sources.memberships=
      st.delivered+st.sources.memberships := by
  induction ps generalizing removed st with
  | nil => rfl
  | cons p ps ih =>
    have hi:=ih (eraseSource_valid hv p)
    have hh:=eraseSource_balance hv p
    exact hi.trans hh

theorem eraseMany_requests (ps : List Nat) (st : State) :
    (eraseMany ps st).requests=st.requests+ps.length := by
  induction ps generalizing st with
  | nil => simp [eraseMany]
  | cons p ps ih =>
    have hh:=ih (eraseSource p st)
    change (eraseMany (p::ps) st).requests=(st.requests+1)+ps.length at hh
    rw [List.length_cons]
    omega

theorem eraseMany_charged {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (ps : List Nat) :
    (eraseMany ps st).updateWork+st.delivered*rowBudget st.n≤
      st.updateWork+ps.length*requestBudget st.n+(eraseMany ps st).delivered*rowBudget st.n := by
  induction ps generalizing removed st with
  | nil => simp [eraseMany]
  | cons p ps ih =>
    have hi:=ih (eraseSource_valid hv p)
    have hh:=eraseSource_charged hv p
    rw [eraseSource_n] at hi
    change (eraseMany (p::ps) st).updateWork+(eraseSource p st).delivered*rowBudget st.n≤
      (eraseSource p st).updateWork+ps.length*requestBudget st.n+
        (eraseMany (p::ps) st).delivered*rowBudget st.n at hi
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem run_delivered (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (hK : 0<K) (ps : List Nat) :
    (run text fallback source K ps).delivered≤6*text.size*(text.size.log2+1) := by
  have hb:=eraseMany_balance (prepare_valid text fallback source K hK) ps
  have hs:=MaskedSourceFanout.prepare_memberships text fallback
  change (run text fallback source K ps).delivered+(run text fallback source K ps).sources.memberships=
    0+(MaskedSourceFanout.prepare text fallback).sources.memberships at hb
  omega

theorem run_work_delivered (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (hK : 0<K) (ps : List Nat) :
    (run text fallback source K ps).updateWork≤ps.length*requestBudget text.size+
      (run text fallback source K ps).delivered*rowBudget text.size := by
  have hh:=eraseMany_charged (prepare_valid text fallback source K hK) ps
  simpa only [run,prepare,Nat.zero_mul,Nat.add_zero,Nat.zero_add] using hh

theorem run_work (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (hK : 0<K) (ps : List Nat) :
    (run text fallback source K ps).updateWork≤ps.length*requestBudget text.size+
      (6*text.size*(text.size.log2+1))*rowBudget text.size := by
  have hw:=run_work_delivered text fallback source K hK ps
  have hm:=Nat.mul_le_mul_right (rowBudget text.size) (run_delivered text fallback source K hK ps)
  omega

theorem run_log_work (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (hK : 0<K) (ps : List Nat) :
    (run text fallback source K ps).updateWork≤
      46*ps.length*((text.size+2).log2+1)+
      258*text.size*(text.size.log2+1)*((text.size+2).log2+1) := by
  have hw:=run_work text fallback source K hK ps
  have ha : requestBudget text.size≤46*((text.size+2).log2+1) := by
    change 12*(2*((text.size+2).log2+1))+22≤46*((text.size+2).log2+1)
    omega
  have hb : rowBudget text.size≤43*((text.size+2).log2+1) := by
    change 12*(2*((text.size+2).log2+1))+19≤43*((text.size+2).log2+1)
    omega
  have hma:=Nat.mul_le_mul_left ps.length ha
  have hmb:=Nat.mul_le_mul_left (6*text.size*(text.size.log2+1)) hb
  have he : ps.length*(46*((text.size+2).log2+1))=46*ps.length*((text.size+2).log2+1) := by ac_rfl
  have he' : (6*text.size*(text.size.log2+1))*(43*((text.size+2).log2+1))=
      258*text.size*(text.size.log2+1)*((text.size+2).log2+1) := by
    rw [show (258:Nat)=6*43 by decide]
    ac_rfl
  rw [he] at hma
  rw [he'] at hmb
  omega

def sourcePreparationBudget (n : Nat) : Nat :=
  n+11+66*n*(n.log2+1)+516*n*(n.log2+1)*((n+2).log2+1)+40*(n+2)*((n+2).log2+1)

def sourceUpdateBudget (n requests : Nat) : Nat :=
  46*requests*((n+2).log2+1)+258*n*(n.log2+1)*((n+2).log2+1)

def totalBudget (σ n requests : Nat) : Nat :=
  MaskedRunEnumerationCost.coefficient σ*(n+1)*((n+1).log2+1)^2+
    sourcePreparationBudget n+sourceUpdateBudget n requests

def State.totalWork (st : State) : Nat := st.enumerationWork+st.preparationWork+st.updateWork

theorem eraseMany_preparation (ps : List Nat) (st : State) :
    (eraseMany ps st).enumerationWork=st.enumerationWork ∧
    (eraseMany ps st).preparationWork=st.preparationWork := by
  induction ps generalizing st with
  | nil => exact ⟨rfl,rfl⟩
  | cons p ps ih => exact ih (eraseSource p st)

/-- All returned counters, including the one actual run enumeration. -/
theorem run_total_work (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (hK : 0<K) (ps : List Nat) :
    (run text fallback source K ps).totalWork≤totalBudget σ text.size ps.length := by
  have he:=prepare_enumeration_work text fallback source K
  have hp:=prepare_source_work text fallback source K
  have hu:=run_log_work text fallback source K hK ps
  have hh:=eraseMany_preparation ps (prepare text fallback source K)
  change (run text fallback source K ps).enumerationWork=(prepare text fallback source K).enumerationWork ∧
    (run text fallback source K ps).preparationWork=(prepare text fallback source K).preparationWork at hh
  unfold State.totalWork totalBudget sourcePreparationBudget sourceUpdateBudget
  rw [hh.1,hh.2]
  omega

end REWB.MaskedMutableProgression.Batch
