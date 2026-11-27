import REWB.MaskedMutableProgressionBatchRows

/-! Global physical source deletion. The reverse row is taken and cleared
once; only its cached run IDs are visited. The singleton snapshot is
updated on every request. Correctness covers repeated and outside-window
requests, with no scan over the run array or occurrence sets. -/
namespace REWB.MaskedMutableProgression.Batch
open REWB.RunGeometry
open REWB.MaskedPeriodic.Batch (span totalSpan)
variable {σ : Nat}

theorem Valid.row_lookup {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (id : Nat) (idx : Index) (hi : st.indexes[id]?=some idx) :
    ∃R,st.runs[id]?=some R ∧ IndexSpec source removed R.lo (span R) (st.modulus*R.period) idx := by
  have hlt : id<st.runs.size := by
    have hh:=(Array.getElem?_eq_some_iff.mp hi).1
    have hs:=hv.size
    omega
  let R:=st.runs[id]
  have hR : st.runs[id]?=some R := Array.getElem?_eq_getElem hlt
  obtain ⟨old,hold,hs⟩:=hv.rows id R hR
  have he : old=idx:=Option.some.inj (hold.symm.trans hi)
  subst old
  exact ⟨R,hR,hs⟩

theorem Valid.rowsValid {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) : RowsValid st.indexes := by
  intro id idx hi
  obtain ⟨_,_,hs⟩:=hv.row_lookup id idx hi
  exact hs.good

theorem Valid.rowsHeight {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) : RowsHeight st.indexes (height (st.n+1)) := by
  intro id idx hi
  obtain ⟨R,hR,hs⟩:=hv.row_lookup id idx hi
  have hb:=hv.bounds id R hR
  have hspan : span R≤st.n+1 := by unfold span; omega
  have hl:=log_window (span R) (st.n+1) hspan
  rw [hs.sized,hs.len_eq]
  unfold height
  omega

theorem IndexSpec.updated {source : Array Bool} {removed : List Nat} {base len step : Nat}
    {old next : Index} (hs : IndexSpec source removed base len step old)
    (p : Nat) (selected : Prop) (hshape : Same old next) (hg : next.Valid)
    (hlive : ∀x,next.Live x ↔ old.Live x ∧ (selected→x≠p))
    (hcover : old.Live p→selected) : IndexSpec source (p::removed) base len step next := by
  refine ⟨hg,hshape.sized hs.sized,hshape.1.trans hs.base_eq,hshape.2.1.trans hs.len_eq,
    hshape.2.2.1.trans hs.step_eq,?_⟩
  intro x
  rw [hlive x,hshape.1,hshape.2.1]
  constructor
  · rintro ⟨hold,hsel⟩
    have hne : x≠p := by intro he; subst x; exact hsel (hcover hold) rfl
    obtain ⟨hlo,hhi,hm,hn⟩:=(hs.live x).mp hold
    exact ⟨hlo,hhi,hm,by simpa only [List.mem_cons,not_or] using And.intro hne hn⟩
  · rintro ⟨hlo,hhi,hm,hn⟩
    have hnot : x≠p ∧ x∉removed := by simpa only [List.mem_cons,not_or] using hn
    exact ⟨(hs.live x).mpr ⟨hlo,hhi,hm,hnot.2⟩,fun _=>hnot.1⟩

def eraseSource (p : Nat) (st : State) : State :=
  let f:=MaskedSourceFanout.take p st.sources
  let rows:=updateRows p f.1.ids st.indexes
  let one:=MaskedMutableProgression.erase st.singleton p
  {st with
    sources:=f.2
    indexes:=rows.rows
    singleton:=one.index
    updateWork:=st.updateWork+rows.work+one.work+8
    requests:=st.requests+1
    delivered:=st.delivered+rows.visits}

theorem eraseSource_n (p : Nat) (st : State) : (eraseSource p st).n=st.n := rfl
theorem eraseSource_modulus (p : Nat) (st : State) : (eraseSource p st).modulus=st.modulus := rfl
theorem eraseSource_runs (p : Nat) (st : State) : (eraseSource p st).runs=st.runs := rfl

theorem eraseSource_valid {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (p : Nat) : Valid source (p::removed) (eraseSource p st) := by
  refine ⟨hv.positive,MaskedSourceFanout.take_good p st.sources hv.sourceGood,?_,?_,hv.bounds,
    hv.singleton.erase p,?_,?_⟩
  · exact (MaskedSourceFanout.take_size p st.sources).trans hv.sourceSize
  · exact (updateRows_size p _ st.indexes).trans hv.size
  · intro id R hR
    obtain ⟨old,hold,hs⟩:=hv.rows id R hR
    obtain ⟨next,hnext,hshape,hgood,hlive⟩:=updateRows_lookup p
      (MaskedSourceFanout.take p st.sources).1.ids st.indexes hv.rowsValid id old hold
    refine ⟨next,hnext,hs.updated p _ hshape hgood hlive ?_⟩
    intro hp
    obtain ⟨hlo,hhi,_,hn⟩:=(hs.live p).mp hp
    rw [hs.base_eq] at hlo
    rw [hs.base_eq,hs.len_eq] at hhi
    have hb:=hv.bounds id R hR
    change id∈(MaskedSourceFanout.read st.sources.rows p).ids
    exact (hv.pending p id).mpr ⟨hn,R,hR,hlo,by unfold span at hhi; omega⟩
  · intro x id
    change id∈(MaskedSourceFanout.read (MaskedSourceFanout.take p st.sources).2.rows x).ids ↔ _
    rw [MaskedSourceFanout.take_read]
    by_cases hx : x=p
    · subst x
      simp
    · rw [if_neg hx,hv.pending x id]
      simp only [List.mem_cons,hx,false_or,eraseSource_runs]

theorem IndexSpec.history {source : Array Bool} {old new : List Nat} {base len step : Nat}
    {idx : Index} (hs : IndexSpec source old base len step idx)
    (he : ∀x,x∈old↔x∈new) : IndexSpec source new base len step idx := by
  refine ⟨hs.good,hs.sized,hs.base_eq,hs.len_eq,hs.step_eq,?_⟩
  intro x
  rw [hs.live x]
  simp only [Current,he x]

theorem Valid.history {source : Array Bool} {old new : List Nat} {st : State}
    (hv : Valid source old st) (he : ∀x,x∈old↔x∈new) : Valid source new st := by
  refine ⟨hv.positive,hv.sourceGood,hv.sourceSize,hv.size,hv.bounds,hv.singleton.history he,?_,?_⟩
  · intro id R hR
    obtain ⟨idx,hi,hs⟩:=hv.rows id R hR
    exact ⟨idx,hi,hs.history he⟩
  · intro p id
    rw [hv.pending p id,he p]

def eraseMany (ps : List Nat) (st : State) : State := ps.foldl (fun st p=>eraseSource p st) st

theorem eraseMany_n (ps : List Nat) (st : State) : (eraseMany ps st).n=st.n := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih => exact (ih (eraseSource p st)).trans rfl

theorem eraseMany_modulus (ps : List Nat) (st : State) : (eraseMany ps st).modulus=st.modulus := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih => exact (ih (eraseSource p st)).trans rfl

theorem eraseMany_runs (ps : List Nat) (st : State) : (eraseMany ps st).runs=st.runs := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih => exact (ih (eraseSource p st)).trans rfl

theorem eraseMany_valid_reverse {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (ps : List Nat) :
    Valid source (ps.reverse++removed) (eraseMany ps st) := by
  induction ps generalizing removed st with
  | nil => exact hv
  | cons p ps ih =>
    have hh:=ih (eraseSource_valid hv p)
    simpa only [eraseMany,List.foldl_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

theorem eraseMany_valid {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (ps : List Nat) :
    Valid source (ps++removed) (eraseMany ps st) :=
  (eraseMany_valid_reverse hv ps).history (by intro x; simp only [List.mem_append,List.mem_reverse])

def run (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (K : Nat)
    (ps : List Nat) : State := eraseMany ps (prepare text fallback source K)

theorem run_valid (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (hK : 0<K) (ps : List Nat) : Valid source ps (run text fallback source K ps) := by
  simpa only [List.append_nil] using eraseMany_valid (prepare_valid text fallback source K hK) ps

/-- Exact singleton source semantics after every requested deletion. -/
theorem run_member (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (hK : 0<K) (ps : List Nat) (p : Nat) :
    (member (run text fallback source K ps).singleton p).1=true ↔
      p≤text.size ∧ MaskedProgression.readMask source p=true ∧ p∉ps := by
  have hv:=(run_valid text fallback source K hK ps).singleton
  rw [member_correct _ hv.good,hv.live p,hv.base_eq,hv.len_eq]
  change (0≤p ∧ p<0+((eraseMany ps (prepare text fallback source K)).n+1) ∧ Current source ps p) ↔ _
  rw [eraseMany_n]
  change (0≤p ∧ p<0+(text.size+1) ∧ Current source ps p) ↔ _
  unfold Current
  constructor
  · rintro ⟨_,hb,hm,hn⟩; exact ⟨by omega,hm,hn⟩
  · rintro ⟨hb,hm,hn⟩; exact ⟨Nat.zero_le _,by omega,hm,hn⟩

end REWB.MaskedMutableProgression.Batch
