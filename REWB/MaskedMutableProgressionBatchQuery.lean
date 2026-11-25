import REWB.MaskedMutableProgressionBatchCost

/-! Executable run-ID queries on the maintained snapshots. Two direct
array reads select a descriptor and its source index. A successful answer
is a globally live physical source after the entire deletion history. -/
namespace REWB.MaskedMutableProgression.Batch
open REWB.RunGeometry
open REWB.MaskedPeriodic.Batch (span)
variable {σ : Nat}

def queryRun (st : State) (id s lo hi r : Nat) : Answer :=
  match st.runs[id]?,st.indexes[id]? with
  | some R,some idx =>
    let out:=ap idx R.period st.modulus s lo hi r
    ⟨out.value,out.work+7⟩
  | _,_ => ⟨none,4⟩

theorem queryRun_correct {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (id s lo hi r : Nat) (R : Bounds) (hR : st.runs[id]?=some R) :
    (queryRun st id s lo hi r).answer=true ↔
      ∃k,lo≤k ∧ k≤hi ∧ k%st.modulus=r ∧ R.lo≤s+k*R.period ∧ s+k*R.period≤R.hi ∧
        Current source removed (s+k*R.period) := by
  obtain ⟨idx,hidx,hs⟩:=hv.rows id R hR
  have hb:=hv.bounds id R hR
  simp only [queryRun,hR,hidx]
  change (ap idx R.period st.modulus s lo hi r).answer=true ↔ _
  rw [ap_represents idx hs.good _ hs.live R.period st.modulus s lo hi r hb.2.2 hv.positive hs.step_eq,
    hs.base_eq,hs.len_eq]
  constructor
  · rintro ⟨k,hlo,hhi,hm,hl,hb',hc⟩
    exact ⟨k,hlo,hhi,hm,hl,by unfold span at hb'; omega,hc⟩
  · rintro ⟨k,hlo,hhi,hm,hl,hb',hc⟩
    exact ⟨k,hlo,hhi,hm,hl,by unfold span; omega,hc⟩

theorem queryRun_some {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (id s lo hi r p : Nat)
    (hp : (queryRun st id s lo hi r).value=some p) :
    ∃R,st.runs[id]?=some R ∧ ∃k,lo≤k ∧ k≤hi ∧ k%st.modulus=r ∧
      p=s+k*R.period ∧ R.lo≤p ∧ p≤R.hi ∧ Current source removed p := by
  cases hR : st.runs[id]? with
  | none => simp only [queryRun,hR] at hp; contradiction
  | some R =>
    obtain ⟨idx,hidx,hs⟩:=hv.rows id R hR
    simp only [queryRun,hR,hidx] at hp
    obtain ⟨k,hlo,hhi,hm,he,hp'⟩:=ap_some idx hs.good R.period st.modulus s lo hi r p hp
    obtain ⟨hl,hb,hcurrent⟩:=(hs.live p).mp hp'
    rw [hs.base_eq] at hl
    rw [hs.base_eq,hs.len_eq] at hb
    have hbounds:=hv.bounds id R hR
    exact ⟨R,rfl,k,hlo,hhi,hm,he,hl,by unfold span at hb; omega,hcurrent⟩

theorem queryRun_work {source : Array Bool} {removed : List Nat} {st : State}
    (hv : Valid source removed st) (id s lo hi r : Nat) :
    (queryRun st id s lo hi r).work≤79*((st.n+2).log2+1)+7 := by
  cases hR : st.runs[id]? with
  | none => simp only [queryRun,hR]; omega
  | some R =>
    obtain ⟨idx,hidx,hs⟩:=hv.rows id R hR
    have hb:=hv.bounds id R hR
    have hlen : idx.len≤st.n+1 := by rw [hs.len_eq]; unfold span; omega
    have hw:=ap_global_work idx hs.sized (st.n+1) hlen R.period st.modulus s lo hi r
    change (ap idx R.period st.modulus s lo hi r).work≤79*((st.n+2).log2+1) at hw
    simp only [queryRun,hR,hidx]
    omega

theorem run_runs (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (ps : List Nat) : (run text fallback source K ps).runs=
      (MaskedOrdered.Owner.enumerateAuto text fallback).runs.toArray :=
  (eraseMany_runs ps _).trans (prepare_runs text fallback source K)

/-- The full public construction/update/query path has exact current
source semantics. Its descriptor IDs are those of the actual enumerator. -/
theorem run_query_correct (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (hK : 0<K) (ps : List Nat) (id s lo hi r : Nat) (R : Bounds)
    (hR : (MaskedOrdered.Owner.enumerateAuto text fallback).runs.toArray[id]?=some R) :
    (queryRun (run text fallback source K ps) id s lo hi r).answer=true ↔
      ∃k,lo≤k ∧ k≤hi ∧ k%K=r ∧ R.lo≤s+k*R.period ∧ s+k*R.period≤R.hi ∧
        MaskedProgression.readMask source (s+k*R.period)=true ∧ s+k*R.period∉ps := by
  have hr : (run text fallback source K ps).runs[id]?=some R := by rw [run_runs]; exact hR
  have hh:=queryRun_correct (run_valid text fallback source K hK ps) id s lo hi r R hr
  have hmod : (run text fallback source K ps).modulus=K := eraseMany_modulus ps _
  simpa only [hmod,Current] using hh

end REWB.MaskedMutableProgression.Batch
