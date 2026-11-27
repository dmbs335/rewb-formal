import REWB.MaskedRunCatalogBuild

/-! Catalog preparation reuses the mutable source batch's single actual
cubic-run enumeration. Target rows and the run-ID map survive every
source-erasure history unchanged. -/
namespace REWB.MaskedRunCatalog
open REWB.RunGeometry
open REWB.MaskedPeriodic.Batch (span totalSpan)
variable {σ : Nat}

theorem batch_bounded (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (K : Nat) :
    ∀R,R∈(MaskedMutableProgression.Batch.prepare text fallback source K).runs.toList→
      RunDedup.Bounded text.size R := by
  intro R hR
  change R∈(MaskedOrdered.Owner.enumerateAuto text fallback).runs.toArray.toList at hR
  simp only [Array.toArray_toList] at hR
  exact RunDedup.valid_bounded _ _ _ ((MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mp hR).1

theorem batch_nodup (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (K : Nat) :
    (MaskedMutableProgression.Batch.prepare text fallback source K).runs.toList.Nodup := by
  change (MaskedOrdered.Owner.enumerateAuto text fallback).runs.toArray.toList.Nodup
  simpa only [Array.toArray_toList] using MaskedOrdered.Owner.enumerateAuto_nodup text fallback

theorem ofBatch_lookupId (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (R : Bounds) (id : Nat) :
    (lookupId (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)) R).1=some id ↔
      (MaskedMutableProgression.Batch.prepare text fallback source K).runs[id]?=some R :=
  lookupId_correct text.size target K _ (batch_bounded text fallback source K)
    (batch_nodup text fallback source K) R id

theorem ofBatch_lookup (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (R : Bounds) (id : Nat) (value : Entry) :
    (lookup (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)) R).1=some ⟨id,value⟩ ↔
      (MaskedMutableProgression.Batch.prepare text fallback source K).runs[id]?=some R ∧
        value=entry target K R :=
  lookup_found text.size target K _ (batch_bounded text fallback source K)
    (batch_nodup text fallback source K) R id value

theorem ofBatch_exists (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (R : Bounds) :
    (∃id,(lookup (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)) R).1=
      some ⟨id,entry target K R⟩) ↔
        R.Valid (ArrayText.read text fallback) text.size ∧ 3*R.period≤R.hi-R.lo := by
  simp only [ofBatch_lookup,and_true]
  exact MaskedMutableProgression.Batch.prepare_run_exists text fallback source K R

theorem ofBatch_eraseMany (target : Array Bool) (ps : List Nat) (st : MaskedMutableProgression.Batch.State) :
    ofBatch target (MaskedMutableProgression.Batch.eraseMany ps st)=ofBatch target st := by
  unfold ofBatch
  rw [MaskedMutableProgression.Batch.eraseMany_n,MaskedMutableProgression.Batch.eraseMany_modulus,
    MaskedMutableProgression.Batch.eraseMany_runs]

theorem ofBatch_counts (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (hK : 0<K) (R : Bounds) (id : Nat) (value : Entry)
    (he : (lookup (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)) R).1=some ⟨id,value⟩) :
    value.run=R ∧ value.counts=(MaskedProgression.build target R.lo (span R) (K*R.period)).counts ∧
      ∃hs : 0<K*R.period,∀i,i<span R→MaskedProgression.readCount value.counts i=
        MaskedProgression.countAt (fun x=>MaskedProgression.readMask target (R.lo+x)) (K*R.period) hs i := by
  obtain ⟨hr,rfl⟩:=(ofBatch_lookup text fallback source target K R id value).mp he
  have hv:=(MaskedMutableProgression.Batch.prepare_run_exists text fallback source K R).mp ⟨id,hr⟩
  have hq:=hv.1.2.2.2.1.1
  refine ⟨rfl,rfl,Nat.mul_pos hK hq,?_⟩
  intro i hi
  exact MaskedProgression.build_correct target R.lo (span R) (K*R.period) (Nat.mul_pos hK hq) i hi

structure Prepared where
  sources : MaskedMutableProgression.Batch.State
  catalog : Index
  work : Nat
  deriving Repr

/-- One source-batch call, followed by one target/catalog pass. -/
def prepare (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (K : Nat) : Prepared :=
  let sources:=MaskedMutableProgression.Batch.prepare text fallback source K
  let catalog:=ofBatch target sources
  ⟨sources,catalog,sources.totalWork+catalog.work+3⟩

theorem prepare_sources (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (K : Nat) :
    (prepare text fallback source target K).sources=MaskedMutableProgression.Batch.prepare text fallback source K := rfl

theorem prepare_lookupId (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (R : Bounds) (id : Nat) :
    (lookupId (prepare text fallback source target K).catalog R).1=some id ↔
      (prepare text fallback source target K).sources.runs[id]?=some R :=
  ofBatch_lookupId text fallback source target K R id

theorem prepare_lookup (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (R : Bounds) (id : Nat) (value : Entry) :
    (lookup (prepare text fallback source target K).catalog R).1=some ⟨id,value⟩ ↔
      (prepare text fallback source target K).sources.runs[id]?=some R ∧ value=entry target K R :=
  ofBatch_lookup text fallback source target K R id value

end REWB.MaskedRunCatalog
