import REWB.MaskedRunCatalogBatch

/-! Aggregate immutable-target allocation and all catalog construction
work over the actual enumerated cubic runs. Target cells are O(n log n);
the binary exact-ID map contributes one logarithmic key path per run. -/
namespace REWB.MaskedRunCatalog
open REWB.RunGeometry
open REWB.MaskedPeriodic.Batch (span totalSpan)
variable {σ : Nat}

theorem build_span_work (n : Nat) (target : Array Bool) (K : Nat) (runs : Array Bounds) :
    (build n target K runs).work≤(38*width n+28)*totalSpan runs.toList+5 := by
  have hw:=build_work n target K runs
  have hs:=MaskedSourceFanout.length_le_span runs.toList
  simp only [Array.length_toList] at hs
  have hm:=Nat.mul_le_mul_left (38*width n+15) hs
  have he : (38*width n+28)*totalSpan runs.toList=
      13*totalSpan runs.toList+(38*width n+15)*totalSpan runs.toList := by
    simp only [Nat.add_mul]
    omega
  rw [he]
  omega

theorem ofBatch_cells (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (K : Nat) :
    (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)).cells≤
      6*text.size*(text.size.log2+1) := by
  rw [ofBatch,build_cells]
  change totalSpan (MaskedOrdered.Owner.enumerateAuto text fallback).runs.toArray.toList≤_
  simpa only [Array.toArray_toList] using MaskedPeriodic.Batch.enumerated_span text fallback

theorem ofBatch_work (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (K : Nat) :
    (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)).work≤
      (38*width text.size+28)*(6*text.size*(text.size.log2+1))+5 := by
  have hw:=build_span_work text.size target K (MaskedMutableProgression.Batch.prepare text fallback source K).runs
  have hs:=MaskedPeriodic.Batch.enumerated_span text fallback
  have hm:=Nat.mul_le_mul_left (38*width text.size+28) hs
  change (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)).work≤
    (38*width text.size+28)*totalSpan (MaskedOrdered.Owner.enumerateAuto text fallback).runs.toArray.toList+5 at hw
  simp only [Array.toArray_toList] at hw
  omega

theorem catalog_factor (n : Nat) :
    (38*width n+28)*(6*n*(n.log2+1))+5≤401*(n+1)*(width n)^2 := by
  have hp : 1≤width n := by unfold width; omega
  have hd : n.log2+1≤width n := MaskedRunEnumerationCost.depth_le n
  have hv : 1≤(n+1)*(width n)^2 := (MaskedRunEnumerationCost.square_bounds n).1
  have ha : 38*width n+28≤66*width n := by omega
  have hb:=Nat.mul_le_mul (Nat.mul_le_mul_left 6 (show n≤n+1 by omega)) hd
  have hm:=Nat.mul_le_mul ha hb
  have he : (66*width n)*(6*(n+1)*width n)=396*(n+1)*(width n)^2 := by
    rw [Nat.pow_two]
    calc
      _ = (66*6)*(n+1)*(width n*width n) := by ac_rfl
      _ = _ := rfl
  rw [he] at hm
  have h5:=Nat.mul_le_mul_left 5 hv
  have he' : 401*(n+1)*(width n)^2=396*(n+1)*(width n)^2+5*((n+1)*(width n)^2) := by
    rw [show (401:Nat)=396+5 by decide,Nat.add_mul,Nat.add_mul,Nat.mul_assoc 5]
  rw [he']
  omega

theorem ofBatch_work_closed (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (K : Nat) :
    (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)).work≤
      401*(text.size+1)*((text.size+1).log2+1)^2 :=
  Nat.le_trans (ofBatch_work text fallback source target K) (catalog_factor text.size)

theorem ofBatch_lookup_work (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (R : Bounds) :
    (lookup (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)) R).2≤
      26*((text.size+1).log2+1)+15 := lookup_work _ _

theorem prepare_work (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (K : Nat) :
    (prepare text fallback source target K).work≤
      (MaskedRunEnumerationCost.coefficient σ+401)*(text.size+1)*((text.size+1).log2+1)^2+
        MaskedMutableProgression.Batch.sourcePreparationBudget text.size+3 := by
  have he:=MaskedMutableProgression.Batch.prepare_enumeration_work text fallback source K
  have hp:=MaskedMutableProgression.Batch.prepare_source_work text fallback source K
  have hc:=ofBatch_work_closed text fallback source target K
  change (MaskedMutableProgression.Batch.prepare text fallback source K).preparationWork≤
    MaskedMutableProgression.Batch.sourcePreparationBudget text.size at hp
  change (MaskedMutableProgression.Batch.prepare text fallback source K).enumerationWork+
    (MaskedMutableProgression.Batch.prepare text fallback source K).preparationWork+0+
    (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)).work+3≤_
  rw [Nat.add_mul,Nat.add_mul]
  omega

end REWB.MaskedRunCatalog
