import REWB.MaskedClusterMutableLocality

/-! Locality of the concrete batch erase operation. A dense row can be
    shared by several clusters: deleting a point changes that source tree,
    but every bank whose actual candidates exclude the deleted position
    remains exactly equal at all replay keys. Targets are never erased.
-/
namespace REWB.MaskedCluster.Mutable.Batch
open REWB.RunGeometry
variable {α : Type}

def Candidates (s q m p : Nat) : Prop := ∃k,k≤m ∧ p=s+k*q

theorem compileRun_erase (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (source : Array Bool) (removed : List Nat) (sources : Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources)
    (id : Nat) (R : Bounds) (hR : sources.runs[id]?=some R)
    (s m L H next incoming : Nat) (enabled : Bool) (target : Array Bool) (targetCounts : Array Nat)
    (window : SourceWindow) (p : Nat) (hp : Candidates s R.period m p→window.allows p=false) :
    (compileRun C E book prepared ci ei (MaskedMutableProgression.Batch.eraseSource p sources)
      id s m L H next incoming enabled target targetCounts window).1=
      (compileRun C E book prepared ci ei sources id s m L H next incoming enabled target targetCounts window).1 := by
  by_cases hK : sources.modulus=prepared.K
  · have hv':=MaskedMutableProgression.Batch.eraseSource_valid hv p
    have hR' : (MaskedMutableProgression.Batch.eraseSource p sources).runs[id]?=some R := hR
    have hK' : (MaskedMutableProgression.Batch.eraseSource p sources).modulus=prepared.K := hK
    obtain ⟨a,ha,hs⟩:=hv.rows id R hR
    obtain ⟨b,hb,ht⟩:=hv'.rows id R hR'
    have hh : SameOn (Candidates s R.period m) window a b := SameOn.history hs ht hp
    have hstep : a.step=prepared.K*R.period := by rw [hs.step_eq,hK]
    rw [compileRun_lookup C E book prepared ci ei _ id s m L H next incoming enabled target targetCounts window R b hK' hR' hb,
      compileRun_lookup C E book prepared ci ei sources id s m L H next incoming enabled target targetCounts window R a hK hR ha]
    simp only
    exact congrArg Option.some (compileDenseBank_same C E book prepared ci ei s R.period m L H next incoming enabled a b target targetCounts
      window hh (hv.bounds id R hR).2.2 hstep (fun k hk=>⟨k,hk,rfl⟩)).symm
  · simp only [compileRun,MaskedMutableProgression.Batch.eraseSource_modulus,hK,if_false]

theorem compileSingleton_erase (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (source : Array Bool) (removed : List Nat) (sources : Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources)
    (s L H next incoming : Nat) (enabled : Bool) (target : Array Bool) (window : SourceWindow)
    (p : Nat) (hp : p=s→window.allows p=false) :
    (compileSingleton C E book ci ei (MaskedMutableProgression.Batch.eraseSource p sources)
      s L H next incoming enabled target window).1=
      (compileSingleton C E book ci ei sources s L H next incoming enabled target window).1 := by
  have hh : SameOn (fun x=>x=s) window sources.singleton (MaskedMutableProgression.erase sources.singleton p).index :=
    SameOn.erase hv.singleton.good p hp
  exact (compilePointBank_same C E book ci ei s L H next incoming enabled _ _ target window hh rfl).symm

end REWB.MaskedCluster.Mutable.Batch
