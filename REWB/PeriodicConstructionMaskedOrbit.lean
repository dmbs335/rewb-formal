import REWB.PeriodicConstructionSyntax
import REWB.MaskedClusterMutableCell

/-! Materialized inputs to the measured masked orbit compiler.
Acceptance is stored in a vector: generic queries cannot hide an
unbounded acceptance closure. Concrete constructors evaluate DFA final
tests or state equalities once per finite state. DFA primitives and
scalar arithmetic use the same unit-operation convention as the rest
of the construction ledger. -/
namespace REWB.PeriodicConstruction.Masked
open REWB.PeriodicConstruction REWB.MaskedPeriodic REWB.MaskedFiniteAction.Maps
open REWB.AffineProjection
variable {α β : Type} {m : Nat}

def tabulate (m : Nat) (f : Fin m→Result β) : Result (Vector β m) :=
  let results:=Vector.ofFn f
  (Vector.ofFn (fun i=>(results.get i).1),
    BoundaryIndex.Counted.rowWork results+2*m+1)

theorem tabulate_get (f : Fin m→Result β) (i : Fin m) :
    (tabulate m f).1.get i=(f i).1 := by
  simp only [tabulate,BoundaryIndex.Table.get_ofFn]

theorem tabulate_work (f : Fin m→Result β) (C : Nat) (h : ∀i,(f i).2≤C) :
    (tabulate m f).2≤m*(C+3)+1 := by
  have hh:=MaskedCluster.rowWork_le (Vector.ofFn f) C (by
    intro i
    simpa only [BoundaryIndex.Table.get_ofFn] using h i)
  unfold tabulate
  dsimp only
  simp only [Nat.mul_add] at hh ⊢
  omega

structure Input (m : Nat) where
  step : Map m
  initial : Fin m
  accepts : Vector Bool m

def Input.data (o : Input m) : OrbitData m := ⟨o.step,o.initial,o.accepts.get⟩

def descriptor (o : Input m) : Result FiniteOrbit.Descriptor :=
  let out:=Orbit.compress m (fun q=>(o.step.get q,2)) o.initial
    (fun q=>(o.accepts.get q,2))
  (out.1.getD ⟨0,1,[],[]⟩,out.2+2)

theorem descriptor_value (o : Input m) : (descriptor o).1=o.data.descriptor := by
  have h:=Orbit.compress_value (FiniteRelation.finEnum m)
    (fun q=>(o.step.get q,2)) o.initial (fun q=>(o.accepts.get q,2))
  simpa only [descriptor,FiniteRelation.finEnum,List.length_ofFn,
    OrbitData.descriptor,Input.data] using congrArg
      (fun x : Option FiniteOrbit.Descriptor=>x.getD ⟨0,1,[],[]⟩) h

def descriptorCost (m : Nat) : Nat := Orbit.compressBudget m 2+2

theorem descriptor_work (o : Input m) : (descriptor o).2≤descriptorCost m := by
  exact Nat.add_le_add_right
    (Orbit.compress_work m 2 _ _ _ (fun _=>Nat.le_refl _) (fun _=>Nat.le_refl _)) 2

def orbitFormula (o : Input m) (t : Aff) : Result AffineProjection.Formula :=
  let d:=descriptor o
  let out:=PeriodicConstruction.Formula.descriptorFormula d.1 t
  (out.1,d.2+out.2+1)

def orbitBudget (m : Nat) : PeriodicConstruction.Formula.Budget :=
  (PeriodicConstruction.Formula.descriptorBudget m).charge (descriptorCost m+1)

theorem orbitFormula_value (o : Input m) (t : Aff) :
    (orbitFormula o t).1=o.data.formula t := by
  simp only [orbitFormula,PeriodicConstruction.Formula.descriptorFormula_value,
    descriptor_value,OrbitData.formula]

theorem orbitFormula_covers (o : Input m) (t : Aff) :
    PeriodicConstruction.Formula.Covers (orbitFormula o t) (orbitBudget m) := by
  have hs:=o.data.descriptor_spec.2.2.1
  have hf:=PeriodicConstruction.Formula.descriptorFormula_covers (descriptor o).1 t m
    (by simpa only [descriptor_value] using hs)
  have hd:=descriptor_work o
  refine ⟨hf.1,?_⟩
  have hw:=hf.2
  unfold orbitFormula orbitBudget PeriodicConstruction.Formula.Budget.charge
  dsimp only
  omega

theorem orbitFormula_atoms (o : Input m) (t : Aff) :
    Syntax.Atoms (orbitFormula o t).1 (Syntax.aff t+4) := by
  rw [orbitFormula_value,OrbitData.formula]
  exact Syntax.atoms_descriptor _ _

def ofMaps (d : DFA α) (period before after : Map d.stateCount) :
    Result (Input d.stateCount) :=
  let bits:=tabulate d.stateCount (fun q=>(d.final (after.get q),3))
  (⟨period,before.get d.initial,bits.1⟩,bits.2+4)

theorem ofMaps_value (d : DFA α) (period before after : Map d.stateCount) :
    (ofMaps d period before after).1.data=MaskedPeriodic.ofMaps d period before after := by
  unfold ofMaps Input.data MaskedPeriodic.ofMaps
  congr 1
  funext q
  exact tabulate_get _ q

theorem ofMaps_work (d : DFA α) (period before after : Map d.stateCount) :
    (ofMaps d period before after).2≤6*d.stateCount+5 := by
  have h:=tabulate_work (fun q=>(d.final (after.get q),3)) 3 (fun _=>Nat.le_refl _)
  simpa only [ofMaps,Nat.reduceAdd,Nat.mul_comm _ 6] using Nat.add_le_add_right h 4

def always (d : DFA α) : Result (Input d.stateCount) :=
  let step:=tabulate d.stateCount (fun q=>(q,1))
  let bits:=tabulate d.stateCount (fun _=>(true,1))
  (⟨step.1,d.initial,bits.1⟩,step.2+bits.2+3)

theorem always_value (d : DFA α) : (always d).1.data=MaskedCluster.always d := by
  unfold always Input.data MaskedCluster.always
  congr 1
  · apply Vector.ext
    intro i hi
    change (tabulate d.stateCount (fun q=>(q,1))).1.get ⟨i,hi⟩=
      (identity d.stateCount).get ⟨i,hi⟩
    simp only [tabulate_get,identity,BoundaryIndex.Table.get_ofFn,id_eq]
  · funext q
    exact tabulate_get _ q

theorem always_work (d : DFA α) : (always d).2≤8*d.stateCount+5 := by
  have h1:=tabulate_work (fun q : Fin d.stateCount=>(q,1)) 1 (fun _=>Nat.le_refl _)
  have h2:=tabulate_work (fun _ : Fin d.stateCount=>(true,1)) 1 (fun _=>Nat.le_refl _)
  unfold always
  dsimp only
  simp only [Nat.reduceAdd,Nat.mul_comm _ 4] at h1 h2
  omega

def entry (C E : DFA α) (maps : MaskedCluster.Context C E) (input : Fin C.stateCount) :
    Result (Input C.stateCount) :=
  let bits:=tabulate C.stateCount (fun q=>(C.final q,1))
  (⟨maps.leftStep,maps.before.get input,bits.1⟩,bits.2+4)

theorem entry_value (C E : DFA α) (maps : MaskedCluster.Context C E) (input : Fin C.stateCount) :
    (entry C E maps input).1.data=MaskedCluster.entryOrbit C E maps input := by
  unfold entry Input.data MaskedCluster.entryOrbit
  congr 1
  funext q
  exact tabulate_get _ q

theorem entry_work (C E : DFA α) (maps : MaskedCluster.Context C E) (input : Fin C.stateCount) :
    (entry C E maps input).2≤4*C.stateCount+5 := by
  have h:=tabulate_work (fun q=>(C.final q,1)) 1 (fun _=>Nat.le_refl _)
  simpa only [entry,Nat.reduceAdd,Nat.mul_comm _ 4] using Nat.add_le_add_right h 4

def exit (d : DFA α) (period replay after : Map d.stateCount) (output : Fin d.stateCount) :
    Result (Input d.stateCount) :=
  let bits:=tabulate d.stateCount (fun q=>(decide (after.get q=output),3))
  (⟨period,replay.get d.initial,bits.1⟩,bits.2+4)

theorem exit_value (d : DFA α) (period replay after : Map d.stateCount) (output : Fin d.stateCount) :
    (exit d period replay after output).1.data=MaskedCluster.exitOrbit d period replay after output := by
  unfold exit Input.data MaskedCluster.exitOrbit
  congr 1
  funext q
  exact tabulate_get _ q

theorem exit_work (d : DFA α) (period replay after : Map d.stateCount) (output : Fin d.stateCount) :
    (exit d period replay after output).2≤6*d.stateCount+5 := by
  have h:=tabulate_work (fun q=>(decide (after.get q=output),3)) 3 (fun _=>Nat.le_refl _)
  simpa only [exit,Nat.reduceAdd,Nat.mul_comm _ 6] using Nat.add_le_add_right h 4

end REWB.PeriodicConstruction.Masked
