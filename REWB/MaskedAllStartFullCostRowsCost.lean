import REWB.MaskedAllStartFullCostRows
import REWB.MaskedAllStartRowsCost

/-! Full construction work for the executed finite row factories.
All constants below depend only on the fixed automata and a fixed
additional action charge. Executable counters are summed from returned
rows; maxima and asymptotic envelopes occur only in these proofs. -/
namespace REWB.MaskedAllStart.FullCost.Rows.Cost
open REWB.BoundaryRange REWB.BoundaryApplication REWB.OneUseRange
open REWB.MaskedAllStart.Rows
open REWB.ResidualCached.Growth
export REWB.MaskedAllStart.Rows.Cost
  (volume volume_length volume_positive volume_mono coefficient_le sum_charge)
variable {σ : Nat}

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable def rowCoefficient (B C E : DFA (Fin σ)) (charge : Nat) : Nat :=
  Classical.choose (FullCost.solve_charged_work_closed B C E charge)+4

theorem row_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (charge n : Nat) (hn : text.size≤n) :
    (row B C E text fallback source target).2+charge*(row B C E text fallback source target).1.fixedPatternBuilds≤
      rowCoefficient B C E charge*volume n := by
  have hh:=Classical.choose_spec (FullCost.solve_charged_work_closed B C E charge)
    text fallback source target
  have hm:=Nat.mul_le_mul_left
    (Classical.choose (FullCost.solve_charged_work_closed B C E charge)) (volume_mono hn)
  have hv:=volume_positive n
  change (FullCost.solve B C E text fallback source target).2+4+
    charge*(FullCost.solve B C E text fallback source target).1.fixedPatternBuilds≤_
  have hh' : (FullCost.solve B C E text fallback source target).2+
    charge*(FullCost.solve B C E text fallback source target).1.fixedPatternBuilds≤
      Classical.choose (FullCost.solve_charged_work_closed B C E charge)*volume text.size := by
    simpa only [volume,ResidualCached.Growth.height,Nat.mul_assoc] using hh
  unfold rowCoefficient
  rw [Nat.add_mul]
  omega

noncomputable def prefixMaximum (B C E : DFA (Fin σ)) (charge : Nat) : Nat :=
  (List.ofFn fun c : TableColor.Key E=>rowCoefficient B C (FarSelection.variant E c) charge).sum

noncomputable def prefixCoefficient (B C E : DFA (Fin σ)) (charge : Nat) : Nat :=
  TableColor.count E*prefixMaximum B C E charge+33*TableColor.count E+19

theorem prefix_charge (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid charge : Nat) :
    (prefixRows B C E w fallback grid).2+charge*(prefixRows B C E w fallback grid).1.fixedPatternBuilds=
      (List.ofFn fun c : TableColor.Key E=>
        (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
          (full (w.take grid).length) (full (w.take grid).length)).2+
        charge*(row B C (FarSelection.variant E c) (w.take grid).toArray fallback
          (full (w.take grid).length) (full (w.take grid).length)).1.fixedPatternBuilds+3).sum+
          1+10*TableColor.count E+5+20*TableColor.count E+4*(grid+1)+9 := by
  simp only [prefixRows,FullCost.Table.build_work,FullCost.Table.get_build,List.size_toArray]
  have hh:=sum_charge
    (fun c : TableColor.Key E=>
      (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).2+3)
    (fun c : TableColor.Key E=>
      (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).1.fixedPatternBuilds) charge
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    congrArg (fun z=>z+1+10*TableColor.count E+5+20*TableColor.count E+4*(grid+1)+9) hh

theorem prefix_work (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid charge : Nat)
    (hg : grid≤w.length) :
    (prefixRows B C E w fallback grid).2+charge*(prefixRows B C E w fallback grid).1.fixedPatternBuilds≤
      prefixCoefficient B C E charge*volume w.length := by
  have each : ∀c : TableColor.Key E,
      (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).2+
      charge*(row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).1.fixedPatternBuilds+3≤
          prefixMaximum B C E charge*volume w.length+3 := by
    intro c
    have hh:=row_work B C (FarSelection.variant E c) (w.take grid).toArray fallback
      (full (w.take grid).length) (full (w.take grid).length) charge w.length
      (by simp only [List.size_toArray,List.length_take]; omega)
    have hm:=Nat.mul_le_mul_right (volume w.length)
      (coefficient_le (fun c : TableColor.Key E=>rowCoefficient B C (FarSelection.variant E c) charge) c)
    change rowCoefficient B C (FarSelection.variant E c) charge*volume w.length≤
      prefixMaximum B C E charge*volume w.length at hm
    omega
  have summed : (List.ofFn fun c : TableColor.Key E=>
      (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).2+
      charge*(row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).1.fixedPatternBuilds+3).sum≤
      TableColor.count E*(prefixMaximum B C E charge*volume w.length+3) :=
    BoundaryRange.Table.sum_ofFn_le _ _ each
  have hv:=volume_positive w.length
  have hn:=volume_length w.length
  have hc:=Nat.mul_le_mul_left (33*TableColor.count E) hv
  rw [prefix_charge]
  unfold prefixCoefficient
  simp only [Nat.mul_one,Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at hc summed ⊢
  omega

theorem table_charge {m : Nat} {X : Type} (make : Fin m→(X×Nat)×Nat)
    (calls : X→Nat) (charge : Nat) :
    (FullCost.Table.build make).2+
      charge*(List.ofFn fun i=>calls (BoundaryRange.Table.get (FullCost.Table.build make).1 i)).sum=
      (List.ofFn fun i=>(make i).2+charge*calls (make i).1.1+3).sum+1+10*m+5 := by
  simp only [FullCost.Table.build_work,FullCost.Table.get_build]
  have hh:=sum_charge (fun i=>(make i).2+3) (fun i=>calls (make i).1.1) charge
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    congrArg (fun z=>z+1+10*m+5) hh

theorem table_work {m : Nat} {X : Type} (make : Fin m→(X×Nat)×Nat)
    (calls : X→Nat) (charge bound : Nat)
    (hm : ∀i,(make i).2+charge*calls (make i).1.1≤bound) :
    (FullCost.Table.build make).2+
      charge*(List.ofFn fun i=>calls (BoundaryRange.Table.get (FullCost.Table.build make).1 i)).sum≤
      m*(bound+3)+1+10*m+5 := by
  rw [table_charge]
  have ht:=BoundaryRange.Table.sum_ofFn_le (bound+3)
    (fun i=>(make i).2+charge*calls (make i).1.1+3)
    (fun i=>Nat.add_le_add_right (hm i) 3)
  omega

theorem grid_work {m : Nat} {X : Type} (make : Fin m→(X×Nat)×Nat)
    (calls : X→Nat) (charge coefficient vol overhead extra : Nat)
    (hm : ∀i,(make i).2+charge*calls (make i).1.1≤coefficient*vol+3)
    (hv : 1≤vol) (hmpos : 1≤m) (ho : overhead+6≤extra*vol) :
    (FullCost.Table.build make).2+12*m+overhead+
      charge*(List.ofFn fun i=>calls (BoundaryRange.Table.get (FullCost.Table.build make).1 i)).sum≤
        (coefficient+28+extra)*vol*m := by
  have ht:=table_work make calls charge (coefficient*vol+3) hm
  have hc:=Nat.mul_le_mul_right m (Nat.mul_le_mul_left 28 hv)
  have he:=Nat.mul_le_mul_left (extra*vol) hmpos
  simp only [Nat.mul_one,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,
    Nat.mul_comm,Nat.mul_left_comm] at ht hc he ho ⊢
  omega

noncomputable def forwardCoefficient (B C E : DFA (Fin σ)) (charge : Nat) : Nat :=
  prefixCoefficient B C E charge+39

theorem forward_work (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (forward B C E w fallback width).2+charge*(forward B C E w fallback width).1.fixedPatternBuilds≤
      forwardCoefficient B C E charge*volume w.length*(w.length/width+2) := by
  have hh:=grid_work
    (fun slot : Fin (Grid.count w.length width)=>
      let out:=prefixRows B C E w fallback (Grid.position w.length width slot.val)
      ((out.1,out.1.work+3),out.2+3)) Prefix.fixedPatternBuilds charge (prefixCoefficient B C E charge)
      (volume w.length) 5 11 (by
        intro slot
        have hp:=prefix_work B C E w fallback (Grid.position w.length width slot.val) charge
          (Grid.position_bound _ _ _)
        dsimp only
        omega)
      (volume_positive _) (by exact Nat.le_trans (by decide : 1≤2) (Nat.le_add_left 2 _))
      (by have hv:=volume_positive w.length; omega)
  simpa only [forward,forwardCoefficient,Grid.count,Nat.add_assoc,Nat.reduceAdd] using hh

noncomputable def backwardCoefficient (A B C : DFA (Fin σ)) (charge : Nat) : Nat :=
  prefixCoefficient (Automata.reverse B) (Automata.reverse C) (Automata.reverse A) charge+42

theorem backward_work (A B C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (backward A B C w fallback width).2+charge*(backward A B C w fallback width).1.fixedPatternBuilds≤
      backwardCoefficient A B C charge*volume w.length*(w.length/width+2) := by
  have hh:=grid_work
    (fun slot : Fin (Grid.count w.length width)=>
      let out:=prefixRows (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
        w.reverse fallback (Grid.backward w.length width slot.val)
      ((out.1,out.1.work+3),out.2+3)) Prefix.fixedPatternBuilds charge
      (prefixCoefficient (Automata.reverse B) (Automata.reverse C) (Automata.reverse A) charge)
      (volume w.length) (2*w.length+8) 14 (by
        intro slot
        have hp:=prefix_work (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
          w.reverse fallback (Grid.backward w.length width slot.val) charge
          (by simp only [List.length_reverse,Grid.backward]; omega)
        rw [List.length_reverse] at hp
        dsimp only
        omega)
      (volume_positive _) (by exact Nat.le_trans (by decide : 1≤2) (Nat.le_add_left 2 _))
      (by have hv:=volume_length w.length; omega)
  simpa only [backward,backwardCoefficient,Grid.count,Nat.add_assoc,Nat.reduceAdd] using hh

export REWB.MaskedAllStart.Rows.Cost (farPreparationCoefficient far_prepare_work)

noncomputable def farMaximum (A B C K D : DFA (Fin σ)) (charge : Nat) : Nat :=
  (List.ofFn fun k : Fin K.stateCount=>rowCoefficient (Automata.reverse B)
    (Automata.reverse (Automata.gap C K D C.initial k)) (Automata.reverse A) charge).sum

noncomputable def farCoefficient (A B C K D : DFA (Fin σ)) (charge : Nat) : Nat :=
  farPreparationCoefficient K+K.stateCount*K.stateCount*farMaximum A B C K D charge+
    39*K.stateCount*K.stateCount+42*K.stateCount+24

theorem far_work (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (grid charge : Nat) :
    (far A B C K D w fallback grid).2+charge*(far A B C K D w fallback grid).1.fixedPatternBuilds≤
      farCoefficient A B C K D charge*volume w.length := by
  let requests:=FarRight.prepare K w grid
  let make:=fun (q k : Fin K.stateCount)=>
    let target:=(BoundaryRange.Table.get (BoundaryRange.Table.get requests.masks q) k).bits.toArray
    let gap:=Automata.reverse (Automata.gap C K D C.initial k)
    let out:=row (Automata.reverse B) gap (Automata.reverse A) w.reverse.toArray fallback (full w.length) target
    ((out.1,out.1.work+6),out.2+6)
  let inner:=fun q=>FullCost.Table.build (make q)
  let calls:=fun idx : BoundaryRange.Table.Index (fun _ : Fin K.stateCount=>Row)=>
    (List.ofFn fun k=>(BoundaryRange.Table.get idx k).fixedPatternBuilds).sum
  have each (q : Fin K.stateCount) :
      (inner q).2+charge*calls (inner q).1≤
        K.stateCount*(farMaximum A B C K D charge*volume w.length+19)+6 := by
    have ht:=table_work (make q) Row.fixedPatternBuilds charge
      (farMaximum A B C K D charge*volume w.length+6) (by
        intro k
        have hh:=row_work (Automata.reverse B) (Automata.reverse (Automata.gap C K D C.initial k))
          (Automata.reverse A) w.reverse.toArray fallback (full w.length)
          (BoundaryRange.Table.get (BoundaryRange.Table.get requests.masks q) k).bits.toArray charge w.length
          (by simp only [List.size_toArray,List.length_reverse,Nat.le_refl])
        have hm:=Nat.mul_le_mul_right (volume w.length)
          (coefficient_le (fun k : Fin K.stateCount=>rowCoefficient (Automata.reverse B)
            (Automata.reverse (Automata.gap C K D C.initial k)) (Automata.reverse A) charge) k)
        change rowCoefficient (Automata.reverse B) (Automata.reverse (Automata.gap C K D C.initial k))
          (Automata.reverse A) charge*volume w.length≤farMaximum A B C K D charge*volume w.length at hm
        dsimp only [make]
        omega)
    change (inner q).2+charge*calls (inner q).1≤_ at ht
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc] at ht ⊢
    omega
  have outer:=table_work
    (fun q : Fin K.stateCount=>(((inner q).1,(inner q).1.work+3),(inner q).2+3)) calls charge
    (K.stateCount*(farMaximum A B C K D charge*volume w.length+19)+9) (by
      intro q
      have hh:=each q
      dsimp only
      omega)
  have hp:=far_prepare_work K w grid
  have hv:=volume_positive w.length
  have hn:=volume_length w.length
  have hc:=Nat.mul_le_mul_left (39*K.stateCount*K.stateCount+42*K.stateCount) hv
  change requests.work+(FullCost.Table.build
      (fun q : Fin K.stateCount=>(((inner q).1,(inner q).1.work+3),(inner q).2+3))).2+
      20*K.stateCount*(K.stateCount+1)+6*(w.length+1)+12+
      charge*(List.ofFn fun q=>calls (BoundaryRange.Table.get (FullCost.Table.build
        (fun q : Fin K.stateCount=>(((inner q).1,(inner q).1.work+3),(inner q).2+3))).1 q)).sum≤_
  change requests.work≤farPreparationCoefficient K*volume w.length at hp
  unfold farCoefficient
  simp only [Nat.mul_one,Nat.one_mul,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,
    Nat.mul_left_comm _ 10,Nat.mul_comm _ 10,Nat.mul_left_comm _ 12,Nat.mul_comm _ 12,
    Nat.mul_left_comm _ 19,Nat.mul_comm _ 19,Nat.mul_left_comm _ 20,Nat.mul_comm _ 20,
    Nat.mul_left_comm _ 39,Nat.mul_comm _ 39,Nat.mul_left_comm _ 42,Nat.mul_comm _ 42] at outer hc ⊢
  omega

noncomputable def boundaryCoefficient (A B C K D : DFA (Fin σ)) (charge : Nat) : Nat :=
  farCoefficient A B C K D charge+39

theorem boundary_work (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (boundary A B C K D w fallback width).2+charge*(boundary A B C K D w fallback width).1.fixedPatternBuilds≤
      boundaryCoefficient A B C K D charge*volume w.length*(w.length/width+2) := by
  have hh:=grid_work
    (fun slot : Fin (CacheGrid.count w.length width)=>
      let out:=far A B C K D w fallback (CacheGrid.upper w.length width slot.val)
      ((out.1,out.1.work+3),out.2+3)) Far.fixedPatternBuilds charge (farCoefficient A B C K D charge)
      (volume w.length) 5 11 (by
        intro slot
        have hp:=far_work A B C K D w fallback (CacheGrid.upper w.length width slot.val) charge
        dsimp only
        omega)
      (volume_positive _) (by exact Nat.le_trans (by decide : 1≤2) (Nat.le_add_left 2 _))
      (by have hv:=volume_positive w.length; omega)
  simpa only [boundary,boundaryCoefficient,CacheGrid.count,Grid.count,Nat.add_assoc,Nat.reduceAdd] using hh

theorem far_profile (A B C K D : DFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat),
      Bound w.length 1 ((far A B C K D w fallback grid).2+
        charge*(far A B C K D w fallback grid).1.fixedPatternBuilds) 1 0 0 3 coefficient := by
  refine ⟨farCoefficient A B C K D charge,?_⟩
  intro w fallback grid
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,volume,Nat.mul_assoc] using
    far_work A B C K D w fallback grid charge

theorem forward_profile (B C E : DFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (width : Nat),
      Bound w.length width ((forward B C E w fallback width).2+
        charge*(forward B C E w fallback width).1.fixedPatternBuilds) 1 0 1 3 coefficient := by
  refine ⟨forwardCoefficient B C E charge,?_⟩
  intro w fallback width
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,volume,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using forward_work B C E w fallback width charge

theorem backward_profile (A B C : DFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (width : Nat),
      Bound w.length width ((backward A B C w fallback width).2+
        charge*(backward A B C w fallback width).1.fixedPatternBuilds) 1 0 1 3 coefficient := by
  refine ⟨backwardCoefficient A B C charge,?_⟩
  intro w fallback width
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,volume,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using backward_work A B C w fallback width charge

theorem boundary_profile (A B C K D : DFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (width : Nat),
      Bound w.length width ((boundary A B C K D w fallback width).2+
        charge*(boundary A B C K D w fallback width).1.fixedPatternBuilds) 1 0 1 3 coefficient := by
  refine ⟨boundaryCoefficient A B C K D charge,?_⟩
  intro w fallback width
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,volume,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using boundary_work A B C K D w fallback width charge

end REWB.MaskedAllStart.FullCost.Rows.Cost
