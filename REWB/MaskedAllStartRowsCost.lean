import REWB.MaskedAllStartRowsCorrect
import REWB.MaskedTraversalExecuteCostGrowth

/-! Actual row-production bounds. Coefficients below are proof-only
fixed-pattern envelopes; the executable producers retain and add their
real returned counters. In particular, no cache caller supplies a row
cost function. Every fixed action charge is carried through all tables.
-/
namespace REWB.MaskedAllStart.Rows.Cost
open REWB.BoundaryRange REWB.BoundaryApplication REWB.OneUseRange
open REWB.ResidualCached.Growth
variable {σ : Nat}

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def volume (n : Nat) : Nat := (n+2)*(ResidualCached.Growth.height n)^3

theorem volume_length (n : Nat) : n+2≤volume n := by
  have hp : 1≤(ResidualCached.Growth.height n)^3 := Nat.pow_pos (by unfold ResidualCached.Growth.height; omega)
  simpa only [Nat.mul_one,volume] using Nat.mul_le_mul_left (n+2) hp

theorem volume_positive (n : Nat) : 1≤volume n := by have hh:=volume_length n; omega

theorem volume_mono {m n : Nat} (hm : m≤n) : volume m≤volume n := by
  apply Nat.mul_le_mul (by omega)
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (CountedJoin.log2_mono (by omega : m+2≤n+2)) 1

theorem member_le_sum (xs : List Nat) (x : Nat) (hx : x∈xs) : x≤xs.sum := by
  induction xs with
  | nil=>cases hx
  | cons a xs ih=>
    rcases List.mem_cons.mp hx with he|he
    · subst x; simp only [List.sum_cons]; omega
    · have hh:=ih he; simp only [List.sum_cons]; omega

theorem coefficient_le {m : Nat} (f : Fin m→Nat) (i : Fin m) : f i≤(List.ofFn f).sum :=
  member_le_sum _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem sum_charge {m : Nat} (f g : Fin m→Nat) (charge : Nat) :
    (List.ofFn f).sum+charge*(List.ofFn g).sum=(List.ofFn fun i=>f i+charge*g i).sum := by
  induction m with
  | zero=>simp only [List.ofFn_zero,List.sum_nil,Nat.mul_zero,Nat.zero_add]
  | succ m ih=>
    rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ,List.sum_cons,List.sum_cons,List.sum_cons,Nat.mul_add]
    have hh:=ih (fun i=>f i.succ) (fun i=>g i.succ)
    omega

noncomputable def rowCoefficient (B C E : DFA (Fin σ)) (charge : Nat) : Nat :=
  Classical.choose (MaskedTraversalExecute.Cost.solve_charged_work_closed B C E charge)+4

theorem row_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (charge n : Nat) (hn : text.size≤n) :
    (row B C E text fallback source target).work+charge*(row B C E text fallback source target).fixedPatternBuilds≤
      rowCoefficient B C E charge*volume n := by
  have hh:=Classical.choose_spec (MaskedTraversalExecute.Cost.solve_charged_work_closed B C E charge)
    text fallback source target
  have hm:=Nat.mul_le_mul_left
    (Classical.choose (MaskedTraversalExecute.Cost.solve_charged_work_closed B C E charge)) (volume_mono hn)
  have hv:=volume_positive n
  change (MaskedAllStart.solve B C E text fallback source target).accountedWork+4+
    charge*(MaskedAllStart.solve B C E text fallback source target).fixedPatternBuilds≤_
  have hh' : (MaskedAllStart.solve B C E text fallback source target).accountedWork+
    charge*(MaskedAllStart.solve B C E text fallback source target).fixedPatternBuilds≤
      Classical.choose (MaskedTraversalExecute.Cost.solve_charged_work_closed B C E charge)*volume text.size := by
    simpa only [volume,ResidualCached.Growth.height,Nat.mul_assoc] using hh
  unfold rowCoefficient
  rw [Nat.add_mul]
  omega

noncomputable def prefixMaximum (B C E : DFA (Fin σ)) (charge : Nat) : Nat :=
  (List.ofFn fun c : TableColor.Key E=>rowCoefficient B C (FarSelection.variant E c) charge).sum

noncomputable def prefixCoefficient (B C E : DFA (Fin σ)) (charge : Nat) : Nat :=
  TableColor.count E*prefixMaximum B C E charge+23*TableColor.count E+14

theorem prefix_charge (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid charge : Nat) :
    (prefixRows B C E w fallback grid).work+charge*(prefixRows B C E w fallback grid).fixedPatternBuilds=
      (List.ofFn fun c : TableColor.Key E=>
        (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
          (full (w.take grid).length) (full (w.take grid).length)).work+
        charge*(row B C (FarSelection.variant E c) (w.take grid).toArray fallback
          (full (w.take grid).length) (full (w.take grid).length)).fixedPatternBuilds+3).sum+
          1+20*TableColor.count E+4*(grid+1)+9 := by
  simp only [prefixRows,Table.build_work,Table.get_build,List.size_toArray]
  have hh:=sum_charge
    (fun c : TableColor.Key E=>
      (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).work+3)
    (fun c : TableColor.Key E=>
      (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).fixedPatternBuilds) charge
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    congrArg (fun z=>z+1+20*TableColor.count E+4*(grid+1)+9) hh

theorem prefix_work (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid charge : Nat)
    (hg : grid≤w.length) :
    (prefixRows B C E w fallback grid).work+charge*(prefixRows B C E w fallback grid).fixedPatternBuilds≤
      prefixCoefficient B C E charge*volume w.length := by
  have each : ∀c : TableColor.Key E,
      (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).work+
      charge*(row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).fixedPatternBuilds+3≤
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
        (full (w.take grid).length) (full (w.take grid).length)).work+
      charge*(row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).fixedPatternBuilds+3).sum≤
      TableColor.count E*(prefixMaximum B C E charge*volume w.length+3) :=
    Table.sum_ofFn_le _ _ each
  have hv:=volume_positive w.length
  have hn:=volume_length w.length
  have hc:=Nat.mul_le_mul_left (23*TableColor.count E) hv
  rw [prefix_charge]
  unfold prefixCoefficient
  simp only [Nat.mul_one,Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at hc summed ⊢
  omega

/-- Charge the fixed constructions stored in the already materialized
table. This identity reads each returned ledger and does not call the
factory a second time in the executable producer. -/
theorem table_charge {m : Nat} {X : Type} (make : Fin m→X×Nat)
    (calls : X→Nat) (charge : Nat) :
    (Table.build make).work+charge*(List.ofFn fun i=>calls (Table.get (Table.build make) i)).sum=
      (List.ofFn fun i=>(make i).2+charge*calls (make i).1+3).sum+1 := by
  simp only [Table.build_work,Table.get_build]
  calc
    (List.ofFn fun i=>(make i).2+3).sum+1+charge*(List.ofFn fun i=>calls (make i).1).sum=
        ((List.ofFn fun i=>(make i).2+3).sum+charge*(List.ofFn fun i=>calls (make i).1).sum)+1 := by omega
    _=(List.ofFn fun i=>((make i).2+3)+charge*calls (make i).1).sum+1 :=
      congrArg (fun z=>z+1) (sum_charge (fun i=>(make i).2+3) (fun i=>calls (make i).1) charge)
    _=(List.ofFn fun i=>(make i).2+charge*calls (make i).1+3).sum+1 := by
      congr 3
      funext i
      omega

theorem table_work {m : Nat} {X : Type} (make : Fin m→X×Nat)
    (calls : X→Nat) (charge bound : Nat)
    (hm : ∀i,(make i).2+charge*calls (make i).1≤bound) :
    (Table.build make).work+charge*(List.ofFn fun i=>calls (Table.get (Table.build make) i)).sum≤
      m*(bound+3)+1 := by
  rw [table_charge]
  exact Nat.add_le_add_right (Table.sum_ofFn_le _ _
    (fun i=>Nat.add_le_add_right (hm i) 3)) 1

/-- A common outer-grid summation, including table headers, reads and
the producer's scalar/bitmap overhead. -/
theorem grid_work {m : Nat} {X : Type} (make : Fin m→X×Nat)
    (calls : X→Nat) (charge coefficient vol overhead extra : Nat)
    (hm : ∀i,(make i).2+charge*calls (make i).1≤coefficient*vol+3)
    (hv : 1≤vol) (hmpos : 1≤m) (ho : overhead+1≤extra*vol) :
    (Table.build make).work+12*m+overhead+
      charge*(List.ofFn fun i=>calls (Table.get (Table.build make) i)).sum≤
        (coefficient+18+extra)*vol*m := by
  have ht:=table_work make calls charge (coefficient*vol+3) hm
  have hc:=Nat.mul_le_mul_right m (Nat.mul_le_mul_left 18 hv)
  have he:=Nat.mul_le_mul_left (extra*vol) hmpos
  simp only [Nat.mul_one,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,
    Nat.mul_comm,Nat.mul_left_comm] at ht hc he ho ⊢
  omega

noncomputable def forwardCoefficient (B C E : DFA (Fin σ)) (charge : Nat) : Nat :=
  prefixCoefficient B C E charge+24

theorem forward_work (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (forward B C E w fallback width).work+charge*(forward B C E w fallback width).fixedPatternBuilds≤
      forwardCoefficient B C E charge*volume w.length*(w.length/width+2) := by
  have hh:=grid_work
    (fun slot : Fin (Grid.count w.length width)=>
      let out:=prefixRows B C E w fallback (Grid.position w.length width slot.val)
      (out,out.work+3)) Prefix.fixedPatternBuilds charge (prefixCoefficient B C E charge)
      (volume w.length) 5 6 (by
        intro slot
        have hp:=prefix_work B C E w fallback (Grid.position w.length width slot.val) charge
          (Grid.position_bound _ _ _)
        dsimp only
        omega)
      (volume_positive _) (by exact Nat.le_trans (by decide : 1≤2) (Nat.le_add_left 2 _))
      (by have hv:=volume_positive w.length; omega)
  simpa only [forward,forwardCoefficient,Grid.count,Nat.add_assoc,Nat.reduceAdd] using hh

noncomputable def backwardCoefficient (A B C : DFA (Fin σ)) (charge : Nat) : Nat :=
  prefixCoefficient (Automata.reverse B) (Automata.reverse C) (Automata.reverse A) charge+27

theorem backward_work (A B C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (backward A B C w fallback width).work+charge*(backward A B C w fallback width).fixedPatternBuilds≤
      backwardCoefficient A B C charge*volume w.length*(w.length/width+2) := by
  have hh:=grid_work
    (fun slot : Fin (Grid.count w.length width)=>
      let out:=prefixRows (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
        w.reverse fallback (Grid.backward w.length width slot.val)
      (out,out.work+3)) Prefix.fixedPatternBuilds charge
      (prefixCoefficient (Automata.reverse B) (Automata.reverse C) (Automata.reverse A) charge)
      (volume w.length) (2*w.length+8) 9 (by
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

theorem far_prepare_profile (K : DFA (Fin σ)) :
    ∃coefficient,∀n s,Bound n s (FarRight.prepareBudget K n) 1 0 0 3 coefficient := by
  refine ⟨?C,?proof⟩
  case proof=>
    intro n s
    residual_growth

noncomputable def farPreparationCoefficient (K : DFA (Fin σ)) : Nat :=
  Classical.choose (far_prepare_profile K)

theorem far_prepare_work (K : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) :
    (FarRight.prepare K w grid).work≤farPreparationCoefficient K*volume w.length := by
  have hh:=Classical.choose_spec (far_prepare_profile K) w.length 1
  have hp:=Nat.le_trans (FarRight.prepare_work K w grid) hh
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,farPreparationCoefficient,volume,
    Nat.mul_assoc] using hp

noncomputable def farMaximum (A B C K D : DFA (Fin σ)) (charge : Nat) : Nat :=
  (List.ofFn fun k : Fin K.stateCount=>rowCoefficient (Automata.reverse B)
    (Automata.reverse (Automata.gap C K D C.initial k)) (Automata.reverse A) charge).sum

noncomputable def farCoefficient (A B C K D : DFA (Fin σ)) (charge : Nat) : Nat :=
  farPreparationCoefficient K+K.stateCount*K.stateCount*farMaximum A B C K D charge+
    29*K.stateCount*K.stateCount+27*K.stateCount+20

theorem far_work (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (grid charge : Nat) :
    (far A B C K D w fallback grid).work+charge*(far A B C K D w fallback grid).fixedPatternBuilds≤
      farCoefficient A B C K D charge*volume w.length := by
  let requests:=FarRight.prepare K w grid
  let make:=fun (q k : Fin K.stateCount)=>
    let target:=(Table.get (Table.get requests.masks q) k).bits.toArray
    let gap:=Automata.reverse (Automata.gap C K D C.initial k)
    let out:=row (Automata.reverse B) gap (Automata.reverse A) w.reverse.toArray fallback (full w.length) target
    (out,out.work+6)
  let inner:=fun q=>Table.build (make q)
  let calls:=fun idx : Table.Index (fun _ : Fin K.stateCount=>Row)=>
    (List.ofFn fun k=>(Table.get idx k).fixedPatternBuilds).sum
  have each (q : Fin K.stateCount) :
      (inner q).work+charge*calls (inner q)≤
        K.stateCount*(farMaximum A B C K D charge*volume w.length+9)+1 := by
    apply table_work (make q) Row.fixedPatternBuilds charge (farMaximum A B C K D charge*volume w.length+6)
    intro k
    have hh:=row_work (Automata.reverse B) (Automata.reverse (Automata.gap C K D C.initial k))
      (Automata.reverse A) w.reverse.toArray fallback (full w.length)
      (Table.get (Table.get requests.masks q) k).bits.toArray charge w.length
      (by simp only [List.size_toArray,List.length_reverse,Nat.le_refl])
    have hm:=Nat.mul_le_mul_right (volume w.length)
      (coefficient_le (fun k : Fin K.stateCount=>rowCoefficient (Automata.reverse B)
        (Automata.reverse (Automata.gap C K D C.initial k)) (Automata.reverse A) charge) k)
    change rowCoefficient (Automata.reverse B) (Automata.reverse (Automata.gap C K D C.initial k))
      (Automata.reverse A) charge*volume w.length≤farMaximum A B C K D charge*volume w.length at hm
    dsimp only [make]
    omega
  have outer:=table_work (fun q : Fin K.stateCount=>(inner q,(inner q).work+3)) calls charge
    (K.stateCount*(farMaximum A B C K D charge*volume w.length+9)+4) (by
      intro q
      have hh:=each q
      dsimp only
      omega)
  have hp:=far_prepare_work K w grid
  have hv:=volume_positive w.length
  have hn:=volume_length w.length
  have hc:=Nat.mul_le_mul_left (29*K.stateCount*K.stateCount+27*K.stateCount) hv
  change (far A B C K D w fallback grid).work+
    charge*(far A B C K D w fallback grid).fixedPatternBuilds≤_
  change requests.work+(Table.build (fun q : Fin K.stateCount=>(inner q,(inner q).work+3))).work+
      20*K.stateCount*(K.stateCount+1)+6*(w.length+1)+12+
      charge*(List.ofFn fun q=>calls (Table.get (Table.build
        (fun q : Fin K.stateCount=>(inner q,(inner q).work+3))) q)).sum≤_
  change requests.work≤farPreparationCoefficient K*volume w.length at hp
  unfold farCoefficient
  simp only [Nat.mul_one,Nat.one_mul,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,
    Nat.mul_left_comm _ 9,Nat.mul_comm _ 9,Nat.mul_left_comm _ 20,Nat.mul_comm _ 20,
    Nat.mul_left_comm _ 27,Nat.mul_comm _ 27,Nat.mul_left_comm _ 29,Nat.mul_comm _ 29] at outer hc ⊢
  omega

noncomputable def boundaryCoefficient (A B C K D : DFA (Fin σ)) (charge : Nat) : Nat :=
  farCoefficient A B C K D charge+24

theorem boundary_work (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width charge : Nat) :
    (boundary A B C K D w fallback width).work+charge*(boundary A B C K D w fallback width).fixedPatternBuilds≤
      boundaryCoefficient A B C K D charge*volume w.length*(w.length/width+2) := by
  have hh:=grid_work
    (fun slot : Fin (CacheGrid.count w.length width)=>
      let out:=far A B C K D w fallback (CacheGrid.upper w.length width slot.val)
      (out,out.work+3)) Far.fixedPatternBuilds charge (farCoefficient A B C K D charge)
      (volume w.length) 5 6 (by
        intro slot
        have hp:=far_work A B C K D w fallback (CacheGrid.upper w.length width slot.val) charge
        dsimp only
        omega)
      (volume_positive _) (by exact Nat.le_trans (by decide : 1≤2) (Nat.le_add_left 2 _))
      (by have hv:=volume_positive w.length; omega)
  simpa only [boundary,boundaryCoefficient,CacheGrid.count,Grid.count,Nat.add_assoc,Nat.reduceAdd] using hh

theorem far_profile (A B C K D : DFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat),
      Bound w.length 1 ((far A B C K D w fallback grid).work+
        charge*(far A B C K D w fallback grid).fixedPatternBuilds) 1 0 0 3 coefficient := by
  refine ⟨farCoefficient A B C K D charge,?_⟩
  intro w fallback grid
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,volume,Nat.mul_assoc] using
    far_work A B C K D w fallback grid charge

theorem forward_profile (B C E : DFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (width : Nat),
      Bound w.length width ((forward B C E w fallback width).work+
        charge*(forward B C E w fallback width).fixedPatternBuilds) 1 0 1 3 coefficient := by
  refine ⟨forwardCoefficient B C E charge,?_⟩
  intro w fallback width
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,volume,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using forward_work B C E w fallback width charge

theorem backward_profile (A B C : DFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (width : Nat),
      Bound w.length width ((backward A B C w fallback width).work+
        charge*(backward A B C w fallback width).fixedPatternBuilds) 1 0 1 3 coefficient := by
  refine ⟨backwardCoefficient A B C charge,?_⟩
  intro w fallback width
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,volume,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using backward_work A B C w fallback width charge

theorem boundary_profile (A B C K D : DFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(w : Word (Fin σ)) (fallback : Fin σ) (width : Nat),
      Bound w.length width ((boundary A B C K D w fallback width).work+
        charge*(boundary A B C K D w fallback width).fixedPatternBuilds) 1 0 1 3 coefficient := by
  refine ⟨boundaryCoefficient A B C K D charge,?_⟩
  intro w fallback width
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,volume,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using boundary_work A B C K D w fallback width charge

end REWB.MaskedAllStart.Rows.Cost
