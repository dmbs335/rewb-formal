import REWB.PhaseBounds

/-! Cache all period-block and residual DFA transitions by starting phase
    and starting state. A fixed-phase descriptor can then be constructed
    without scanning any string of length q. The cache itself performs
    exactly q*q*stateCount character transitions. -/
namespace REWB.PeriodicCache
open REWB.Periodic
variable {α : Type}

abbrev StateRow (d : DFA α) := Array (Fin d.stateCount)
abbrev PhaseRow (d : DFA α) := Array (StateRow d)
abbrev Table (d : DFA α) := Array (PhaseRow d)

def state (d : DFA α) (i : Nat) : Fin d.stateCount :=
  if h : i<d.stateCount then ⟨i,h⟩ else d.initial

theorem state_val (d : DFA α) (q : Fin d.stateCount) :
    state d q.val=q := by
  unfold state
  rw [dif_pos q.isLt]

def countedMap (f : X→Y×Nat) : List X→List Y×Nat
  | [] => ([],0)
  | x::xs =>
    let a := f x
    let b := countedMap f xs
    (a.1::b.1,a.2+b.2)

theorem countedMap_values (f : X→Y×Nat) (xs : List X) :
    (countedMap f xs).1=xs.map (fun x=>(f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (f x).1::(countedMap f xs).1=_
    rw [ih]
    rfl

theorem countedMap_cost (f : X→Y×Nat) (xs : List X) (c : Nat)
    (h : ∀ x,x∈xs→(f x).2=c) :
    (countedMap f xs).2=xs.length*c := by
  induction xs with
  | nil => simp [countedMap]
  | cons x xs ih =>
    change (f x).2+(countedMap f xs).2=(xs.length+1)*c
    rw [h x (by simp),ih (fun y hy=>h y (by simp [hy])),Nat.add_mul,Nat.one_mul]
    omega

def buildPhase (d : DFA α) (s : Nat→α) (q a : Nat) : PhaseRow d × Nat :=
  let w := segment s a q
  let t := countedMap (fun i=>
    let r := IntervalDFA.countedPrefix d (state d i) w
    (r.1.toArray,r.2)) (List.range d.stateCount)
  (t.1.toArray,t.2)

theorem buildPhase_cost (d : DFA α) (s : Nat→α) (q a : Nat) :
    (buildPhase d s q a).2=d.stateCount*q := by
  unfold buildPhase
  rw [countedMap_cost _ _ q]
  · rw [List.length_range]
  · intro i _
    change (IntervalDFA.countedPrefix d (state d i) (segment s a q)).2=q
    rw [IntervalDFA.countedPrefix_spec,segment_length]

def build (d : DFA α) (s : Nat→α) (q : Nat) : Table d × Nat :=
  let t := countedMap (buildPhase d s q) (List.range q)
  (t.1.toArray,t.2)

theorem build_cost (d : DFA α) (s : Nat→α) (q : Nat) :
    (build d s q).2=q*(d.stateCount*q) := by
  unfold build
  rw [countedMap_cost _ _ (d.stateCount*q)]
  · rw [List.length_range]
  · intro a _
    exact buildPhase_cost d s q a

def lookup (d : DFA α) (T : Table d) (a r : Nat) (v : Fin d.stateCount) :
    Option (Fin d.stateCount) := do
  let ph ← T[a]?
  let row ← ph[v.val]?
  row[r]?

private theorem segment_take (s : Nat→α) (a q r : Nat) (hr : r≤q) :
    (segment s a q).take r=segment s a r := by
  induction r generalizing a q with
  | zero => rfl
  | succ r ih =>
    cases q with
    | zero => omega
    | succ q =>
      change s a::(segment s (a+1) q).take r=s a::segment s (a+1) r
      rw [ih _ _ (by omega)]

theorem phase_get (d : DFA α) (s : Nat→α) (q a : Nat) (v : Fin d.stateCount) :
    (buildPhase d s q a).1[v.val]? =
      some ((MaskScan.prefixStates d v (segment s a q)).toArray) := by
  unfold buildPhase
  simp only [List.getElem?_toArray,countedMap_values,List.getElem?_map,
    List.getElem?_range,v.isLt,if_true,Option.map,IntervalDFA.countedPrefix_spec,state_val]

theorem lookup_correct (d : DFA α) (s : Nat→α) (q a r : Nat) (v : Fin d.stateCount)
    (ha : a<q) (hr : r≤q) :
    lookup d (build d s q).1 a r v=some (d.run v (segment s a r)) := by
  unfold lookup build
  simp only [List.getElem?_toArray,countedMap_values,List.getElem?_map,
    List.getElem?_range,ha,if_true,Option.map]
  change ((buildPhase d s q a).1[v.val]?).bind (fun row=>row[r]?)=_
  rw [phase_get]
  change ((MaskScan.prefixStates d v (segment s a q)).toArray)[r]?=_
  rw [List.getElem?_toArray,MaskScan.prefixStates_get d _ r (by rw [segment_length]; exact hr),
    segment_take s a q r hr]

def stateAt (d : DFA α) (T : Table d) (a r : Nat) (v : Fin d.stateCount) : Fin d.stateCount :=
  (lookup d T a r v).getD d.initial

theorem stateAt_correct (d : DFA α) (s : Nat→α) (q a r : Nat) (v : Fin d.stateCount)
    (ha : a<q) (hr : r≤q) :
    stateAt d (build d s q).1 a r v=d.run v (segment s a r) := by
  unfold stateAt
  rw [lookup_correct d s q a r v ha hr]
  rfl

def descriptor (d : DFA α) (T : Table d) (q a rho : Nat) :
    Option FiniteOrbit.Descriptor :=
  FiniteOrbit.compress (FiniteRelation.finEnum d.stateCount)
    (fun v=>stateAt d T a q v) d.initial (fun v=>d.final (stateAt d T a rho v))

/-- Equality of the actual descriptor data, not merely of its language. -/
theorem descriptor_correct (d : DFA α) (s : Nat→α) (q a rho : Nat)
    (ha : a<q) (hr : rho≤q) :
    descriptor d (build d s q).1 q a rho=factorDescriptor d s a q rho := by
  have hstep : (fun v=>stateAt d (build d s q).1 a q v) =
      (fun v=>d.run v (segment s a q)) := by
    funext v
    exact stateAt_correct d s q a q v ha (Nat.le_refl _)
  have hfinal : (fun v=>d.final (stateAt d (build d s q).1 a rho v)) =
      (fun v=>d.final (d.run v (segment s a rho))) := by
    funext v
    rw [stateAt_correct d s q a rho v ha hr]
  unfold descriptor factorDescriptor
  rw [hstep,hfinal]

end REWB.PeriodicCache
