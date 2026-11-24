import REWB.KeyedJoin

/-! Materialized DFA prefix and suffix vectors for a cut. A source
    carries the state reached at the cut; a target carries every state
    that accepts the suffix from the cut to the target. These vectors
    avoid a separate string scan for every event. -/
namespace REWB.DFACut
open REWB.Spec (slice)
variable {α : Type}

abbrev Row (d : DFA α) := Array (Fin d.stateCount)

def vector (d : DFA α) (f : Fin d.stateCount→Fin d.stateCount) : Row d :=
  ((List.range d.stateCount).map (fun i=>f (PeriodicCache.state d i))).toArray

def read (d : DFA α) (r : Row d) (q : Fin d.stateCount) : Fin d.stateCount :=
  (r[q.val]?).getD d.initial

theorem read_vector (d : DFA α) (f : Fin d.stateCount→Fin d.stateCount) (q : Fin d.stateCount) :
    read d (vector d f) q=f q := by
  unfold read vector
  simp only [List.getElem?_toArray,List.getElem?_map,List.getElem?_range,q.isLt,
    if_true,Option.map,PeriodicCache.state_val,Option.getD]

def suffixRows (d : DFA α) : Word α→List (Row d)
  | [] => [vector d id]
  | c::cs =>
    let rest := suffixRows d cs
    let r := rest.headD #[]
    vector d (fun q=>read d r (d.step q c)) :: rest

theorem suffix_head (d : DFA α) (w : Word α) (q : Fin d.stateCount) :
    read d ((suffixRows d w).headD #[]) q=d.run q w := by
  induction w generalizing q with
  | nil =>
    change read d (vector d id) q=q
    rw [read_vector]
    rfl
  | cons c cs ih =>
    change read d (vector d (fun q=>read d ((suffixRows d cs).headD #[]) (d.step q c))) q=_
    rw [read_vector,ih]
    rfl

theorem suffix_get (d : DFA α) (w : Word α) (a : Nat) (q : Fin d.stateCount)
    (ha : a≤w.length) :
    ((suffixRows d w)[a]?).map (fun r=>read d r q)=some (d.run q (w.drop a)) := by
  induction w generalizing a with
  | nil =>
    have he : a=0 := by simpa using ha
    subst a
    change some (read d (vector d id) q)=some q
    rw [read_vector]
    rfl
  | cons c cs ih =>
    cases a with
    | zero =>
      change some (read d ((suffixRows d (c::cs)).headD #[]) q)=_
      rw [suffix_head]
      rfl
    | succ a => exact ih a (by simpa using ha)

def prefixRows (d : DFA α) (w : Word α) : Array (Row d) :=
  ((List.range d.stateCount).map (fun i=>
    (MaskScan.prefixStates d (PeriodicCache.state d i) w).toArray)).toArray

theorem prefix_get (d : DFA α) (w : Word α) (p : Nat) (q : Fin d.stateCount)
    (hp : p≤w.length) :
    (prefixRows d w)[q.val]?.bind (fun row=>row[p]?)=some (d.run q (w.take p)) := by
  unfold prefixRows
  simp only [List.getElem?_toArray,List.getElem?_map,List.getElem?_range,q.isLt,
    if_true,Option.map,PeriodicCache.state_val,Option.bind,
    MaskScan.prefixStates_get d w p hp q]

structure Index (d : DFA α) where
  cut : Nat
  left : Array (Row d)
  right : Array (Row d)

def build (d : DFA α) (left right : Word α) : Index d :=
  ⟨left.length,(suffixRows d left).toArray,prefixRows d right⟩

def leftAt (d : DFA α) (I : Index d) (a : Nat) : Fin d.stateCount :=
  read d (I.left[a]?.getD #[]) d.initial

def rightAt (d : DFA α) (I : Index d) (p : Nat) (q : Fin d.stateCount) : Bool :=
  d.final (((I.right[q.val]?).bind (fun row=>row[p-I.cut]?)).getD d.initial)

theorem leftAt_correct (d : DFA α) (left right : Word α) (a : Nat) (ha : a≤left.length) :
    leftAt d (build d left right) a=d.run d.initial (left.drop a) := by
  have h := suffix_get d left a d.initial ha
  unfold leftAt build
  rw [List.getElem?_toArray]
  cases he : (suffixRows d left)[a]? with
  | none => simp [he] at h
  | some row =>
    simpa only [he,Option.map,Option.getD,Option.some.injEq] using h

theorem rightAt_correct (d : DFA α) (left right : Word α) (p : Nat) (q : Fin d.stateCount)
    (hc : left.length≤p) (hp : p≤left.length+right.length) :
    rightAt d (build d left right) p q=true ↔
      d.final (d.run q (right.take (p-left.length)))=true := by
  unfold rightAt build
  change d.final (((prefixRows d right)[q.val]?.bind (fun row=>row[p-left.length]?)).getD d.initial)=true ↔ _
  rw [prefix_get d right _ q (by omega)]
  rfl

theorem crossing_accepts (d : DFA α) (left right : Word α) (a p : Nat)
    (ha : a≤left.length) (hc : left.length≤p) (hp : p≤left.length+right.length) :
    rightAt d (build d left right) p (leftAt d (build d left right) a)=true ↔
      d.accepts (slice (left++right) a p) := by
  rw [leftAt_correct d left right a ha,rightAt_correct _ _ _ _ _ hc hp,
    RangeProducts.crossing_slice left right a p ha hc]
  unfold DFA.accepts
  rw [DFA.run_append]

/-- Each backward step materializes a vector of fixed state count.
    This counter counts the number of state entries, not arbitrary
    evaluator overhead. -/
def suffixCells (d : DFA α) : Word α→Nat
  | [] => d.stateCount
  | _::xs => d.stateCount+suffixCells d xs

theorem suffixCells_eq (d : DFA α) (w : Word α) :
    suffixCells d w=(w.length+1)*d.stateCount := by
  induction w with
  | nil => simp [suffixCells]
  | cons c cs ih =>
    change d.stateCount+suffixCells d cs=(cs.length+1+1)*d.stateCount
    rw [ih,Nat.add_mul,Nat.one_mul]
    omega

end REWB.DFACut
