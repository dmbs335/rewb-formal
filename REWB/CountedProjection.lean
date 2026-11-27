import REWB.PhaseMagnitude

/-! Executable projection with structural-operation counters.
    Integer arithmetic/comparisons are counted as primitive operations;
    list traversal, affine traversal and candidate construction are
    performed by the instrumented definitions, not supplied as a cost
    oracle. LCM operations concern shape-dependent coefficients and
    moduli; their internal gcd work is independent of text literals.
    Checked compiler simplifications use tail-recursive accumulators
    while preserving the logical result and counter exactly. Runtime
    accumulator/reversal overhead, allocation, garbage collection and
    bit-level arithmetic are outside this abstract counter. -/
namespace REWB.CountedProjection
open REWB.AffineProjection REWB.UniformProjection

abbrev Result (X : Type) := X×Nat

theorem isEmpty_map (f : X→Y) (xs : List X) : (xs.map f).isEmpty=xs.isEmpty := by
  cases xs <;> rfl

def append (xs ys : List X) : Result (List X) :=
  match xs with
  | [] => (ys,1)
  | x::xs => let r := append xs ys; (x::r.1,r.2+1)

theorem append_value (xs ys : List X) : (append xs ys).1=xs++ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [append,List.cons_append] using congrArg (List.cons x) ih

theorem append_steps (xs ys : List X) : (append xs ys).2=xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [append,List.length_cons] using congrArg (·+1) ih

/-- Runtime implementation using the core library's tail-recursive append.
    The logical counter remains exactly the structurally measured count. -/
def appendTR (xs ys : List X) : Result (List X) := (xs++ys,xs.length+1)

@[csimp] theorem append_eq_appendTR : @append=@appendTR := by
  funext X xs ys
  exact Prod.ext (append_value xs ys) (append_steps xs ys)

def map (f : X→Result Y) : List X→Result (List Y)
  | [] => ([],1)
  | x::xs => let a := f x; let b := map f xs; (a.1::b.1,a.2+b.2+1)

theorem map_value (f : X→Result Y) (xs : List X) :
    (map f xs).1=xs.map (fun x=>(f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change (f x).1::(map f xs).1=_; rw [ih]; rfl

def mapTR.go (f : X→Result Y) : List X→List Y→Nat→Result (List Y)
  | [],acc,c => (acc.reverse,c+1)
  | x::xs,acc,c => let a:=f x; go f xs (a.1::acc) (c+a.2+1)

theorem mapTR.go_eq (f : X→Result Y) (xs : List X) (acc : List Y) (c : Nat) :
    go f xs acc c=(acc.reverse++(map f xs).1,c+(map f xs).2) := by
  induction xs generalizing acc c with
  | nil => simp [go,map]
  | cons x xs ih =>
    rw [go,ih]
    simp only [map,List.reverse_cons,List.append_assoc,List.singleton_append]
    congr 1
    omega

def mapTR (f : X→Result Y) (xs : List X) : Result (List Y) := mapTR.go f xs [] 0

@[csimp] theorem map_eq_mapTR : @map=@mapTR := by
  funext X Y f xs
  simp only [mapTR,mapTR.go_eq,List.reverse_nil,List.nil_append,Nat.zero_add]

theorem map_steps_congr (f : X→Result Y) (g : Z→Result W) (s : X→Z) (xs : List X)
    (h : ∀ x,x∈xs→(f x).2=(g (s x)).2) :
    (map f xs).2=(map g (xs.map s)).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (f x).2+(map f xs).2+1=(g (s x)).2+(map g (xs.map s)).2+1
    rw [h x (by simp),ih (fun z hz=>h z (by simp [hz]))]

theorem map_steps_constant (f : X→Result Y) (xs : List X) (c : Nat)
    (h : ∀ x,x∈xs→(f x).2=c) : (map f xs).2=xs.length*(c+1)+1 := by
  induction xs with
  | nil => simp [map]
  | cons x xs ih =>
    change (f x).2+(map f xs).2+1=(xs.length+1)*(c+1)+1
    rw [h x (by simp),ih (fun z hz=>h z (by simp [hz])),Nat.add_mul,Nat.one_mul]
    omega

theorem map_plain_steps (f : X→Y) (xs : List X) (c : Nat) :
    (map (fun x=>(f x,c)) xs).2=xs.length*(c+1)+1 :=
  map_steps_constant _ _ c (fun _ _=>rfl)

/-- The accumulator reversal has one output cell per input cell, so its
    extra runtime pass is itself bounded by the recorded list work. -/
theorem map_length_le_steps (f : X→Result Y) (xs : List X) :
    xs.length+1≤(map f xs).2 := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    change xs.length+1+1≤(f x).2+(map f xs).2+1
    omega

def flatMap (f : X→Result (List Y)) : List X→Result (List Y)
  | [] => ([],1)
  | x::xs =>
    let a := f x
    let b := flatMap f xs
    let c := append a.1 b.1
    (c.1,a.2+b.2+c.2+1)

theorem flatMap_value (f : X→Result (List Y)) (xs : List X) :
    (flatMap f xs).1=xs.flatMap (fun x=>(f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (append (f x).1 (flatMap f xs).1).1=_
    rw [append_value,ih]
    rfl

def flatMapTR.go (f : X→Result (List Y)) : List X→List Y→Nat→Result (List Y)
  | [],acc,c => (acc.reverse,c+1)
  | x::xs,acc,c =>
    let a:=f x
    go f xs (a.1.reverseAux acc) (c+a.2+a.1.length+2)

theorem flatMapTR.go_eq (f : X→Result (List Y)) (xs : List X) (acc : List Y) (c : Nat) :
    go f xs acc c=(acc.reverse++(flatMap f xs).1,c+(flatMap f xs).2) := by
  induction xs generalizing acc c with
  | nil => simp [go,flatMap]
  | cons x xs ih =>
    rw [go,ih]
    simp only [List.reverseAux_eq,List.reverse_append,List.reverse_reverse,flatMap,
      append_value,append_steps,List.append_assoc]
    congr 1
    omega

def flatMapTR (f : X→Result (List Y)) (xs : List X) : Result (List Y) := flatMapTR.go f xs [] 0

@[csimp] theorem flatMap_eq_flatMapTR : @flatMap=@flatMapTR := by
  funext X Y f xs
  simp only [flatMapTR,flatMapTR.go_eq,List.reverse_nil,List.nil_append,Nat.zero_add]

theorem flatMap_steps_congr (f : X→Result (List Y)) (g : Z→Result (List W))
    (s : X→Z) (xs : List X)
    (hc : ∀ x,x∈xs→(f x).2=(g (s x)).2)
    (hl : ∀ x,x∈xs→(f x).1.length=(g (s x)).1.length) :
    (flatMap f xs).2=(flatMap g (xs.map s)).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (f x).2+(flatMap f xs).2+(append (f x).1 _).2+1=
      (g (s x)).2+(flatMap g (xs.map s)).2+(append (g (s x)).1 _).2+1
    rw [append_steps,append_steps,hc x (by simp),hl x (by simp),
      ih (fun z hz=>hc z (by simp [hz])) (fun z hz=>hl z (by simp [hz]))]

theorem flatMap_steps_constant (f : X→Result (List Y)) (xs : List X) (c l : Nat)
    (hc : ∀ x,x∈xs→(f x).2=c) (hl : ∀ x,x∈xs→(f x).1.length=l) :
    (flatMap f xs).2=xs.length*(c+l+2)+1 := by
  induction xs with
  | nil => simp [flatMap]
  | cons x xs ih =>
    change (f x).2+(flatMap f xs).2+(append (f x).1 _).2+1=_
    rw [append_steps,hc x (by simp),hl x (by simp),
      ih (fun z hz=>hc z (by simp [hz])) (fun z hz=>hl z (by simp [hz]))]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Each accumulator pass of the tail implementation is linear in its
    output, whose length is bounded by the original measured work. -/
theorem flatMap_length_le_steps (f : X→Result (List Y)) (xs : List X) :
    (flatMap f xs).1.length+xs.length+1≤(flatMap f xs).2 := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [flatMap,append_value,append_steps,List.length_append,List.length_cons]
    omega

def rangeFrom (start : Nat) : Nat→Result (List Nat)
  | 0 => ([],1)
  | n+1 => let r := rangeFrom (start+1) n; (start::r.1,r.2+2)

theorem rangeFrom_value (start n : Nat) : (rangeFrom start n).1=List.range' start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => change start::(rangeFrom (start+1) n).1=_; rw [ih,List.range'_succ]

theorem rangeFrom_steps (start n : Nat) : (rangeFrom start n).2=2*n+1 := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [rangeFrom,ih,Nat.mul_add,Nat.mul_one]

def rangeFromTR (start n : Nat) : Result (List Nat) := (List.range' start n,2*n+1)

@[csimp] theorem rangeFrom_eq_rangeFromTR : rangeFrom=rangeFromTR := by
  funext start n
  exact Prod.ext (rangeFrom_value start n) (rangeFrom_steps start n)

def range (n : Nat) : Result (List Nat) := rangeFrom 0 n

theorem range_value (n : Nat) : (range n).1=List.range n := by
  rw [range,rangeFrom_value]
  exact List.range_eq_range'.symm

def split : Aff→Result (Int×Aff)
  | .lit z => ((0,.lit z),1)
  | .var 0 => ((1,.lit 0),1)
  | .var (i+1) => ((0,.var i),2)
  | .add a b =>
    let x := split a
    let y := split b
    ((x.1.1+y.1.1,.add x.1.2 y.1.2),x.2+y.2+2)
  | .scale c a =>
    let x := split a
    ((c*x.1.1,.scale c x.1.2),x.2+2)

theorem split_value (a : Aff) : (split a).1=a.split := by
  induction a with
  | lit z => rfl
  | var i => cases i <;> rfl
  | add a b ha hb => simp only [split,Aff.split,ha,hb]
  | scale c a ha => simp only [split,Aff.split,ha]

theorem split_steps (a : Aff) : (split a).2=(split (LiteralShape.aff a)).2 := by
  induction a with
  | lit z => rfl
  | var i => rfl
  | add a b ha hb => simp only [split,LiteralShape.aff,ha,hb]
  | scale c a ha => simp only [split,LiteralShape.aff,ha]

def factor : Atom→Result Nat
  | .le a => let r := split a; (max 1 r.1.1.natAbs,r.2+2)
  | .dvd _ _ => (1,1)

theorem factor_value (a : Atom) : (factor a).1=a.factor := by
  cases a <;> simp only [factor,Atom.factor,split_value]

theorem factor_steps (a : Atom) : (factor a).2=(factor (LiteralShape.atom a)).2 := by
  cases a with
  | le a => exact congrArg (·+2) (split_steps a)
  | dvd m a => rfl

def multiplier : Conj→Result Nat
  | [] => (1,1)
  | a::as => let x := factor a; let y := multiplier as; (Nat.lcm x.1 y.1,x.2+y.2+1)

theorem multiplier_value (C : Conj) : (multiplier C).1=AffineProjection.multiplier C := by
  induction C with
  | nil => rfl
  | cons a as ih => simp only [multiplier,AffineProjection.multiplier,factor_value,ih]

theorem multiplier_steps (C : Conj) : (multiplier C).2=(multiplier (LiteralShape.conj C)).2 := by
  induction C with
  | nil => rfl
  | cons a as ih =>
    change (factor a).2+(multiplier as).2+1=
      (factor (LiteralShape.atom a)).2+(multiplier (LiteralShape.conj as)).2+1
    rw [factor_steps,ih]

def normalizeAtom (D : Nat) : Atom→Result Norm
  | .le a =>
    let x := split a
    if x.1.1=0 then (⟨[],[],[.le x.1.2],[]⟩,x.2+2)
    else
      let s : Int := Int.ofNat (D/x.1.1.natAbs)
      if 0<x.1.1 then (⟨[],[.scale (-s) x.1.2],[],[]⟩,x.2+5)
      else (⟨[.scale s x.1.2],[],[],[]⟩,x.2+4)
  | .dvd m a =>
    let x := split a
    (⟨[],[],[],[⟨D*m,x.1.1,.scale (Int.ofNat D) x.1.2⟩]⟩,x.2+3)

theorem normalizeAtom_value (D : Nat) (a : Atom) :
    (normalizeAtom D a).1=AffineProjection.normalizeAtom D a := by
  cases a with
  | le a => simp only [normalizeAtom,AffineProjection.normalizeAtom,split_value]; split <;> (try split) <;> rfl
  | dvd m a => simp only [normalizeAtom,AffineProjection.normalizeAtom,split_value]

theorem normalizeAtom_steps (D : Nat) (a : Atom) :
    (normalizeAtom D a).2=(normalizeAtom D (LiteralShape.atom a)).2 := by
  cases a with
  | le a =>
    simp only [normalizeAtom,LiteralShape.atom,split_value,LiteralShape.split_aff]
    rw [split_steps a]
    split <;> (try split) <;> rfl
  | dvd m a => exact congrArg (·+3) (split_steps a)

def merge (N M : Norm) : Result Norm :=
  let l := append N.lower M.lower
  let u := append N.upper M.upper
  let f := append N.free M.free
  let g := append N.guards M.guards
  (⟨l.1,u.1,f.1,g.1⟩,l.2+u.2+f.2+g.2+1)

theorem merge_value (N M : Norm) : (merge N M).1=N.merge M := by
  simp only [merge,Norm.merge,append_value]

theorem merge_steps (N M : Norm) :
    (merge N M).2=N.lower.length+N.upper.length+N.free.length+N.guards.length+5 := by
  simp only [merge,append_steps]
  omega

theorem merge_steps_shape (N M : Norm) :
    (merge N M).2=(merge (LiteralShape.norm N) (LiteralShape.norm M)).2 := by
  simp only [merge_steps,LiteralShape.norm,LiteralShape.conj,List.length_map]

def normalizeRows (D : Nat) : Conj→Result Norm
  | [] => (Norm.empty,1)
  | a::as =>
    let x := normalizeAtom D a
    let y := normalizeRows D as
    let z := merge x.1 y.1
    (z.1,x.2+y.2+z.2+1)

theorem normalizeRows_value (D : Nat) (C : Conj) :
    (normalizeRows D C).1=AffineProjection.normalizeRows D C := by
  induction C with
  | nil => rfl
  | cons a as ih => simp only [normalizeRows,AffineProjection.normalizeRows,merge_value,normalizeAtom_value,ih]

theorem normalizeRows_steps (D : Nat) (C : Conj) :
    (normalizeRows D C).2=(normalizeRows D (LiteralShape.conj C)).2 := by
  induction C with
  | nil => rfl
  | cons a as ih =>
    change (normalizeAtom D a).2+(normalizeRows D as).2+
      (merge (normalizeAtom D a).1 (normalizeRows D as).1).2+1=
      (normalizeAtom D (LiteralShape.atom a)).2+(normalizeRows D (LiteralShape.conj as)).2+
      (merge (normalizeAtom D (LiteralShape.atom a)).1 (normalizeRows D (LiteralShape.conj as)).1).2+1
    rw [normalizeAtom_steps,ih,normalizeAtom_value,normalizeAtom_value,normalizeRows_value,normalizeRows_value,
      ← LiteralShape.norm_atom,← LiteralShape.norm_rows,merge_steps_shape]

def normalize (C : Conj) : Result Norm :=
  let m := multiplier C
  let r := normalizeRows m.1 C
  let z := merge r.1 (integrality m.1)
  (z.1,m.2+r.2+z.2+2)

theorem normalize_value (C : Conj) : (normalize C).1=AffineProjection.normalize C := by
  simp only [normalize,AffineProjection.normalize,merge_value,normalizeRows_value,multiplier_value]

theorem normalize_steps (C : Conj) : (normalize C).2=(normalize (LiteralShape.conj C)).2 := by
  unfold normalize
  simp only [multiplier_value,LiteralShape.multiplier_conj,normalizeRows_value]
  rw [multiplier_steps,normalizeRows_steps,← LiteralShape.norm_rows]
  rw [merge_steps,merge_steps]
  simp only [LiteralShape.norm,LiteralShape.conj,List.length_map]

def commonPeriod : List Guard→Result Nat
  | [] => (1,1)
  | g::gs => let r := commonPeriod gs; (Nat.lcm g.modulus r.1,r.2+1)

theorem commonPeriod_value (gs : List Guard) : (commonPeriod gs).1=AffineProjection.commonPeriod gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [commonPeriod,AffineProjection.commonPeriod,ih]

theorem commonPeriod_steps (gs : List Guard) : (commonPeriod gs).2=gs.length+1 := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simpa only [commonPeriod,List.length_cons] using congrArg (·+1) ih

def candidates (N : Norm) (K : Nat) : Result (List Aff) :=
  let rs := range K
  if N.lower.isEmpty then
    let r := map (fun i : Nat=>(Aff.lit (i:Int),1)) rs.1
    (r.1,rs.2+r.2+1)
  else
    let r := flatMap (fun l=>map (fun i : Nat=>(Aff.add l (.lit (i:Int)),2)) rs.1) N.lower
    (r.1,rs.2+r.2+1)

theorem candidates_value (N : Norm) (K : Nat) : (candidates N K).1=N.candidates K := by
  simp only [candidates,Norm.candidates,range_value]
  split
  · rw [map_value]
  · rw [flatMap_value]
    simp only [map_value]

theorem candidates_steps (N : Norm) (K : Nat) :
    (candidates N K).2=(range K).2+
      (if N.lower.isEmpty then K*2+1 else N.lower.length*(K*3+1+K+2)+1)+1 := by
  unfold candidates
  split <;> dsimp only
  · rw [map_plain_steps,range_value,List.length_range]
  · rw [flatMap_steps_constant _ _ (K*3+1) K]
    · intro l _
      rw [map_plain_steps,range_value,List.length_range]
    · intro l _
      rw [map_value,List.length_map,range_value,List.length_range]

theorem candidates_steps_shape (N : Norm) (K : Nat) :
    (candidates N K).2=(candidates (LiteralShape.norm N) K).2 := by
  rw [candidates_steps,candidates_steps]
  simp only [LiteralShape.norm,isEmpty_map,List.length_map]

def substitute (N : Norm) (c : Aff) : Result Conj :=
  let b : Result Conj :=
    if N.lower.isEmpty then ([],1)
    else
      let l := map (fun a=>(Atom.le (a.sub c),3)) N.lower
      let u := map (fun a=>(Atom.le (c.sub a),3)) N.upper
      let r := append l.1 u.1
      (r.1,l.2+u.2+r.2+1)
  let g := map (fun a=>(a.substitute c,3)) N.guards
  let a := append N.free b.1
  let z := append a.1 g.1
  (z.1,b.2+g.2+a.2+z.2+1)

theorem substitute_value (N : Norm) (c : Aff) : (substitute N c).1=N.substitute c := by
  unfold substitute Norm.substitute
  split <;> simp only [append_value,map_value]

theorem substitute_steps (N : Norm) (c : Aff) :
    (substitute N c).2=
      (if N.lower.isEmpty then 1 else N.lower.length*5+N.upper.length*4+4)+
      N.guards.length*4+2*N.free.length+
      (if N.lower.isEmpty then 0 else N.lower.length+N.upper.length)+4 := by
  unfold substitute
  split <;> simp only [map_plain_steps,append_steps,append_value,map_value,List.length_map,
    List.length_append,List.length_nil] <;> omega

theorem substitute_steps_shape (N : Norm) (c d : Aff) :
    (substitute N c).2=(substitute (LiteralShape.norm N) d).2 := by
  rw [substitute_steps,substitute_steps]
  simp only [LiteralShape.norm,LiteralShape.conj,isEmpty_map,List.length_map]

def eliminateConj (C : Conj) : Result Formula :=
  let n := normalize C
  let k := commonPeriod n.1.guards
  let cs := candidates n.1 k.1
  let r := map (substitute n.1) cs.1
  (r.1,n.2+k.2+cs.2+r.2+1)

theorem eliminateConj_value (C : Conj) :
    (eliminateConj C).1=AffineProjection.eliminateConj C := by
  simp only [eliminateConj,AffineProjection.eliminateConj,Norm.eliminate,
    normalize_value,commonPeriod_value,candidates_value,map_value,substitute_value]

theorem substitute_length (N : Norm) (c : Aff) :
    (substitute N c).1.length=N.free.length+
      (if N.lower.isEmpty then 0 else N.lower.length+N.upper.length)+N.guards.length := by
  rw [substitute_value]
  simp only [Norm.substitute,List.length_append,List.length_map]
  split <;> simp only [List.length_nil,List.length_append,List.length_map]

theorem eliminateConj_steps (C : Conj) :
    (eliminateConj C).2=(eliminateConj (LiteralShape.conj C)).2 := by
  unfold eliminateConj
  simp only [normalize_value,commonPeriod_value]
  rw [normalize_steps,commonPeriod_steps,commonPeriod_steps,← LiteralShape.norm_normalize]
  have hK : AffineProjection.commonPeriod ((LiteralShape.norm (AffineProjection.normalize C)).guards)=
      AffineProjection.commonPeriod (AffineProjection.normalize C).guards :=
    LiteralShape.commonPeriod_map _
  rw [hK]
  have hmap : (map (substitute (AffineProjection.normalize C))
      (candidates (AffineProjection.normalize C) (AffineProjection.commonPeriod (AffineProjection.normalize C).guards)).1).2 =
      (map (substitute (LiteralShape.norm (AffineProjection.normalize C)))
        (candidates (LiteralShape.norm (AffineProjection.normalize C))
          (AffineProjection.commonPeriod (AffineProjection.normalize C).guards)).1).2 := by
    rw [map_steps_constant _ _ (substitute (AffineProjection.normalize C) (.lit 0)).2]
    · rw [map_steps_constant _ _ (substitute (LiteralShape.norm (AffineProjection.normalize C)) (.lit 0)).2]
      · rw [substitute_steps_shape _ (.lit 0) (.lit 0),candidates_value,candidates_value]
        have he := congrArg List.length (LiteralShape.candidate_shape (AffineProjection.normalize C)
          (AffineProjection.commonPeriod (AffineProjection.normalize C).guards))
        simpa only [List.length_map] using congrArg (fun n=>n*
          ((substitute (LiteralShape.norm (AffineProjection.normalize C)) (.lit 0)).2+1)+1) he
      · intro a _
        rw [substitute_steps,substitute_steps]
    · intro a _
      rw [substitute_steps,substitute_steps]
  rw [hmap,candidates_steps_shape]
  simp only [LiteralShape.norm,List.length_map]

def eliminateFormula (F : Formula) : Result Formula := flatMap eliminateConj F

theorem eliminateFormula_value (F : Formula) :
    (eliminateFormula F).1=AffineProjection.eliminateFormula F := by
  simp only [eliminateFormula,AffineProjection.eliminateFormula,flatMap_value,eliminateConj_value]

theorem eliminateFormula_steps (F : Formula) :
    (eliminateFormula F).2=(eliminateFormula (LiteralShape.formula F)).2 := by
  apply flatMap_steps_congr eliminateConj eliminateConj LiteralShape.conj F
  · intro C _
    exact eliminateConj_steps C
  · intro C _
    rw [eliminateConj_value,eliminateConj_value]
    have h := congrArg List.length (LiteralShape.eliminateConj_shape C)
    simpa only [LiteralShape.formula,List.length_map] using h

def project : Nat→Formula→Result Formula
  | 0,F => (F,1)
  | k+1,F =>
    let p := project k F
    let r := eliminateFormula p.1
    (r.1,p.2+r.2+1)

theorem project_value (k : Nat) (F : Formula) : (project k F).1=AffineProjection.project k F := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [project,AffineProjection.project,eliminateFormula_value,ih]

theorem project_steps_shape (k : Nat) (F G : Formula)
    (h : LiteralShape.formula F=LiteralShape.formula G) : (project k F).2=(project k G).2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (project k F).2+(eliminateFormula (project k F).1).2+1=
      (project k G).2+(eliminateFormula (project k G).1).2+1
    rw [ih,project_value,project_value,eliminateFormula_steps (AffineProjection.project k F),
      eliminateFormula_steps (AffineProjection.project k G),LiteralShape.project_shape k F G h]

def read : List Int→Nat→Result Int
  | [],_ => (0,1)
  | z::_,0 => (z,1)
  | _::zs,i+1 => let r := read zs i; (r.1,r.2+1)

theorem read_value (env : List Int) (i : Nat) : (read env i).1=env[i]?.getD 0 := by
  induction env generalizing i with
  | nil => rfl
  | cons z zs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem read_steps (env other : List Int) (i : Nat) (h : env.length=other.length) :
    (read env i).2=(read other i).2 := by
  induction env generalizing other i with
  | nil =>
    cases other with
    | nil => rfl
    | cons z zs => simp at h
  | cons z zs ih =>
    cases other with
    | nil => simp at h
    | cons w ws =>
      cases i with
      | zero => rfl
      | succ i =>
        change (read zs i).2+1=(read ws i).2+1
        rw [ih ws i (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using h)]

def eval (env : List Int) : Aff→Result Int
  | .lit z => (z,1)
  | .var i => let r := read env i; (r.1,r.2+1)
  | .add a b => let x := eval env a; let y := eval env b; (x.1+y.1,x.2+y.2+1)
  | .scale c a => let x := eval env a; (c*x.1,x.2+1)

theorem eval_value (env : List Int) (a : Aff) : (eval env a).1=a.eval env := by
  induction a with
  | lit z => rfl
  | var i => exact read_value env i
  | add a b ha hb => simp only [eval,Aff.eval,ha,hb]
  | scale c a ha => simp only [eval,Aff.eval,ha]

theorem eval_steps (env other : List Int) (a : Aff) (h : env.length=other.length) :
    (eval env a).2=(eval other (LiteralShape.aff a)).2 := by
  induction a with
  | lit z => rfl
  | var i => exact congrArg (·+1) (read_steps env other i h)
  | add a b ha hb => simp only [eval,LiteralShape.aff,ha,hb]
  | scale c a ha => simp only [eval,LiteralShape.aff,ha]

def atomTest (env : List Int) : Atom→Result Bool
  | .le a => let r := eval env a; (decide (r.1≤0),r.2+1)
  | .dvd m a => let r := eval env a; (decide (r.1%(m:Int)=0),r.2+2)

theorem atomTest_value (env : List Int) (a : Atom) : (atomTest env a).1=a.test env := by
  cases a <;> simp only [atomTest,Atom.test,eval_value]

theorem atomTest_steps (env other : List Int) (a : Atom) (h : env.length=other.length) :
    (atomTest env a).2=(atomTest other (LiteralShape.atom a)).2 := by
  cases a with
  | le a => exact congrArg (·+1) (eval_steps env other a h)
  | dvd m a => exact congrArg (·+2) (eval_steps env other a h)

/-- Eager traversal keeps the counter independent of truth values.
    The resulting Boolean is exactly the original conjunction test. -/
def testConj (env : List Int) : Conj→Result Bool
  | [] => (true,1)
  | a::as =>
    let x := atomTest env a
    let y := testConj env as
    (x.1 && y.1,x.2+y.2+1)

theorem testConj_value (env : List Int) (C : Conj) :
    (testConj env C).1=C.all (Atom.test env) := by
  induction C with
  | nil => rfl
  | cons a as ih => simp only [testConj,List.all_cons,atomTest_value,ih]

theorem testConj_steps (env other : List Int) (C : Conj) (h : env.length=other.length) :
    (testConj env C).2=(testConj other (LiteralShape.conj C)).2 := by
  induction C with
  | nil => rfl
  | cons a as ih =>
    change (atomTest env a).2+(testConj env as).2+1=
      (atomTest other (LiteralShape.atom a)).2+(testConj other (LiteralShape.conj as)).2+1
    rw [atomTest_steps env other a h,ih]

def testConjTR.go (env : List Int) : Conj→Bool→Nat→Result Bool
  | [],acc,c => (acc,c+1)
  | a::as,acc,c => let r:=atomTest env a; go env as (acc && r.1) (c+r.2+1)

theorem testConjTR.go_eq (env : List Int) (C : Conj) (acc : Bool) (c : Nat) :
    go env C acc c=(acc && (testConj env C).1,c+(testConj env C).2) := by
  induction C generalizing acc c with
  | nil => simp [go,testConj]
  | cons a as ih =>
    rw [go,ih]
    simp only [testConj,Bool.and_assoc]
    congr 1
    omega

def testConjTR (env : List Int) (C : Conj) : Result Bool := testConjTR.go env C true 0

@[csimp] theorem testConj_eq_testConjTR : testConj=testConjTR := by
  funext env C
  simp only [testConjTR,testConjTR.go_eq,Bool.true_and,Nat.zero_add]

def decide (env : List Int) : Formula→Result Bool
  | [] => (false,1)
  | C::Cs =>
    let x := testConj env C
    let y := decide env Cs
    (x.1 || y.1,x.2+y.2+1)

theorem decide_value (env : List Int) (F : Formula) :
    (decide env F).1=AffineProjection.decideFormula F env := by
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change ((testConj env C).1 || (decide env Cs).1)=_
    rw [testConj_value,ih]
    rfl

theorem decide_steps (env other : List Int) (F : Formula) (h : env.length=other.length) :
    (decide env F).2=(decide other (LiteralShape.formula F)).2 := by
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change (testConj env C).2+(decide env Cs).2+1=
      (testConj other (LiteralShape.conj C)).2+(decide other (LiteralShape.formula Cs)).2+1
    rw [testConj_steps env other C h,ih]

def decideTR.go (env : List Int) : Formula→Bool→Nat→Result Bool
  | [],acc,c => (acc,c+1)
  | C::Cs,acc,c => let r:=testConj env C; go env Cs (acc || r.1) (c+r.2+1)

theorem decideTR.go_eq (env : List Int) (F : Formula) (acc : Bool) (c : Nat) :
    go env F acc c=(acc || (decide env F).1,c+(decide env F).2) := by
  induction F generalizing acc c with
  | nil => simp [go,decide]
  | cons C Cs ih =>
    rw [go,ih]
    simp only [decide,Bool.or_assoc]
    congr 1
    omega

def decideTR (env : List Int) (F : Formula) : Result Bool := decideTR.go env F false 0

@[csimp] theorem decide_eq_decideTR : decide=decideTR := by
  funext env F
  simp only [decideTR,decideTR.go_eq,Bool.false_or,Nat.zero_add]

def solve (k : Nat) (F : Formula) (env : List Int) : Result Bool :=
  let p := project k F
  let r := decide env p.1
  (r.1,p.2+r.2+1)

theorem solve_value (k : Nat) (F : Formula) (env : List Int) :
    (solve k F env).1=AffineProjection.solve k F env := by
  simp only [solve,AffineProjection.solve,decide_value,project_value]

theorem solve_steps_shape (k : Nat) (F G : Formula) (env other : List Int)
    (hF : LiteralShape.formula F=LiteralShape.formula G) (hE : env.length=other.length) :
    (solve k F env).2=(solve k G other).2 := by
  unfold solve
  simp only [project_value]
  rw [project_steps_shape k F G hF,decide_steps env other (AffineProjection.project k F) hE,
    decide_steps other other (AffineProjection.project k G) rfl,LiteralShape.project_shape k F G hF]

def stepsBudget (k envLength : Nat) : Family→Nat
  | [] => 0
  | F::fs => max (solve k F (List.replicate envLength 0)).2 (stepsBudget k envLength fs)

theorem member_stepsBudget (k envLength : Nat) (fs : Family) (F : Formula) (h : F∈fs) :
    (solve k F (List.replicate envLength 0)).2≤stepsBudget k envLength fs := by
  induction fs with
  | nil => simp at h
  | cons G gs ih =>
    rcases List.mem_cons.mp h with he|hm
    · subst F
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hm) (Nat.le_max_right _ _)

/-- This is a bound on the counter of the executable instrumented
    algorithm. It is not a freely supplied cost function. -/
theorem solve_uniform_steps (k : Nat) (F : Formula) (fs : Family) (env : List Int)
    (h : Covered F fs) : (solve k F env).2≤stepsBudget k env.length fs := by
  have he := solve_steps_shape k F (LiteralShape.formula F) env (List.replicate env.length 0)
    (by
      simp only [LiteralShape.formula,LiteralShape.conj,List.map_map,Function.comp_def,LiteralShape.atom_idem]
      rfl)
    (by simp only [List.length_replicate])
  rw [he]
  exact member_stepsBudget k env.length fs _ h

/-- Depth-first elimination can return as soon as one projected branch
    succeeds. It never constructs later branches merely to reject them. -/
def search (env : List Int) : Nat→Formula→Result Bool
  | 0,F => decide env F
  | _+1,[] => (false,1)
  | k+1,C::Cs =>
    let e:=eliminateConj C
    let a:=search env k e.1
    if a.1 then (true,e.2+a.2+1)
    else
      let b:=search env (k+1) Cs
      (b.1,e.2+a.2+b.2+1)
termination_by k F => (k,F.length)

theorem original_project_nil (k : Nat) : AffineProjection.project k []=[] := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [AffineProjection.project,ih,AffineProjection.eliminateFormula,List.flatMap_nil]

theorem original_project_append (k : Nat) (F G : Formula) :
    AffineProjection.project k (F++G)=AffineProjection.project k F++AffineProjection.project k G := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [AffineProjection.project,ih,AffineProjection.eliminateFormula,List.flatMap_append]

theorem original_project_first (k : Nat) (F : Formula) :
    AffineProjection.project (k+1) F=AffineProjection.project k (AffineProjection.eliminateFormula F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change AffineProjection.eliminateFormula (AffineProjection.project (k+1) F)=_
    rw [ih]
    rfl

theorem original_project_cons (k : Nat) (C : Conj) (Cs : Formula) :
    AffineProjection.project (k+1) (C::Cs)=
      AffineProjection.project k (AffineProjection.eliminateConj C)++AffineProjection.project (k+1) Cs := by
  rw [original_project_first]
  change AffineProjection.project k (AffineProjection.eliminateConj C++AffineProjection.eliminateFormula Cs)=_
  rw [original_project_append,← original_project_first]

theorem original_decide_append (F G : Formula) (env : List Int) :
    AffineProjection.decideFormula (F++G) env=
      (AffineProjection.decideFormula F env || AffineProjection.decideFormula G env) := by
  simp only [AffineProjection.decideFormula,List.any_append]

theorem search_value (env : List Int) (k : Nat) (F : Formula) :
    (search env k F).1=AffineProjection.solve k F env := by
  change (search env k F).1=AffineProjection.decideFormula (AffineProjection.project k F) env
  induction k generalizing F with
  | zero => simp only [search,decide_value,AffineProjection.project]
  | succ k ih =>
    induction F with
    | nil => simp only [search,original_project_nil,AffineProjection.decideFormula,List.any_nil]
    | cons C Cs ih' =>
      have hc:=ih (eliminateConj C).1
      rw [eliminateConj_value] at hc
      rw [original_project_cons,original_decide_append,← hc,← ih']
      rw [search]
      split <;> simp_all [eliminateConj_value]

/-- The same traversal without pruning gives a computable bound whose
    count is determined by erased syntax and environment length alone. -/
def searchWork (envLength : Nat) : Nat→Formula→Nat
  | 0,F => (decide (List.replicate envLength 0) F).2
  | _+1,[] => 1
  | k+1,C::Cs =>
    let e:=eliminateConj C
    e.2+searchWork envLength k e.1+searchWork envLength (k+1) Cs+1
termination_by k F => (k,F.length)

theorem search_steps (env : List Int) (k : Nat) (F : Formula) :
    (search env k F).2≤searchWork env.length k F := by
  induction k generalizing F with
  | zero =>
    have h:=decide_steps env (List.replicate env.length 0) F (by simp)
    have h':=decide_steps (List.replicate env.length 0) (List.replicate env.length 0) F rfl
    simp only [search,searchWork]
    rw [h,h']
    exact Nat.le_refl _
  | succ k ih =>
    induction F with
    | nil => simp only [search,searchWork,Nat.le_refl]
    | cons C Cs ih' =>
      have hc:=ih (eliminateConj C).1
      rw [search,searchWork]
      split <;> dsimp only <;> omega

theorem searchWork_erase (envLength k : Nat) (F : Formula) :
    searchWork envLength k F=searchWork envLength k (LiteralShape.formula F) := by
  induction k generalizing F with
  | zero =>
    simpa only [searchWork] using (decide_steps
      (List.replicate envLength 0) (List.replicate envLength 0) F rfl)
  | succ k ih =>
    induction F with
    | nil => rfl
    | cons C Cs ih' =>
      change searchWork envLength (k+1) (C::Cs)=
        searchWork envLength (k+1) (LiteralShape.conj C::LiteralShape.formula Cs)
      rw [searchWork,searchWork]
      change (eliminateConj C).2+searchWork envLength k (eliminateConj C).1+
        searchWork envLength (k+1) Cs+1=
        (eliminateConj (LiteralShape.conj C)).2+
        searchWork envLength k (eliminateConj (LiteralShape.conj C)).1+
        searchWork envLength (k+1) (LiteralShape.formula Cs)+1
      rw [eliminateConj_steps C,ih',eliminateConj_value,eliminateConj_value,
        ih (AffineProjection.eliminateConj C),ih (AffineProjection.eliminateConj (LiteralShape.conj C)),
        LiteralShape.eliminateConj_shape]

def searchBudget (k envLength : Nat) : Family→Nat
  | [] => 0
  | F::fs => max (searchWork envLength k F) (searchBudget k envLength fs)

theorem member_searchBudget (k envLength : Nat) (fs : Family) (F : Formula) (h : F∈fs) :
    searchWork envLength k F≤searchBudget k envLength fs := by
  induction fs with
  | nil => simp at h
  | cons G gs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem search_uniform_steps (env : List Int) (k : Nat) (F : Formula) (fs : Family)
    (h : Covered F fs) : (search env k F).2≤searchBudget k env.length fs := by
  have hh:=search_steps env k F
  rw [searchWork_erase] at hh
  exact Nat.le_trans hh (member_searchBudget k env.length fs _ h)

def p2 (P : SevenDFA α) [DecidableEq α] (s : Nat→α) (n q : Nat)
    (pre post : Word α) (ph : P2Periodic.Layout Nat) : Result Bool :=
  solve 8 (PhaseSolver.compileSystem q n s
    (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph))) []

theorem p2_value (P : SevenDFA α) [DecidableEq α] (s : Nat→α) (n q : Nat)
    (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    (p2 P s n q pre post ph).1=P2Periodic.solveAt P s n q pre post ph :=
  solve_value _ _ _

def p2Steps (P : SevenDFA α) : Nat :=
  max (stepsBudget 8 0 (UniformPhaseBounds.p2Family P))
    (searchBudget 8 0 (UniformPhaseBounds.p2Family P))

/-- All recursive projection operations and the final eager decision
    have one pattern-only structural-operation bound per phase. -/
theorem p2_steps (P : SevenDFA α) [DecidableEq α] (s : Nat→α) (n q : Nat)
    (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    (p2 P s n q pre post ph).2≤p2Steps P :=
  Nat.le_trans (solve_uniform_steps _ _ _ [] (UniformPhaseBounds.p2_covered P s q n pre post ph))
    (Nat.le_max_left _ _)

theorem p2_search_steps (P : SevenDFA α) (F : Formula)
    (h : Covered F (UniformPhaseBounds.p2Family P)) : (search [] 8 F).2≤p2Steps P :=
  Nat.le_trans (search_uniform_steps [] 8 F _ h) (Nat.le_max_right _ _)

end REWB.CountedProjection
