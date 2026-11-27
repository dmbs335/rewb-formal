import REWB.UniformJoin

/-! Compute a shared positive modulus from the formulas actually emitted.
    The finite-family modulus is a proof bound only and is never evaluated
    by this constructor. Work counts list visits and primitive LCM steps. -/
namespace REWB.ActualModulus
open REWB.AffineProjection

def atom (a : Atom) : Nat := match a with
  | .le _ => 1
  | .dvd m _ => max 1 m

def row : Conj→Nat×Nat
  | [] => (1,1)
  | a::as => let r:=row as; (Nat.lcm (atom a) r.1,r.2+2)

def formula : Formula→Nat×Nat
  | [] => (1,1)
  | C::Cs => let a:=row C; let b:=formula Cs; (Nat.lcm a.1 b.1,a.2+b.2+1)

def entries : List TimedJoin.TimedEntry→Nat×Nat
  | [] => (1,1)
  | e::es => let a:=formula e.entry.formula; let b:=entries es; (Nat.lcm a.1 b.1,a.2+b.2+1)

def build (es fs : List TimedJoin.TimedEntry) : Nat×Nat :=
  let a:=entries es; let b:=entries fs; (Nat.lcm a.1 b.1,a.2+b.2+1)

theorem atom_pos (a : Atom) : 0<atom a := by
  cases a with
  | le t => exact Nat.zero_lt_one
  | dvd m t => exact Nat.lt_of_lt_of_le (by decide : 0<1) (Nat.le_max_left _ _)

theorem lcm_pos (a b : Nat) (ha : 0<a) (hb : 0<b) : 0<Nat.lcm a b :=
  Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt hb))

theorem row_pos (C : Conj) : 0<(row C).1 := by
  induction C with
  | nil => decide
  | cons a as ih => exact lcm_pos _ _ (atom_pos a) ih

theorem formula_pos (F : Formula) : 0<(formula F).1 := by
  induction F with
  | nil => decide
  | cons C Cs ih => exact lcm_pos _ _ (row_pos C) ih

theorem entries_pos (es : List TimedJoin.TimedEntry) : 0<(entries es).1 := by
  induction es with
  | nil => decide
  | cons e es ih => exact lcm_pos _ _ (formula_pos e.entry.formula) ih

theorem build_pos (es fs : List TimedJoin.TimedEntry) : 0<(build es fs).1 :=
  lcm_pos _ _ (entries_pos es) (entries_pos fs)

def AtomDivides (M : Nat) (a : Atom) : Prop := match a with
  | .le _ => True
  | .dvd m _ => m∣M

theorem atom_dvd (a : Atom) (M : Nat) (hM : 0<M) (h : AtomDivides M a) : atom a∣M := by
  cases a with
  | le t => exact Nat.one_dvd _
  | dvd m t =>
    have hm : 1≤m := by
      have hh : m∣M := h
      rcases Nat.eq_zero_or_pos m with hz|hp
      · subst m
        have he : M=0 := Nat.zero_dvd.mp hh
        omega
      · omega
    simpa only [atom,Nat.max_eq_right hm] using h

theorem row_dvd (C : Conj) (M : Nat) (hM : 0<M)
    (h : ∀ a,a∈C→AtomDivides M a) : (row C).1∣M := by
  induction C with
  | nil => exact Nat.one_dvd _
  | cons a as ih =>
    exact Nat.lcm_dvd (atom_dvd a M hM (h a (by simp))) (ih (fun x hx=>h x (by simp [hx])))

theorem formula_dvd (F : Formula) (M : Nat) (hM : 0<M)
    (h : ExponentIntervals.Compatible M F) : (formula F).1∣M := by
  induction F with
  | nil => exact Nat.one_dvd _
  | cons C Cs ih =>
    exact Nat.lcm_dvd (row_dvd C M hM (fun a ha=>h C (by simp) a ha))
      (ih (fun D hD=>h D (by simp [hD])))

theorem entries_dvd (es : List TimedJoin.TimedEntry) (M : Nat) (hM : 0<M)
    (h : TimedJoin.Good M es) : (entries es).1∣M := by
  induction es with
  | nil => exact Nat.one_dvd _
  | cons e es ih =>
    exact Nat.lcm_dvd (formula_dvd e.entry.formula M hM (h e (by simp)))
      (ih (fun x hx=>h x (by simp [hx])))

theorem build_dvd (es fs : List TimedJoin.TimedEntry) (M : Nat) (hM : 0<M)
    (he : TimedJoin.Good M es) (hf : TimedJoin.Good M fs) : (build es fs).1∣M :=
  Nat.lcm_dvd (entries_dvd es M hM he) (entries_dvd fs M hM hf)

theorem build_le (es fs : List TimedJoin.TimedEntry) (M : Nat) (hM : 0<M)
    (he : TimedJoin.Good M es) (hf : TimedJoin.Good M fs) : (build es fs).1≤M :=
  Nat.le_of_dvd hM (build_dvd es fs M hM he hf)

theorem row_contains (C : Conj) (a : Atom) (ha : a∈C) : atom a∣(row C).1 := by
  induction C with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl|ha
    · exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_trans (ih ha) (Nat.dvd_lcm_right _ _)

theorem formula_contains (F : Formula) (C : Conj) (hC : C∈F) : (row C).1∣(formula F).1 := by
  induction F with
  | nil => simp at hC
  | cons D Ds ih =>
    rcases List.mem_cons.mp hC with rfl|hC
    · exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_trans (ih hC) (Nat.dvd_lcm_right _ _)

theorem entries_contains (es : List TimedJoin.TimedEntry) (e : TimedJoin.TimedEntry)
    (he : e∈es) : (formula e.entry.formula).1∣(entries es).1 := by
  induction es with
  | nil => simp at he
  | cons x xs ih =>
    rcases List.mem_cons.mp he with rfl|he
    · exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_trans (ih he) (Nat.dvd_lcm_right _ _)

theorem formula_good (F : Formula) (M : Nat) (hM : 0<M)
    (h : ExponentIntervals.Compatible M F) : ExponentIntervals.Compatible (formula F).1 F := by
  intro C hC a ha
  have hx := Nat.dvd_trans (row_contains C a ha) (formula_contains F C hC)
  cases a with
  | le t => trivial
  | dvd m t =>
    have hm : 1≤m := by
      have hd := h C hC (.dvd m t) ha
      change m∣M at hd
      rcases Nat.eq_zero_or_pos m with hz|hp
      · subst m
        have he : M=0 := Nat.zero_dvd.mp hd
        omega
      · omega
    simpa only [atom,Nat.max_eq_right hm] using hx

theorem entries_good (es : List TimedJoin.TimedEntry) (M : Nat) (hM : 0<M)
    (h : TimedJoin.Good M es) : TimedJoin.Good (entries es).1 es := by
  intro e he
  exact UniformPhaseBounds.compatible_multiple _ _ _
    (formula_good e.entry.formula M hM (h e he)) (entries_contains es e he)

theorem build_good (es fs : List TimedJoin.TimedEntry) (M : Nat) (hM : 0<M)
    (he : TimedJoin.Good M es) (hf : TimedJoin.Good M fs) :
    TimedJoin.Good (build es fs).1 es ∧ TimedJoin.Good (build es fs).1 fs := by
  constructor
  · intro e h
    exact UniformPhaseBounds.compatible_multiple _ _ _ (entries_good es M hM he e h)
      (Nat.dvd_lcm_left _ _)
  · intro e h
    exact UniformPhaseBounds.compatible_multiple _ _ _ (entries_good fs M hM hf e h)
      (Nat.dvd_lcm_right _ _)

theorem row_steps (C : Conj) : (row C).2=2*C.length+1 := by
  induction C with
  | nil => rfl
  | cons a as ih => simp only [row,List.length_cons,ih,Nat.mul_succ]

def cells (F : Formula) : Nat := (F.map (fun C=>C.length+1)).sum

theorem formula_steps (F : Formula) : (formula F).2=2*cells F+1 := by
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change (row C).2+(formula Cs).2+1=2*((C.length+1)+cells Cs)+1
    rw [row_steps,ih,Nat.mul_add,Nat.mul_succ]
    omega

def eventCells (es : List TimedJoin.TimedEntry) : Nat :=
  (es.map (fun e=>cells e.entry.formula+1)).sum

theorem entries_steps (es : List TimedJoin.TimedEntry) : (entries es).2=2*eventCells es+1 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change (formula e.entry.formula).2+(entries es).2+1=2*((cells e.entry.formula+1)+eventCells es)+1
    rw [formula_steps,ih,Nat.mul_add,Nat.mul_succ]
    omega

theorem build_steps (es fs : List TimedJoin.TimedEntry) :
    (build es fs).2=2*(eventCells es+eventCells fs)+3 := by
  simp only [build,entries_steps,Nat.mul_add]
  omega

theorem row_length_bound (C : Conj) : C.length≤UniformProjection.conjMeasure C := by
  induction C with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
    change as.length+1≤UniformProjection.atomMeasure a+UniformProjection.conjMeasure as+1
    omega

theorem cells_bound (F : Formula) : cells F≤UniformProjection.measure F := by
  induction F with
  | nil => exact Nat.le_refl _
  | cons C Cs ih =>
    have h := row_length_bound C
    change (C.length+1)+cells Cs≤UniformProjection.conjMeasure C+UniformProjection.measure Cs+1
    omega

theorem eventCells_bound (es : List TimedJoin.TimedEntry) (B : Nat)
    (h : ∀ e,e∈es→UniformProjection.measure e.entry.formula≤B) :
    eventCells es≤(B+1)*es.length := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
    have he := Nat.le_trans (cells_bound e.entry.formula) (h e (by simp))
    have ht := ih (fun x hx=>h x (by simp [hx]))
    change (cells e.entry.formula+1)+eventCells es≤(B+1)*(es.length+1)
    rw [Nat.mul_succ]
    omega

theorem build_steps_bound (es fs : List TimedJoin.TimedEntry) (S T : Nat)
    (he : ∀ e,e∈es→UniformProjection.measure e.entry.formula≤S)
    (hf : ∀ e,e∈fs→UniformProjection.measure e.entry.formula≤T) :
    (build es fs).2≤2*((S+1)*es.length+(T+1)*fs.length)+3 := by
  rw [build_steps]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _
    (Nat.add_le_add (eventCells_bound es S he) (eventCells_bound fs T hf))) 3

/-! Tail-recursive executable replacements preserve both output and
    measured work. A projected formula can contain many conjunctions;
    its proof definition must not require the same runtime stack depth. -/

def combine (a b : Nat×Nat) : Nat×Nat := (Nat.lcm a.1 b.1,a.2+b.2)

theorem combine_assoc (a b c : Nat×Nat) : combine (combine a b) c=combine a (combine b c) := by
  simp only [combine,Nat.lcm_assoc,Nat.add_assoc]

theorem combine_comm (a b : Nat×Nat) : combine a b=combine b a := by
  simp only [combine,Nat.lcm_comm,Nat.add_comm]

theorem combine_unit (a : Nat×Nat) : combine a (1,0)=a := by
  simp only [combine,Nat.lcm_one_right,Nat.add_zero]

theorem fold_start {X : Type} (g : X→Nat×Nat) (xs : List X) (a : Nat×Nat) :
    xs.foldl (fun r x=>combine r (g x)) a=
      combine a (xs.foldl (fun r x=>combine r (g x)) (1,0)) := by
  induction xs generalizing a with
  | nil => exact (combine_unit a).symm
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (combine a (g x)),ih (combine (1,0) (g x))]
    have hu : combine (1,0) (g x)=g x := by rw [combine_comm,combine_unit]
    rw [hu,combine_assoc]

def fastFold {X : Type} (g : X→Nat×Nat) (xs : List X) : Nat×Nat :=
  xs.foldl (fun r x=>combine r (g x)) (1,1)

theorem fastFold_cons {X : Type} (g : X→Nat×Nat) (x : X) (xs : List X) :
    fastFold g (x::xs)=combine (g x) (fastFold g xs) := by
  unfold fastFold
  rw [List.foldl_cons,fold_start g xs (combine (1,1) (g x)),fold_start g xs (1,1)]
  rw [combine_comm (1,1) (g x),combine_assoc]

def rowFast (C : Conj) : Nat×Nat := fastFold (fun a=>(atom a,2)) C

@[csimp] theorem row_fast : row=rowFast := by
  funext C
  induction C with
  | nil => rfl
  | cons a as ih =>
    change (Nat.lcm (atom a) (row as).1,(row as).2+2)=fastFold _ (a::as)
    rw [fastFold_cons,ih]
    simp only [combine,Nat.add_comm]
    rfl

def formulaFast (F : Formula) : Nat×Nat := fastFold (fun C=>let r:=row C; (r.1,r.2+1)) F

@[csimp] theorem formula_fast : formula=formulaFast := by
  funext F
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change (Nat.lcm (row C).1 (formula Cs).1,(row C).2+(formula Cs).2+1)=fastFold _ (C::Cs)
    rw [fastFold_cons,ih]
    simp only [combine,formulaFast]
    congr 1
    omega

def entriesFast (es : List TimedJoin.TimedEntry) : Nat×Nat :=
  fastFold (fun e=>let r:=formula e.entry.formula; (r.1,r.2+1)) es

@[csimp] theorem entries_fast : entries=entriesFast := by
  funext es
  induction es with
  | nil => rfl
  | cons e es ih =>
    change (Nat.lcm (formula e.entry.formula).1 (entries es).1,
      (formula e.entry.formula).2+(entries es).2+1)=fastFold _ (e::es)
    rw [fastFold_cons,ih]
    simp only [combine,entriesFast]
    congr 1
    omega

/-- Compiled after the three replacement equalities, so calls made by
    this entry point also use the verified tail-recursive traversals. -/
def buildFast (es fs : List TimedJoin.TimedEntry) : Nat×Nat :=
  let a:=entries es; let b:=entries fs; (Nat.lcm a.1 b.1,a.2+b.2+1)

@[csimp] theorem build_fast : build=buildFast := by
  funext es fs
  rfl

end REWB.ActualModulus
