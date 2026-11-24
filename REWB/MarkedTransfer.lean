import REWB.RangeProducts

/-! Boolean relations are executable over an explicitly enumerated finite
    state space. Composition does not assume invertibility. -/
namespace REWB.FiniteRelation

structure Enumeration (S : Type) where
  elems : List S
  complete : ∀ x : S, x ∈ elems

variable {S : Type}

def any (e : Enumeration S) (p : S → Bool) : Bool :=
  e.elems.any p

theorem any_true (e : Enumeration S) (p : S → Bool) :
    any e p = true ↔ ∃ x, p x = true := by
  rw [any,List.any_eq_true]
  constructor
  · rintro ⟨x,_,hx⟩
    exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,e.complete x,hx⟩

def finEnum (n : Nat) : Enumeration (Fin n) :=
  ⟨List.ofFn id,by intro x; simp⟩

def sumEnum (a : Enumeration S) {T : Type} (b : Enumeration T) : Enumeration (Sum S T) :=
  ⟨a.elems.map Sum.inl ++ b.elems.map Sum.inr,by
    intro x
    cases x with
    | inl s => exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨s,a.complete s,rfl⟩))
    | inr t => exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨t,b.complete t,rfl⟩))⟩

private theorem bool_ext (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

abbrev Rel (S : Type) := S → S → Bool

def ident [DecidableEq S] : Rel S := fun p q => decide (p=q)

def comp (e : Enumeration S) (a b : Rel S) : Rel S :=
  fun p q => any e (fun r => a p r && b r q)

theorem comp_true (e : Enumeration S) (a b : Rel S) (p q : S) :
    comp e a b p q = true ↔ ∃ r, a p r = true ∧ b r q = true := by
  simp only [comp,any_true,Bool.and_eq_true]

theorem comp_assoc (e : Enumeration S) (a b c : Rel S) :
    comp e (comp e a b) c = comp e a (comp e b c) := by
  funext p q
  apply bool_ext
  simp only [comp_true]
  constructor
  · rintro ⟨r,⟨s,has,hbs⟩,hcr⟩
    exact ⟨s,has,r,hbs,hcr⟩
  · rintro ⟨s,has,r,hbs,hcr⟩
    exact ⟨r,⟨s,has,hbs⟩,hcr⟩

theorem ident_left [DecidableEq S] (e : Enumeration S) (a : Rel S) :
    comp e ident a = a := by
  funext p q
  apply bool_ext
  simp only [comp_true,ident,decide_eq_true_eq]
  constructor
  · rintro ⟨r,rfl,h⟩
    exact h
  · intro h
    exact ⟨p,rfl,h⟩

theorem ident_right [DecidableEq S] (e : Enumeration S) (a : Rel S) :
    comp e a ident = a := by
  funext p q
  apply bool_ext
  simp only [comp_true,ident,decide_eq_true_eq]
  constructor
  · rintro ⟨r,h,rfl⟩
    exact h
  · intro h
    exact ⟨q,h,rfl⟩

def ops [DecidableEq S] (e : Enumeration S) : RangeProducts.Ops (Rel S) :=
  ⟨ident,comp e,ident_left e,ident_right e,comp_assoc e⟩

/-- Apply a Boolean relation to a vector of accepting continuation states. -/
def pre (e : Enumeration S) (r : Rel S) (v : S → Bool) (p : S) : Bool :=
  any e (fun q => r p q && v q)

theorem pre_true (e : Enumeration S) (r : Rel S) (v : S → Bool) (p : S) :
    pre e r v p = true ↔ ∃ q, r p q = true ∧ v q = true := by
  simp only [pre,any_true,Bool.and_eq_true]

theorem pre_comp (e : Enumeration S) (r s : Rel S) (v : S → Bool) (p : S) :
    pre e (comp e r s) v p = pre e r (pre e s v) p := by
  apply bool_ext
  simp only [pre_true,comp_true]
  constructor
  · rintro ⟨q,⟨m,hr,hs⟩,hv⟩
    exact ⟨m,hr,q,hs,hv⟩
  · rintro ⟨m,hr,q,hs,hv⟩
    exact ⟨q,⟨m,hr,hs⟩,hv⟩

theorem pre_ident [DecidableEq S] (e : Enumeration S) (v : S → Bool) (p : S) :
    pre e ident v p = v p := by
  apply bool_ext
  simp only [pre_true,ident,decide_eq_true_eq]
  constructor
  · rintro ⟨q,rfl,h⟩
    exact h
  · intro h
    exact ⟨p,rfl,h⟩

def deterministic [DecidableEq S] (f : S → S) : Rel S := fun p q => decide (f p=q)

theorem pre_deterministic [DecidableEq S] (e : Enumeration S)
    (f : S → S) (v : S → Bool) (p : S) :
    pre e (deterministic f) v p = v (f p) := by
  apply bool_ext
  simp only [pre_true,deterministic,decide_eq_true_eq]
  constructor
  · rintro ⟨q,rfl,h⟩
    exact h
  · intro h
    exact ⟨f p,rfl,h⟩

end REWB.FiniteRelation

namespace REWB.MarkedTransfer
open FiniteRelation

variable {α : Type}

abbrev Phase (d b : DFA α) := Sum (Fin d.stateCount) (Fin b.stateCount)

def enum (d b : DFA α) : Enumeration (Phase d b) :=
  sumEnum (finEnum d.stateCount) (finEnum b.stateCount)

/-- At a marked boundary an accepting D state can switch to B. The
    identity alternative is always retained. -/
def epsilon (d b : DFA α) (m : Bool) : Rel (Phase d b)
  | .inl q,.inr r => m && d.final q && decide (r=b.initial)
  | p,q => decide (p=q)

def advance (d b : DFA α) (c : α) : Phase d b → Phase d b
  | .inl q => .inl (d.step q c)
  | .inr q => .inr (b.step q c)

def letter (d b : DFA α) (x : α × Bool) : Rel (Phase d b) :=
  comp (enum d b) (epsilon d b x.2) (deterministic (advance d b x.1))

def final (d b : DFA α) : Phase d b → Bool
  | .inl _ => false
  | .inr r => b.final r

theorem epsilon_left (d b : DFA α) (m : Bool) (v : Phase d b → Bool)
    (q : Fin d.stateCount) :
    pre (enum d b) (epsilon d b m) v (.inl q) =
      (v (.inl q) || ((m && d.final q) && v (.inr b.initial))) := by
  apply bool_ext
  simp only [pre_true,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨r,he,hv⟩
    cases r with
    | inl r =>
      have h : q=r := by simpa [epsilon] using he
      subst r
      exact Or.inl hv
    | inr r =>
      have h : (m=true ∧ d.final q=true) ∧ r=b.initial := by
        simpa only [epsilon,Bool.and_eq_true,decide_eq_true_eq] using he
      rcases h with ⟨hh,rfl⟩
      exact Or.inr ⟨hh,hv⟩
  · rintro (h | ⟨⟨hm,hq⟩,hv⟩)
    · exact ⟨.inl q,by simp [epsilon],h⟩
    · exact ⟨.inr b.initial,by simp [epsilon,hm,hq],hv⟩

theorem epsilon_right (d b : DFA α) (m : Bool) (v : Phase d b → Bool)
    (q : Fin b.stateCount) :
    pre (enum d b) (epsilon d b m) v (.inr q) = v (.inr q) := by
  apply bool_ext
  simp only [pre_true]
  constructor
  · rintro ⟨r,he,hv⟩
    have h : Sum.inr q = r := by
      cases r <;> simpa [epsilon] using he
    rwa [← h] at hv
  · intro h
    exact ⟨.inr q,by simp [epsilon],h⟩

def transfer (d b : DFA α) (w : MarkedDP.MarkedWord α) : Rel (Phase d b) :=
  RangeProducts.product (ops (enum d b)) (w.map (letter d b))

/-- The terminal mark is handled separately, including when w is empty. -/
def run (d b : DFA α) (terminal : Bool) (w : MarkedDP.MarkedWord α)
    (q : Phase d b) : Bool :=
  pre (enum d b) (transfer d b w)
    (pre (enum d b) (epsilon d b terminal) (final d b)) q

theorem run_cons (d b : DFA α) (terminal : Bool) (x : α × Bool)
    (xs : MarkedDP.MarkedWord α) (q : Phase d b) :
    run d b terminal (x :: xs) q =
      pre (enum d b) (epsilon d b x.2)
        (fun p => run d b terminal xs (advance d b x.1 p)) q := by
  unfold run
  change pre (enum d b) (comp (enum d b) (letter d b x) (transfer d b xs)) _ q = _
  rw [pre_comp]
  unfold letter
  rw [pre_comp]
  congr 1
  funext p
  rw [pre_deterministic]

theorem run_right (d b : DFA α) (terminal : Bool) (w : MarkedDP.MarkedWord α)
    (q : Fin b.stateCount) :
    run d b terminal w (.inr q) = (MarkedDP.summarize d b terminal w).suffixAccept q := by
  induction w generalizing q with
  | nil =>
    change pre (enum d b) ident
      (pre (enum d b) (epsilon d b terminal) (final d b)) (.inr q) = b.final q
    rw [pre_ident,epsilon_right]
    rfl
  | cons x xs ih =>
    rcases x with ⟨c,m⟩
    rw [run_cons,epsilon_right]
    change run d b terminal xs (.inr (b.step q c)) =
      (MarkedDP.summarize d b terminal xs).suffixAccept (b.step q c)
    exact ih _

theorem run_left (d b : DFA α) (terminal : Bool) (w : MarkedDP.MarkedWord α)
    (q : Fin d.stateCount) :
    run d b terminal w (.inl q) = (MarkedDP.summarize d b terminal w).canSwitch q := by
  induction w generalizing q with
  | nil =>
    change pre (enum d b) ident
      (pre (enum d b) (epsilon d b terminal) (final d b)) (.inl q) =
        ((terminal && d.final q) && b.final b.initial)
    rw [pre_ident,epsilon_left]
    rfl
  | cons x xs ih =>
    rcases x with ⟨c,m⟩
    rw [run_cons,epsilon_left]
    change run d b terminal xs (.inl (d.step q c)) ||
      ((m && d.final q) && run d b terminal xs (.inr (b.step b.initial c))) =
        (((m && d.final q) &&
          (MarkedDP.summarize d b terminal xs).suffixAccept (b.step b.initial c)) ||
          (MarkedDP.summarize d b terminal xs).canSwitch (d.step q c))
    rw [ih,run_right,Bool.or_comm]

theorem run_correct (d b : DFA α) (terminal : Bool) (w : MarkedDP.MarkedWord α)
    (q : Fin d.stateCount) :
    run d b terminal w (.inl q) = true ↔
      ∃ pre suf, w = pre ++ suf ∧ MarkedDP.markAtHead terminal suf = true ∧
        d.final (d.run q (MarkedDP.text pre)) = true ∧ b.accepts (MarkedDP.text suf) := by
  rw [run_left,MarkedDP.canSwitch_correct]

theorem transfer_append (d b : DFA α) (x y : MarkedDP.MarkedWord α) :
    transfer d b (x ++ y) =
      comp (enum d b) (transfer d b x) (transfer d b y) := by
  simp only [transfer,List.map_append,RangeProducts.product_append,ops]

end REWB.MarkedTransfer
