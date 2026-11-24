import REWB.IndexedMarked

/-! A generic ordered exit from a nondeterministic left phase into a
    deterministic right phase. All switches occur at actual boundaries.
    In particular the final boundary may be selected. -/
namespace REWB.OrderedExit
open FiniteRelation
variable {S α : Type} [DecidableEq S]

private theorem beq_ext (x y : Bool) (h : x = true ↔ y = true) : x=y := by
  cases x <;> cases y <;> simp_all

structure Machine (S α : Type) where
  states : Enumeration S
  stay : (α × Bool) → Rel S
  gate : Bool → S → Bool
  right : DFA α

namespace Machine

variable (M : Machine S α)

abbrev State := Sum S (Fin M.right.stateCount)

def enum : Enumeration M.State :=
  sumEnum M.states (finEnum M.right.stateCount)

def letter (x : α × Bool) : Rel M.State
  | .inl p,.inl q => M.stay x p q
  | .inl p,.inr q => M.gate x.2 p && decide (M.right.step M.right.initial x.1=q)
  | .inr _,.inl _ => false
  | .inr p,.inr q => decide (M.right.step p x.1=q)

def final (terminal : Bool) : M.State → Bool
  | .inl p => M.gate terminal p && M.right.final M.right.initial
  | .inr p => M.right.final p

def transfer (w : MarkedDP.MarkedWord α) : Rel M.State :=
  RangeProducts.product (FiniteRelation.ops M.enum) (w.map M.letter)

def leftProduct (w : MarkedDP.MarkedWord α) : Rel S :=
  RangeProducts.product (FiniteRelation.ops M.states) (w.map M.stay)

def run (terminal : Bool) (w : MarkedDP.MarkedWord α) (s : M.State) : Bool :=
  pre M.enum (M.transfer w) (M.final terminal) s

theorem run_nil (terminal : Bool) (s : M.State) :
    M.run terminal [] s = M.final terminal s := by
  change pre M.enum ident (M.final terminal) s = _
  exact pre_ident _ _ _

theorem run_cons (terminal : Bool) (x : α × Bool) (w : MarkedDP.MarkedWord α)
    (s : M.State) :
    M.run terminal (x::w) s = pre M.enum (M.letter x) (M.run terminal w) s := by
  change pre M.enum (comp M.enum (M.letter x) (M.transfer w)) _ s = _
  rw [pre_comp]
  rfl

theorem run_right (terminal : Bool) (w : MarkedDP.MarkedWord α)
    (q : Fin M.right.stateCount) :
    M.run terminal w (.inr q) = M.right.final (M.right.run q (MarkedDP.text w)) := by
  induction w generalizing q with
  | nil => rw [run_nil]; rfl
  | cons x xs ih =>
    rw [run_cons]
    have h : pre M.enum (M.letter x) (M.run terminal xs) (.inr q) =
        M.run terminal xs (.inr (M.right.step q x.1)) := by
      apply beq_ext
      rw [pre_true]
      constructor
      · rintro ⟨r,hr,hv⟩
        cases r with
        | inl r => simp [letter] at hr
        | inr r =>
          have hh : M.right.step q x.1=r := by simpa only [letter,decide_eq_true_eq] using hr
          subst r
          exact hv
      · intro h
        exact ⟨.inr (M.right.step q x.1),by simp [letter],h⟩
    rw [h,ih]
    rfl

theorem run_left_cons (terminal : Bool) (x : α × Bool)
    (xs : MarkedDP.MarkedWord α) (p : S) :
    M.run terminal (x::xs) (.inl p) = true ↔
      (M.gate x.2 p = true ∧ M.right.accepts (MarkedDP.text (x::xs))) ∨
        ∃ q, M.stay x p q = true ∧ M.run terminal xs (.inl q) = true := by
  rw [run_cons,pre_true]
  constructor
  · rintro ⟨r,hr,hv⟩
    cases r with
    | inl q => exact Or.inr ⟨q,hr,hv⟩
    | inr q =>
      have hh : M.gate x.2 p=true ∧ M.right.step M.right.initial x.1=q := by
        simpa only [letter,Bool.and_eq_true,decide_eq_true_eq] using hr
      rcases hh with ⟨hg,rfl⟩
      rw [run_right] at hv
      exact Or.inl ⟨hg,hv⟩
  · rintro (⟨hg,hb⟩ | ⟨q,hq,hv⟩)
    · refine ⟨.inr (M.right.step M.right.initial x.1),?_,?_⟩
      · simp [letter,hg]
      · rw [run_right]
        exact hb
    · exact ⟨.inl q,hq,hv⟩

theorem leftProduct_nil : M.leftProduct [] = ident := rfl

theorem leftProduct_cons (x : α × Bool) (w : MarkedDP.MarkedWord α) :
    M.leftProduct (x::w) = comp M.states (M.stay x) (M.leftProduct w) := rfl

/-- Select the unique boundary where the path enters the right phase.
    The left path is preserved as a relation, not collapsed to unrelated
    existential witnesses for its endpoint and guard. -/
theorem run_left (terminal : Bool) (w : MarkedDP.MarkedWord α) (p : S) :
    M.run terminal w (.inl p) = true ↔
      ∃ pre suf, w = pre++suf ∧
        FiniteRelation.pre M.states (M.leftProduct pre)
          (M.gate (MarkedDP.markAtHead terminal suf)) p = true ∧
        M.right.accepts (MarkedDP.text suf) := by
  induction w generalizing p with
  | nil =>
    rw [run_nil]
    change (M.gate terminal p && M.right.final M.right.initial)=true ↔ _
    rw [Bool.and_eq_true]
    constructor
    · rintro ⟨hg,hb⟩
      refine ⟨[],[],rfl,?_,hb⟩
      rw [leftProduct_nil,pre_ident]
      exact hg
    · rintro ⟨pre,suf,he,hg,hb⟩
      cases pre with
      | cons x xs => cases he
      | nil =>
        have h : ([] : MarkedDP.MarkedWord α) = suf := he
        subst suf
        rw [leftProduct_nil,pre_ident] at hg
        exact ⟨hg,hb⟩
  | cons x xs ih =>
    rw [run_left_cons]
    constructor
    · rintro (⟨hg,hb⟩ | ⟨q,hq,hr⟩)
      · refine ⟨[],x::xs,rfl,?_,hb⟩
        rw [leftProduct_nil,pre_ident]
        cases x
        exact hg
      · obtain ⟨pre,suf,he,hg,hb⟩ := (ih q).mp hr
        refine ⟨x::pre,suf,congrArg (List.cons x) he,?_,hb⟩
        rw [leftProduct_cons,pre_comp,pre_true]
        exact ⟨q,hq,hg⟩
    · rintro ⟨pre,suf,he,hg,hb⟩
      cases pre with
      | nil =>
        have h : x::xs = suf := he
        subst suf
        rw [leftProduct_nil,pre_ident] at hg
        exact Or.inl ⟨by cases x; exact hg,hb⟩
      | cons y ys =>
        have h : x=y ∧ xs=ys++suf := by simpa using he
        rcases h with ⟨rfl,h⟩
        rw [leftProduct_cons,pre_comp,pre_true] at hg
        obtain ⟨q,hq,hv⟩ := hg
        exact Or.inr ⟨q,hq,(ih q).mpr ⟨ys,suf,h,hv,hb⟩⟩

end Machine
end REWB.OrderedExit

namespace REWB.TensorRelation
open FiniteRelation
variable {S T : Type} [DecidableEq T]

def pairEnum (s : Enumeration S) (t : Enumeration T) : Enumeration (S × T) :=
  ⟨s.elems.flatMap (fun p => t.elems.map (fun q => (p,q))),by
    rintro ⟨p,q⟩
    exact List.mem_flatMap.mpr ⟨p,s.complete p,List.mem_map.mpr ⟨q,t.complete q,rfl⟩⟩⟩

def tensor (r : Rel S) (f : T → T) : Rel (S × T) :=
  fun p q => r p.1 q.1 && decide (f p.2=q.2)

private theorem beq_ext (a b : Bool) (h : a=true ↔ b=true) : a=b := by
  cases a <;> cases b <;> simp_all

theorem tensor_comp (s : Enumeration S) (t : Enumeration T)
    (a b : Rel S) (f g : T → T) :
    comp (pairEnum s t) (tensor a f) (tensor b g) =
      tensor (comp s a b) (fun q => g (f q)) := by
  funext p q
  rcases p with ⟨p,u⟩
  rcases q with ⟨q,v⟩
  apply beq_ext
  simp only [comp_true,tensor,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨r,z⟩,⟨ha,hf⟩,hb,hg⟩
    exact ⟨⟨r,ha,hb⟩,hf ▸ hg⟩
  · rintro ⟨⟨r,ha,hb⟩,hfg⟩
    exact ⟨(r,f u),⟨ha,rfl⟩,hb,hfg⟩

theorem tensor_ident [DecidableEq S] :
    tensor (ident : Rel S) (id : T → T) = ident := by
  funext p q
  rcases p with ⟨p,u⟩
  rcases q with ⟨q,v⟩
  apply beq_ext
  simp [tensor,ident]

theorem pre_tensor (s : Enumeration S) (t : Enumeration T)
    (a : Rel S) (f : T → T) (v : S × T → Bool) (p : S) (q : T) :
    pre (pairEnum s t) (tensor a f) v (p,q) =
      pre s a (fun r => v (r,f q)) p := by
  apply beq_ext
  simp only [pre_true,tensor,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨r,z⟩,⟨ha,hf⟩,hv⟩
    exact ⟨r,ha,hf.symm ▸ hv⟩
  · rintro ⟨r,ha,hv⟩
    exact ⟨(r,f q),⟨ha,rfl⟩,hv⟩

end REWB.TensorRelation
