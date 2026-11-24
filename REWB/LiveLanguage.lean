import REWB.PrunedSkeletons

/-! The liveness pass is a two-state transducer. Kleene iteration becomes
    a walk on the two possible live-in/live-out flags. This module proves
    a closed regular-language expression for every such walk. -/
namespace REWB.LiveLanguage
variable {X : Type}

def join (L R : Language X) (w : Word X) : Prop :=
  ∃ x y, w=x++y ∧ L x ∧ R y

inductive Star (L : Language X) : Language X where
  | nil : Star L []
  | cons {u v : Word X} : L u → Star L v → Star L (u++v)

inductive Walk (E : Bool→Bool→Language X) : Bool→Bool→Language X where
  | nil (q : Bool) : Walk E q q []
  | cons {a b c : Bool} {u v : Word X} :
      E a b u → Walk E b c v → Walk E a c (u++v)

namespace Walk
variable {E : Bool→Bool→Language X}

theorem edge {a b : Bool} {w : Word X} (h : E a b w) : Walk E a b w := by
  simpa only [List.append_nil] using Walk.cons h (Walk.nil b)

theorem append {a b c : Bool} {u v : Word X}
    (hu : Walk E a b u) (hv : Walk E b c v) : Walk E a c (u++v) := by
  induction hu with
  | nil q => exact hv
  | cons hstep hrest ih =>
    rw [List.append_assoc]
    exact Walk.cons hstep (ih hv)

end Walk

theorem star_walk {E : Bool→Bool→Language X} {L : Language X} {q : Bool}
    (h : ∀ w,L w→Walk E q q w) {w : Word X} (hw : Star L w) :
    Walk E q q w := by
  induction hw with
  | nil => exact .nil q
  | cons hu hv ih => exact Walk.append (h _ hu) ih

def selfOne (E : Bool→Bool→Language X) : Language X := Star (E true true)

def excursion (E : Bool→Bool→Language X) (w : Word X) : Prop :=
  ∃ x y z, w=x++y++z ∧ E false true x ∧ selfOne E y ∧ E true false z

def loopZero (E : Bool→Bool→Language X) : Language X :=
  Star (fun w=> E false false w ∨ excursion E w)

/-- Explicit two-state elimination. These are standard regular operations
    over the four edge languages, with only a constant number of factors. -/
def shape (E : Bool→Bool→Language X) : Bool→Bool→Language X
  | false,false => loopZero E
  | false,true => fun w => ∃ x y z,
      w=x++y++z ∧ loopZero E x ∧ E false true y ∧ selfOne E z
  | true,false => fun w => ∃ x y z,
      w=x++y++z ∧ selfOne E x ∧ E true false y ∧ loopZero E z
  | true,true => fun w => selfOne E w ∨ ∃ a b c d e,
      w=a++b++c++d++e ∧ selfOne E a ∧ E true false b ∧
        loopZero E c ∧ E false true d ∧ selfOne E e

theorem one_sound {E : Bool→Bool→Language X} {w : Word X}
    (h : selfOne E w) : Walk E true true w :=
  star_walk (fun _ hu=>Walk.edge hu) h

theorem excursion_sound {E : Bool→Bool→Language X} {w : Word X}
    (h : excursion E w) : Walk E false false w := by
  rcases h with ⟨x,y,z,rfl,hx,hy,hz⟩
  exact Walk.append (Walk.append (Walk.edge hx) (one_sound hy)) (Walk.edge hz)

theorem zero_sound {E : Bool→Bool→Language X} {w : Word X}
    (h : loopZero E w) : Walk E false false w :=
  star_walk (fun _ h=>h.elim Walk.edge excursion_sound) h

theorem shape_sound {E : Bool→Bool→Language X} {a b : Bool} {w : Word X}
    (h : shape E a b w) : Walk E a b w := by
  cases a <;> cases b
  · exact zero_sound h
  · rcases h with ⟨x,y,z,rfl,hx,hy,hz⟩
    exact Walk.append (Walk.append (zero_sound hx) (Walk.edge hy)) (one_sound hz)
  · rcases h with ⟨x,y,z,rfl,hx,hy,hz⟩
    exact Walk.append (Walk.append (one_sound hx) (Walk.edge hy)) (zero_sound hz)
  · rcases h with h|⟨x,y,z,u,v,rfl,hx,hy,hz,hu,hv⟩
    · exact one_sound h
    · exact Walk.append (Walk.append (Walk.append (Walk.append (one_sound hx)
        (Walk.edge hy)) (zero_sound hz)) (Walk.edge hu)) (one_sound hv)

theorem shape_step {E : Bool→Bool→Language X} (a b c : Bool)
    (u v : Word X) (hu : E a b u) (hv : shape E b c v) :
    shape E a c (u++v) := by
  cases a <;> cases b <;> cases c
  · exact Star.cons (Or.inl hu) hv
  · rcases hv with ⟨x,y,z,rfl,hx,hy,hz⟩
    refine ⟨u++x,y,z,?_,Star.cons (Or.inl hu) hx,hy,hz⟩
    simp only [List.append_assoc]
  · rcases hv with ⟨x,y,z,rfl,hx,hy,hz⟩
    have he : excursion E (u++x++y) := ⟨u,x,y,rfl,hu,hx,hy⟩
    have h : loopZero E ((u++x++y)++z) := Star.cons (Or.inr he) hz
    simpa only [List.append_assoc] using h
  · rcases hv with h|⟨x,y,z,p,q,rfl,hx,hy,hz,hp,hq⟩
    · exact ⟨[],u,v,by simp,Star.nil,hu,h⟩
    · have he : excursion E (u++x++y) := ⟨u,x,y,rfl,hu,hx,hy⟩
      refine ⟨(u++x++y)++z,p,q,?_,Star.cons (Or.inr he) hz,hp,hq⟩
      simp only [List.append_assoc]
  · exact ⟨[],u,v,by simp,Star.nil,hu,hv⟩
  · rcases hv with ⟨x,y,z,rfl,hx,hy,hz⟩
    exact Or.inr ⟨[],u,x,y,z,by simp only [List.nil_append,List.append_assoc],
      Star.nil,hu,hx,hy,hz⟩
  · rcases hv with ⟨x,y,z,rfl,hx,hy,hz⟩
    refine ⟨u++x,y,z,?_,Star.cons hu hx,hy,hz⟩
    simp only [List.append_assoc]
  · rcases hv with h|⟨x,y,z,p,q,rfl,hx,hy,hz,hp,hq⟩
    · exact Or.inl (Star.cons hu h)
    · refine Or.inr ⟨u++x,y,z,p,q,?_,Star.cons hu hx,hy,hz,hp,hq⟩
      simp only [List.append_assoc]

theorem shape_complete {E : Bool→Bool→Language X} {a b : Bool} {w : Word X}
    (h : Walk E a b w) : shape E a b w := by
  induction h with
  | nil q =>
    cases q
    · exact Star.nil
    · exact Or.inl Star.nil
  | cons hu hv ih => exact shape_step _ _ _ _ _ hu ih

theorem shape_iff_walk (E : Bool→Bool→Language X) (a b : Bool) (w : Word X) :
    shape E a b w ↔ Walk E a b w :=
  ⟨shape_sound,shape_complete⟩

end REWB.LiveLanguage
