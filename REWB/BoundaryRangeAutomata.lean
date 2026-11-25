import REWB.BoundaryRangeCases
import REWB.BoundaryApplicationRange
import REWB.RegularDFA

/-! Concrete finite automata used by the boundary-block dispatch.
Changing an initial state or final subset preserves the transition
graph. Intersection, one split, and reversal are constructed over
explicit finite state universes. -/
namespace REWB.BoundaryRange.Automata
open REWB.Spec (slice)
open REWB.BoundaryApplication
variable {α : Type}

def change (d : DFA α) (q : Fin d.stateCount) (F : Fin d.stateCount→Bool) : DFA α :=
  ⟨d.stateCount,q,d.step,F⟩

theorem change_run (d : DFA α) (q : Fin d.stateCount) (F : Fin d.stateCount→Bool)
    (s : Fin d.stateCount) (w : Word α) : (change d q F).run s w=d.run s w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih (d.step s a)

theorem change_accepts (d : DFA α) (q : Fin d.stateCount) (F : Fin d.stateCount→Bool)
    (w : Word α) : (change d q F).accepts w ↔ F (d.run q w)=true := by
  change F ((change d q F).run q w)=true ↔ _
  rw [change_run]

def start (d : DFA α) (q : Fin d.stateCount) : DFA α := change d q d.final
def finish (d : DFA α) (F : Fin d.stateCount→Bool) : DFA α := change d d.initial F
def stop (d : DFA α) (q : Fin d.stateCount) : DFA α := finish d (fun s=>decide (s=q))
def tail (d : DFA α) (tr : Range.Map d.stateCount) : DFA α :=
  finish d (fun q=>d.final (tr.get q))

theorem start_accepts (d : DFA α) (q : Fin d.stateCount) (w : Word α) :
    (start d q).accepts w ↔ d.final (d.run q w)=true := change_accepts d q d.final w

theorem finish_accepts (d : DFA α) (F : Fin d.stateCount→Bool) (w : Word α) :
    (finish d F).accepts w ↔ F (d.run d.initial w)=true := change_accepts d d.initial F w

theorem stop_accepts (d : DFA α) (q : Fin d.stateCount) (w : Word α) :
    (stop d q).accepts w ↔ d.run d.initial w=q := by
  rw [stop,finish_accepts,decide_eq_true_eq]

theorem tail_accepts (d : DFA α) (tr : Range.Map d.stateCount) (w : Word α) :
    (tail d tr).accepts w ↔ d.final (tr.get (d.run d.initial w))=true :=
  finish_accepts d _ w

theorem tail_slice (d : DFA α) (w : Word α) (a g p : Nat)
    (hag : a≤g) (hgp : g≤p) (hp : p≤w.length) :
    (tail d (Range.query d (Range.build d w) g p).map).accepts (slice w a g) ↔
      d.accepts (slice w a p) := by
  rw [tail_accepts,Range.query_correct d w g p hgp hp]
  rw [OuterColumn.slice_split w a g p hag hgp]
  simp only [DFA.accepts,DFA.run_append]

theorem start_slice (d : DFA α) (w : Word α) (p g j : Nat)
    (hpg : p≤g) (hgj : g≤j) (hg : g≤w.length) :
    (start d ((Range.query d (Range.build d w) p g).map.get d.initial)).accepts
      (slice w g j) ↔ d.accepts (slice w p j) := by
  rw [start_accepts,Range.query_correct d w p g hpg hg]
  rw [OuterColumn.slice_split w p g j hpg hgj]
  simp only [DFA.accepts,DFA.run_append]

def intersectionMachine (A B : DFA α) : RegularDFA.Machine α :=
  ⟨Fin A.stateCount×Fin B.stateCount,inferInstance,
    RegularDFA.prodEnum (FiniteRelation.finEnum A.stateCount) (FiniteRelation.finEnum B.stateCount),
    (A.initial,B.initial),(fun q c=>(A.step q.1 c,B.step q.2 c)),
    (fun q=>A.final q.1 && B.final q.2)⟩

theorem intersection_run (A B : DFA α) (a : Fin A.stateCount) (b : Fin B.stateCount)
    (w : Word α) : (intersectionMachine A B).run (a,b) w=(A.run a w,B.run b w) := by
  induction w generalizing a b with
  | nil => rfl
  | cons c w ih => exact ih (A.step a c) (B.step b c)

def meet (A B : DFA α) : DFA α := (intersectionMachine A B).toDFA

theorem meet_accepts (A B : DFA α) (w : Word α) :
    (meet A B).accepts w ↔ A.accepts w ∧ B.accepts w := by
  rw [meet,RegularDFA.Machine.toDFA_correct]
  change ((intersectionMachine A B).run (A.initial,B.initial) w |> fun q=>
    A.final q.1 && B.final q.2)=true ↔ _
  rw [intersection_run,Bool.and_eq_true]
  rfl

def join (A B : DFA α) : DFA α :=
  (RegularDFA.concatenate (RegularDFA.lift A) (RegularDFA.lift B)).toDFA

theorem join_accepts (A B : DFA α) (w : Word α) :
    (join A B).accepts w ↔ ∃u v,w=u++v ∧ A.accepts u ∧ B.accepts v := by
  rw [join,RegularDFA.Machine.toDFA_correct,RegularDFA.concatenate_correct]
  simp only [LiveLanguage.join,RegularDFA.lift_correct]

theorem slice_take (w : Word α) (a p j : Nat) (hap : a≤p) (hpj : p≤j) (hj : j≤w.length) :
    (slice w a j).take (p-a)=slice w a p := by
  have hl:=OuterColumn.slice_length w a p hap (by omega)
  rw [OuterColumn.slice_split w a p j hap hpj,←hl,List.take_left]

theorem slice_drop (w : Word α) (a p j : Nat) (hap : a≤p) (hpj : p≤j) (hj : j≤w.length) :
    (slice w a j).drop (p-a)=slice w p j := by
  have hl:=OuterColumn.slice_length w a p hap (by omega)
  rw [OuterColumn.slice_split w a p j hap hpj,←hl,List.drop_left]

theorem join_slice (A B : DFA α) (w : Word α) (a j : Nat) (haj : a≤j) (hj : j≤w.length) :
    (join A B).accepts (slice w a j) ↔
      ∃p,a≤p ∧ p≤j ∧ A.accepts (slice w a p) ∧ B.accepts (slice w p j) := by
  rw [join_accepts]
  constructor
  · rintro ⟨u,v,he,hA,hB⟩
    have hl:=congrArg List.length he
    rw [OuterColumn.slice_length w a j haj hj,List.length_append] at hl
    have hp : a+u.length≤j := by omega
    have hsub : a+u.length-a=u.length := by omega
    have hu:=slice_take w a (a+u.length) j (by omega) hp hj
    rw [he,hsub,List.take_left] at hu
    have hv:=slice_drop w a (a+u.length) j (by omega) hp hj
    rw [he,hsub,List.drop_left] at hv
    exact ⟨a+u.length,by omega,hp,hu ▸ hA,hv ▸ hB⟩
  · rintro ⟨p,hap,hpj,hA,hB⟩
    exact ⟨slice w a p,slice w p j,OuterColumn.slice_split w a p j hap hpj,hA,hB⟩

def gap (C K D : DFA α) (c : Fin C.stateCount) (k : Fin K.stateCount) : DFA α :=
  join (meet (start C c) (start K k)) D

theorem gap_slice (C K D : DFA α) (w : Word α) (c : Fin C.stateCount)
    (k : Fin K.stateCount) (a j : Nat) (haj : a≤j) (hj : j≤w.length) :
    (gap C K D c k).accepts (slice w a j) ↔
      ∃p,a≤p ∧ p≤j ∧ C.final (C.run c (slice w a p))=true ∧
        K.final (K.run k (slice w a p))=true ∧ D.accepts (slice w p j) := by
  rw [gap,join_slice _ _ w a j haj hj]
  simp only [meet_accepts,start_accepts,and_assoc]

def reverseMachine (d : DFA α) : RegularDFA.Machine α where
  State:=Fin d.stateCount→Bool
  decEq:=RegularDFA.functionDecEq (FiniteRelation.finEnum d.stateCount)
  enumeration:=RegularDFA.functionEnum (FiniteRelation.finEnum d.stateCount)
  initial:=d.final
  step:=fun F c q=>F (d.step q c)
  final:=fun F=>F d.initial

theorem reverse_run (d : DFA α) (F : Fin d.stateCount→Bool) (w : Word α)
    (q : Fin d.stateCount) : (reverseMachine d).run F w q=F (d.run q w.reverse) := by
  induction w generalizing F q with
  | nil => rfl
  | cons c w ih =>
    change (reverseMachine d).run (fun s=>F (d.step s c)) w q=_
    rw [ih,List.reverse_cons,DFA.run_append]
    rfl

def reverse (d : DFA α) : DFA α := (reverseMachine d).toDFA

theorem reverse_accepts (d : DFA α) (w : Word α) :
    (reverse d).accepts w ↔ d.accepts w.reverse := by
  rw [reverse,RegularDFA.Machine.toDFA_correct]
  change (reverseMachine d).run d.final w d.initial=true ↔ _
  rw [reverse_run]
  rfl

end REWB.BoundaryRange.Automata
