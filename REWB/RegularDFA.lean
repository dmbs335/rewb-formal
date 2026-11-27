import REWB.MarkedFactors

/-! Constructive finite-automaton closure machinery for the regular
marked-code compiler. State sets are explicitly enumerated, and every
finite automaton is constructed directly from the regular syntax. -/
namespace REWB.RegularDFA
open REWB.FiniteRelation
open REWB.LiveLanguage (join Star)
variable {α S T : Type}

private theorem bool_ext (a b : Bool) (h : (a=true ↔ b=true)) : a=b := by
  cases a <;> cases b <;> simp_all

def prodEnum (e : Enumeration S) (f : Enumeration T) : Enumeration (S×T) :=
  ⟨e.elems.flatMap (fun x=>f.elems.map (x,·)),by
    rintro ⟨x,y⟩
    exact List.mem_flatMap.mpr ⟨x,e.complete x,
      List.mem_map.mpr ⟨y,f.complete y,rfl⟩⟩⟩

def boolEnum : Enumeration Bool := ⟨[false,true],by intro b; cases b <;> simp⟩

def optionEnum (e : Enumeration S) : Enumeration (Option S) :=
  ⟨none::e.elems.map some,by
    intro x
    cases x with
    | none => simp
    | some x => simp [e.complete x]⟩

def update [DecidableEq S] (f : S→Bool) (x : S) (b : Bool) : S→Bool :=
  fun y=>if y=x then b else f y

def functions [DecidableEq S] : List S→List (S→Bool)
  | [] => [fun _=>false]
  | x::xs => (functions xs).flatMap (fun f=>[update f x false,update f x true])

theorem functions_cover [DecidableEq S] (xs : List S) (f : S→Bool) :
    ∃ g∈functions xs,∀ x,x∈xs→g x=f x := by
  induction xs with
  | nil => exact ⟨fun _=>false,by simp [functions],by intro x hx; simp at hx⟩
  | cons x xs ih =>
    obtain ⟨g,hg,hgf⟩ := ih
    refine ⟨update g x (f x),?_,?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨g,hg,?_⟩
      cases f x <;> simp
    · intro y hy
      rcases List.mem_cons.mp hy with he|hy
      · subst y
        simp [update]
      · by_cases he : y=x
        · subst y
          simp [update]
        · simp [update,he,hgf y hy]

def functionEnum [DecidableEq S] (e : Enumeration S) : Enumeration (S→Bool) :=
  ⟨functions e.elems,by
    intro f
    obtain ⟨g,hg,hgf⟩ := functions_cover e.elems f
    have he : g=f := funext (fun x=>hgf x (e.complete x))
    rwa [← he]⟩

def functionDecEq (e : Enumeration S) : DecidableEq (S→Bool) := fun f g=>
  if h : e.elems.all (fun x=>decide (f x=g x))=true then
    isTrue (funext (fun x=>of_decide_eq_true
      (List.all_eq_true.mp h x (e.complete x))))
  else isFalse (by intro he; subst g; simp at h)

structure Machine (α : Type) where
  State : Type
  decEq : DecidableEq State
  enumeration : Enumeration State
  initial : State
  step : State→α→State
  final : State→Bool

attribute [instance] Machine.decEq

namespace Machine

def run (M : Machine α) : M.State→Word α→M.State
  | q,[] => q
  | q,c::cs => run M (M.step q c) cs

def accepts (M : Machine α) (w : Word α) : Prop := M.final (M.run M.initial w)=true

theorem run_append (M : Machine α) (q : M.State) (u v : Word α) :
    M.run q (u++v)=M.run (M.run q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih => exact ih (M.step q a)

private theorem get_idx [DecidableEq S] (xs : List S) (x : S) (h : x∈xs) :
    xs[xs.idxOf x]?=some x := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    by_cases he : x=a
    · subst x
      simp
    · have hx : x∈xs := (List.mem_cons.mp h).resolve_left he
      rw [List.idxOf_cons]
      simp only [cond_eq_if,beq_iff_eq,if_neg (Ne.symm he),List.getElem?_cons_succ]
      exact ih hx

def encode (M : Machine α) (q : M.State) : Fin M.enumeration.elems.length :=
  ⟨M.enumeration.elems.idxOf q,List.idxOf_lt_length (M.enumeration.complete q)⟩

def decode (M : Machine α) (q : Fin M.enumeration.elems.length) : M.State :=
  (M.enumeration.elems[q.val]?).getD M.initial

theorem decode_encode (M : Machine α) (q : M.State) : M.decode (M.encode q)=q := by
  unfold decode encode
  rw [get_idx _ _ (M.enumeration.complete q)]
  rfl

def toDFA (M : Machine α) : DFA α :=
  ⟨M.enumeration.elems.length,M.encode M.initial,
    (fun q a=>M.encode (M.step (M.decode q) a)),(fun q=>M.final (M.decode q))⟩

theorem toDFA_run (M : Machine α) (q : M.State) (w : Word α) :
    M.toDFA.run (M.encode q) w=M.encode (M.run q w) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
    change M.toDFA.run (M.encode (M.step (M.decode (M.encode q)) a)) w=_
    rw [decode_encode,ih]
    rfl

theorem toDFA_correct (M : Machine α) (w : Word α) :
    M.toDFA.accepts w ↔ M.accepts w := by
  change M.final (M.decode (M.toDFA.run (M.encode M.initial) w))=true ↔ _
  rw [toDFA_run,decode_encode]
  rfl

end Machine

def lift (d : DFA α) : Machine α :=
  ⟨Fin d.stateCount,inferInstance,finEnum d.stateCount,d.initial,d.step,d.final⟩

theorem lift_run (d : DFA α) (q : Fin d.stateCount) (w : Word α) :
    (lift d).run q w=d.run q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => exact ih (d.step q a)

theorem lift_correct (d : DFA α) (w : Word α) :
    (lift d).accepts w ↔ d.accepts w := by
  change d.final ((lift d).run d.initial w)=true ↔ _
  rw [lift_run]
  rfl

def alternate (A B : Machine α) : Machine α :=
  ⟨A.State×B.State,inferInstance,prodEnum A.enumeration B.enumeration,
    (A.initial,B.initial),(fun q a=>(A.step q.1 a,B.step q.2 a)),
    (fun q=>A.final q.1 || B.final q.2)⟩

theorem alternate_run (A B : Machine α) (a : A.State) (b : B.State) (w : Word α) :
    (alternate A B).run (a,b) w=(A.run a w,B.run b w) := by
  induction w generalizing a b with
  | nil => rfl
  | cons c w ih => exact ih (A.step a c) (B.step b c)

theorem alternate_correct (A B : Machine α) (w : Word α) :
    (alternate A B).accepts w ↔ A.accepts w ∨ B.accepts w := by
  change ((alternate A B).run (A.initial,B.initial) w |> fun q=>
    A.final q.1 || B.final q.2)=true ↔ _
  rw [alternate_run,Bool.or_eq_true]
  rfl

theorem snoc_cases (w : Word α) : w=[] ∨ ∃ v a,w=v++[a] := by
  induction w with
  | nil => exact Or.inl rfl
  | cons a w ih =>
    rcases ih with rfl|⟨v,b,rfl⟩
    · exact Or.inr ⟨[],a,rfl⟩
    · exact Or.inr ⟨a::v,b,rfl⟩

theorem snoc_induction {P : Word α→Prop} (h0 : P [])
    (hs : ∀ w a,P w→P (w++[a])) (w : Word α) : P w := by
  have h : ∀ v : Word α,P v.reverse := by
    intro v
    induction v with
    | nil => exact h0
    | cons a v ih => simpa using hs v.reverse a ih
  simpa using h w.reverse

def Split (L : Language α) (B : Machine α) (w : Word α) (q : B.State) : Prop :=
  ∃ u v,w=u++v ∧ L u ∧ B.run B.initial v=q

theorem split_nil (L : Language α) (B : Machine α) (q : B.State) :
    Split L B [] q ↔ L [] ∧ B.initial=q := by
  constructor
  · rintro ⟨u,v,he,hu,hv⟩
    have hh := List.nil_eq_append_iff.mp he
    rcases hh with ⟨rfl,rfl⟩
    exact ⟨hu,hv⟩
  · rintro ⟨hL,hq⟩
    exact ⟨[],[],rfl,hL,hq⟩

theorem split_snoc (L : Language α) (B : Machine α) (w : Word α)
    (c : α) (q : B.State) :
    Split L B (w++[c]) q ↔
      (∃ r,Split L B w r ∧ B.step r c=q) ∨ (L (w++[c]) ∧ B.initial=q) := by
  constructor
  · rintro ⟨u,v,he,hu,hv⟩
    rcases snoc_cases v with rfl|⟨t,a,rfl⟩
    · simp only [List.append_nil] at he
      subst u
      exact Or.inr ⟨hu,hv⟩
    · have hh : (u++t).concat a=w.concat c := by
        simpa only [List.concat_eq_append,List.append_assoc] using he.symm
      obtain ⟨hp,ha⟩ := List.of_concat_eq_concat hh
      subst a
      rw [Machine.run_append] at hv
      exact Or.inl ⟨B.run B.initial t,⟨u,t,hp.symm,hu,rfl⟩,hv⟩
  · rintro (⟨r,⟨u,v,he,hu,hv⟩,hr⟩|⟨hu,hq⟩)
    · refine ⟨u,v++[c],?_,hu,?_⟩
      · rw [he,List.append_assoc]
      · rw [Machine.run_append,hv]
        exact hr
    · exact ⟨w++[c],[],by simp,hu,hq⟩

def move (B : Machine α) (f : B.State→Bool) (a : α) : B.State→Bool :=
  fun r=>any B.enumeration (fun q=>f q && decide (B.step q a=r))

theorem move_true (B : Machine α) (f : B.State→Bool) (a : α) (r : B.State) :
    move B f a r=true ↔ ∃ q,f q=true ∧ B.step q a=r := by
  simp only [move,any_true,Bool.and_eq_true,decide_eq_true_eq]

def inject (B : Machine α) (b : Bool) : B.State→Bool :=
  fun q=>b && decide (B.initial=q)

theorem inject_true (B : Machine α) (b : Bool) (q : B.State) :
    inject B b q=true ↔ b=true ∧ B.initial=q := by
  simp only [inject,Bool.and_eq_true,decide_eq_true_eq]

def concatenate (A B : Machine α) : Machine α :=
  { State := A.State×(B.State→Bool)
    decEq := by
      letI := functionDecEq B.enumeration
      infer_instance
    enumeration := prodEnum A.enumeration (functionEnum B.enumeration)
    initial := (A.initial,inject B (A.final A.initial))
    step := fun s a=>
      let q := A.step s.1 a
      (q,fun r=>move B s.2 a r || inject B (A.final q) r)
    final := fun s=>any B.enumeration (fun q=>s.2 q && B.final q) }

theorem concatenate_run (A B : Machine α) (w : Word α) :
    let s := (concatenate A B).run (concatenate A B).initial w
    s.1=A.run A.initial w ∧
      ∀ q,s.2 q=true ↔ Split A.accepts B w q := by
  apply snoc_induction (P:=fun w=>
    let s := (concatenate A B).run (concatenate A B).initial w
    s.1=A.run A.initial w ∧ ∀ q,s.2 q=true ↔ Split A.accepts B w q)
  · refine ⟨rfl,?_⟩
    intro q
    change inject B (A.final A.initial) q=true ↔ _
    rw [inject_true,split_nil]
    rfl
  · intro w a ih
    rw [Machine.run_append]
    change A.step ((concatenate A B).run (concatenate A B).initial w).1 a=
      A.run A.initial (w++[a]) ∧ _
    refine ⟨?_,?_⟩
    · rw [ih.1,Machine.run_append]
      rfl
    · intro q
      change (move B ((concatenate A B).run (concatenate A B).initial w).2 a q ||
        inject B (A.final (A.step ((concatenate A B).run
          (concatenate A B).initial w).1 a)) q)=true ↔ _
      rw [Bool.or_eq_true,move_true,inject_true,ih.1,split_snoc]
      simp only [ih.2]
      simp only [Machine.accepts,Machine.run_append,Machine.run]

theorem concatenate_correct (A B : Machine α) (w : Word α) :
    (concatenate A B).accepts w ↔ join A.accepts B.accepts w := by
  change any B.enumeration (fun q=>
    ((concatenate A B).run (concatenate A B).initial w).2 q && B.final q)=true ↔ _
  rw [any_true]
  simp only [Bool.and_eq_true,(concatenate_run A B w).2,Split,join]
  constructor
  · rintro ⟨q,⟨u,v,he,hu,hv⟩,hf⟩
    exact ⟨u,v,he,hu,by change B.final (B.run B.initial v)=true; rwa [hv]⟩
  · rintro ⟨u,v,he,hu,hv⟩
    exact ⟨B.run B.initial v,⟨u,v,he,hu,rfl⟩,hv⟩

theorem star_append {L : Language α} {u v : Word α}
    (hu : Star L u) (hv : Star L v) : Star L (u++v) := by
  induction hu with
  | nil => exact hv
  | cons hx hy ih =>
    rw [List.append_assoc]
    exact Star.cons hx ih

theorem star_last {L : Language α} {w : Word α} (h : Star L w) (hn : w≠[]) :
    ∃ u v,w=u++v ∧ Star L u ∧ L v ∧ v≠[] := by
  revert hn
  induction h with
  | nil => intro hn; exact False.elim (hn rfl)
  | @cons u v hu hv ih =>
    intro hn
    cases v with
    | nil =>
      refine ⟨[],u,by simp,Star.nil,hu,?_⟩
      simpa using hn
    | cons a v =>
      obtain ⟨x,y,hv,hx,hy,hne⟩ := ih (by simp)
      refine ⟨u++x,y,?_,Star.cons hu hx,hy,hne⟩
      rw [hv,List.append_assoc]

theorem star_snoc (A : Machine α) (w : Word α) (a : α) :
    Star A.accepts (w++[a]) ↔
      ∃ q,Split (Star A.accepts) A w q ∧ A.final (A.step q a)=true := by
  constructor
  · intro h
    obtain ⟨u,v,he,hu,hv,hn⟩ := star_last h (by simp)
    rcases snoc_cases v with hnil|⟨t,b,rfl⟩
    · exact False.elim (hn hnil)
    · have hh : (u++t).concat b=w.concat a := by
        simpa only [List.concat_eq_append,List.append_assoc] using he.symm
      obtain ⟨hp,hb⟩ := List.of_concat_eq_concat hh
      subst b
      refine ⟨A.run A.initial t,⟨u,t,hp.symm,hu,rfl⟩,?_⟩
      simpa only [Machine.accepts,Machine.run_append,Machine.run] using hv
  · rintro ⟨q,⟨u,v,he,hu,hv⟩,ha⟩
    have hacc : A.accepts (v++[a]) := by
      change A.final (A.run A.initial (v++[a]))=true
      rw [Machine.run_append,hv]
      exact ha
    have hs := star_append hu (Star.cons hacc Star.nil)
    simpa only [he,List.append_nil,List.append_assoc] using hs

def starred (A : Machine α) : Machine α :=
  { State := Bool×(A.State→Bool)
    decEq := by
      letI := functionDecEq A.enumeration
      infer_instance
    enumeration := prodEnum boolEnum (functionEnum A.enumeration)
    initial := (true,inject A true)
    step := fun s a=>
      let g := move A s.2 a
      let b := any A.enumeration (fun q=>g q && A.final q)
      (b,fun q=>g q || inject A b q)
    final := Prod.fst }

theorem starred_run (A : Machine α) (w : Word α) :
    let s := (starred A).run (starred A).initial w
    (s.1=true ↔ Star A.accepts w) ∧
      ∀ q,s.2 q=true ↔ Split (Star A.accepts) A w q := by
  apply snoc_induction (P:=fun w=>
    let s := (starred A).run (starred A).initial w
    (s.1=true ↔ Star A.accepts w) ∧
      ∀ q,s.2 q=true ↔ Split (Star A.accepts) A w q)
  · refine ⟨⟨fun _=>Star.nil,fun _=>rfl⟩,?_⟩
    intro q
    change inject A true q=true ↔ _
    rw [inject_true,split_nil]
    exact ⟨fun h=>⟨Star.nil,h.2⟩,fun h=>⟨rfl,h.2⟩⟩
  · intro w a ih
    let f := ((starred A).run (starred A).initial w).2
    let g := move A f a
    let b := any A.enumeration (fun q=>g q && A.final q)
    have hb : b=true ↔ Star A.accepts (w++[a]) := by
      rw [star_snoc]
      change any A.enumeration (fun q=>move A f a q && A.final q)=true ↔ _
      simp only [any_true,Bool.and_eq_true,move_true]
      constructor
      · rintro ⟨q,⟨r,hr,hq⟩,hf⟩
        refine ⟨r,(ih.2 r).mp hr,?_⟩
        rwa [hq]
      · rintro ⟨r,hr,hf⟩
        exact ⟨A.step r a,⟨r,(ih.2 r).mpr hr,rfl⟩,hf⟩
    rw [Machine.run_append]
    change (b=true ↔ Star A.accepts (w++[a])) ∧
      ∀ q,(g q || inject A b q)=true ↔ Split (Star A.accepts) A (w++[a]) q
    refine ⟨hb,?_⟩
    intro q
    rw [Bool.or_eq_true,inject_true,hb,split_snoc]
    change (move A f a q=true ∨ _) ↔ _
    rw [move_true]
    simp only [f,ih.2]

theorem starred_correct (A : Machine α) (w : Word α) :
    (starred A).accepts w ↔ Star A.accepts w := (starred_run A w).1

def empty : Machine α :=
  ⟨Unit,inferInstance,⟨[()],by intro q; cases q; simp⟩,(),
    (fun _ _=>()),(fun _=>false)⟩

theorem empty_correct (w : Word α) : (empty : Machine α).accepts w ↔ False := by
  simp [Machine.accepts,empty]

def epsilon : Machine α :=
  ⟨Bool,inferInstance,boolEnum,true,(fun _ _=>false),id⟩

theorem epsilon_false (w : Word α) : (epsilon : Machine α).run false w=false := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ih

theorem epsilon_correct (w : Word α) : (epsilon : Machine α).accepts w ↔ w=[] := by
  cases w with
  | nil => simp [Machine.accepts,Machine.run,epsilon]
  | cons a w =>
    change (epsilon : Machine α).run false w=true ↔ _
    rw [epsilon_false]
    simp

def atom (d : DFA α) : Machine (MarkedSymbol α) :=
  { State := Option (Fin d.stateCount)
    decEq := inferInstance
    enumeration := optionEnum (finEnum d.stateCount)
    initial := some d.initial
    step := fun q a=>match q,a with
      | some q,.inl a => some (d.step q a)
      | _,_ => none
    final := fun q=>match q with
      | none => false
      | some q => d.final q }

theorem atom_none (d : DFA α) (z : Word (MarkedSymbol α)) :
    (atom d).run none z=none := by
  induction z with
  | nil => rfl
  | cons a z ih => cases a <;> exact ih

theorem atom_from (d : DFA α) (q : Fin d.stateCount) (z : Word (MarkedSymbol α)) :
    (atom d).final ((atom d).run (some q) z)=true ↔
      ∃ w,z=w.map Sum.inl ∧ d.final (d.run q w)=true := by
  induction z generalizing q with
  | nil =>
    constructor
    · intro h
      exact ⟨[],rfl,h⟩
    · rintro ⟨w,hw,hq⟩
      have hlen : w.length=0 := by simpa using (congrArg List.length hw).symm
      have he : w=[] := List.length_eq_zero_iff.mp hlen
      subst w
      exact hq
  | cons x z ih =>
    cases x with
    | inl a =>
      change (atom d).final ((atom d).run (some (d.step q a)) z)=true ↔ _
      rw [ih]
      constructor
      · rintro ⟨w,he,hw⟩
        exact ⟨a::w,by rw [he]; rfl,hw⟩
      · rintro ⟨w,he,hw⟩
        cases w with
        | nil => simp at he
        | cons b w =>
          have hh : a=b ∧ z=w.map Sum.inl := by simpa using he
          rcases hh with ⟨rfl,hz⟩
          exact ⟨w,hz,hw⟩
    | inr c =>
      change (atom d).final ((atom d).run none z)=true ↔ _
      rw [atom_none]
      constructor
      · intro h
        contradiction
      · rintro ⟨w,he,_⟩
        cases w <;> simp at he

theorem atom_correct (d : DFA α) (z : Word (MarkedSymbol α)) :
    (atom d).accepts z ↔ LiveCompiler.denote (.atom d) z := by
  change (atom d).final ((atom d).run (some d.initial) z)=true ↔ _
  rw [atom_from]
  constructor
  · rintro ⟨w,he,hw⟩
    exact ⟨w,hw,he⟩
  · rintro ⟨w,hw,he⟩
    exact ⟨w,he,hw⟩

inductive TokenState where
  | start | matched | dead
  deriving Repr, DecidableEq

def tokenEnum : Enumeration TokenState :=
  ⟨[.start,.matched,.dead],by intro q; cases q <;> simp⟩

def marker (c : Control) : Machine (MarkedSymbol α) :=
  { State := TokenState
    decEq := inferInstance
    enumeration := tokenEnum
    initial := .start
    step := fun q x=>match q,x with
      | .start,.inr c' => if c'=c then .matched else .dead
      | _,_ => .dead
    final := fun q=>match q with
      | .matched => true
      | _ => false }

theorem marker_dead (c : Control) (z : Word (MarkedSymbol α)) :
    (marker c).run .dead z=.dead := by
  induction z with
  | nil => rfl
  | cons x z ih => cases x <;> exact ih

theorem marker_matched (c : Control) (z : Word (MarkedSymbol α)) :
    (marker c).final ((marker c).run .matched z)=true ↔ z=[] := by
  cases z with
  | nil => simp [Machine.run,marker]
  | cons x z =>
    cases x <;> change (marker c).final ((marker c).run .dead z)=true ↔ _
    all_goals rw [marker_dead]; simp [marker]

theorem marker_correct (c : Control) (z : Word (MarkedSymbol α)) :
    (marker c).accepts z ↔ z=[.inr c] := by
  cases z with
  | nil => simp [Machine.accepts,Machine.run,marker]
  | cons x z =>
    cases x with
    | inl a =>
      change (marker c).final ((marker c).run .dead z)=true ↔ _
      rw [marker_dead]
      simp [marker]
    | inr c' =>
      change (marker c).final ((marker c).run (if c'=c then .matched else .dead) z)=true ↔ _
      by_cases he : c'=c
      · subst c'
        rw [if_pos rfl,marker_matched]
        simp
      · rw [if_neg he,marker_dead]
        simp [marker,he]

/-- A concrete finite machine for every regular marked-code syntax node.
    Concatenation and star use explicit finite subsets of component
    states; they never enumerate input words or their factors. -/
def compile : LiveCompiler.Reg α → Machine (MarkedSymbol α)
  | .empty => empty
  | .epsilon => epsilon
  | .atom d => atom d
  | .mark c => marker c
  | .alt r s => alternate (compile r) (compile s)
  | .seq r s => concatenate (compile r) (compile s)
  | .star r => starred (compile r)

theorem compile_correct (r : LiveCompiler.Reg α) (z : Word (MarkedSymbol α)) :
    (compile r).accepts z ↔ LiveCompiler.denote r z := by
  induction r generalizing z with
  | empty => exact empty_correct z
  | epsilon => exact epsilon_correct z
  | atom d => exact atom_correct d z
  | mark c => exact marker_correct c z
  | alt r s hr hs =>
    rw [compile,alternate_correct,hr,hs]
    rfl
  | seq r s hr hs =>
    rw [compile,concatenate_correct]
    change join _ _ z ↔ join _ _ z
    simp only [join,hr,hs]
  | star r hr =>
    rw [compile,starred_correct]
    have he : (compile r).accepts=LiveCompiler.denote r :=
      funext (fun z=>propext (hr z))
    rw [he]
    rfl

/-- Executable `Fin`-state DFA, in the exact representation used by all
    existing normal-form and periodic modules. -/
def compileDFA (r : LiveCompiler.Reg α) : DFA (MarkedSymbol α) :=
  (compile r).toDFA

theorem compileDFA_correct (r : LiveCompiler.Reg α) (z : Word (MarkedSymbol α)) :
    (compileDFA r).accepts z ↔ LiveCompiler.denote r z := by
  rw [compileDFA,Machine.toDFA_correct,compile_correct]

def sourceDFA (p : Expr α) : DFA (MarkedSymbol α) :=
  compileDFA (LiveCompiler.compiled p)

/-- End-to-end finite DFA factor extraction from an arbitrary REWB
    source expression, with no supplied-DFA premise. The remaining
    interpreter has one of the ten already classified control words. -/
theorem source_factorization (p : Expr α) (w : Word α) :
    MatchesWithin p w 2 ↔
      ∃ s : ControlShapes.Shape,
      ∃ ds∈MarkedFactors.families (sourceDFA p) (sourceDFA p).initial s.controls,
      ∃ ws z,MarkedFactors.Interleaves s.controls ws z ∧
        MarkedFactors.acceptsFactors ds ws ∧ LiveCompiler.CodeMatches z w 2 := by
  rw [ControlShapes.matches_iff_shaped_codes]
  constructor
  · rintro ⟨s,z,hz,hsk,hm⟩
    have ha : (sourceDFA p).accepts z :=
      (compileDFA_correct (LiveCompiler.compiled p) z).mpr hz
    obtain ⟨ds,hds,ws,hw,hacc⟩ :=
      (MarkedFactors.factorization (sourceDFA p) s.controls z).mp ⟨ha,hsk⟩
    exact ⟨s,ds,hds,ws,z,hw,hacc,hm⟩
  · rintro ⟨s,ds,hds,ws,z,hw,hacc,hm⟩
    obtain ⟨ha,hsk⟩ :=
      (MarkedFactors.factorization (sourceDFA p) s.controls z).mpr ⟨ds,hds,ws,hw,hacc⟩
    exact ⟨s,z,(compileDFA_correct (LiveCompiler.compiled p) z).mp ha,hsk,hm⟩

end REWB.RegularDFA
