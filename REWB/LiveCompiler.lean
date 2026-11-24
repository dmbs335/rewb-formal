import REWB.LiveLanguage

/-! A regular-expression compiler over the extended alphabet of characters
    and retained control markers. It eliminates dead capture events while
    retaining every choice in the source expression, including repetitions.
    DFA construction and extraction of regular factor languages are later
    steps; this module produces an ordinary finite regular syntax. -/
namespace REWB
variable {α : Type}

abbrev MarkedSymbol (α : Type) := Sum α Control

namespace Plan

def code : Plan α → Word (MarkedSymbol α)
  | .nil => []
  | .literal w => w.map Sum.inl
  | .recall => [.inr .recall]
  | .seq p q => p.code++q.code
  | .cap p => [.inr .openCap]++p.code++[.inr .closeCap]

end Plan

namespace LiveCompiler
open LiveLanguage (join Star Walk shape)

inductive Reg (α : Type) where
  | empty
  | epsilon
  | atom : DFA α → Reg α
  | mark : Control → Reg α
  | alt : Reg α → Reg α → Reg α
  | seq : Reg α → Reg α → Reg α
  | star : Reg α → Reg α

def denote : Reg α → Language (MarkedSymbol α)
  | .empty => fun _=>False
  | .epsilon => fun w=>w=[]
  | .atom d => fun w=>∃ u, d.accepts u ∧ w=u.map Sum.inl
  | .mark c => fun w=>w=[.inr c]
  | .alt r s => fun w=>denote r w ∨ denote s w
  | .seq r s => join (denote r) (denote s)
  | .star r => Star (denote r)

private theorem join3 (A B C : Language (MarkedSymbol α)) (w : Word (MarkedSymbol α)) :
    join (join A B) C w ↔
      ∃ x y z,w=x++y++z ∧ A x ∧ B y ∧ C z := by
  constructor
  · rintro ⟨u,z,rfl,⟨x,y,rfl,hx,hy⟩,hz⟩
    exact ⟨x,y,z,rfl,hx,hy,hz⟩
  · rintro ⟨x,y,z,rfl,hx,hy,hz⟩
    exact ⟨x++y,z,rfl,⟨x,y,rfl,hx,hy⟩,hz⟩

private theorem join5 (A B C D E : Language (MarkedSymbol α)) (w : Word (MarkedSymbol α)) :
    join (join (join (join A B) C) D) E w ↔
      ∃ a b c d e,w=a++b++c++d++e ∧ A a ∧ B b ∧ C c ∧ D d ∧ E e := by
  constructor
  · rintro ⟨u,e,rfl,⟨v,d,rfl,⟨x,c,rfl,⟨a,b,rfl,ha,hb⟩,hc⟩,hd⟩,he⟩
    exact ⟨a,b,c,d,e,rfl,ha,hb,hc,hd,he⟩
  · rintro ⟨a,b,c,d,e,rfl,ha,hb,hc,hd,he⟩
    exact ⟨a++b++c++d,e,rfl,⟨a++b++c,d,rfl,⟨a++b,c,rfl,
      ⟨a,b,rfl,ha,hb⟩,hc⟩,hd⟩,he⟩

theorem lang_ext (A B : Language (MarkedSymbol α)) (h : ∀ w,A w↔B w) : A=B := by
  funext w
  exact propext (h w)

def oneLoop (R : Bool→Bool→Reg α) : Reg α := .star (R true true)

def zeroLoop (R : Bool→Bool→Reg α) : Reg α :=
  .star (.alt (R false false) (.seq (.seq (R false true) (oneLoop R)) (R true false)))

theorem zeroLoop_denote (R : Bool→Bool→Reg α) :
    denote (zeroLoop R)=LiveLanguage.loopZero (fun a b=>denote (R a b)) := by
  unfold zeroLoop LiveLanguage.loopZero
  change Star (fun w=>denote (R false false) w ∨
    join (join (denote (R false true)) (Star (denote (R true true)))) (denote (R true false)) w)=_
  have h : (fun w=>denote (R false false) w ∨
      join (join (denote (R false true)) (Star (denote (R true true)))) (denote (R true false)) w) =
      (fun w=>denote (R false false) w ∨
        LiveLanguage.excursion (fun a b=>denote (R a b)) w) := by
    apply lang_ext
    intro w
    rw [join3]
    rfl
  rw [h]

def pathReg (R : Bool→Bool→Reg α) : Bool→Bool→Reg α
  | false,false => zeroLoop R
  | false,true => .seq (.seq (zeroLoop R) (R false true)) (oneLoop R)
  | true,false => .seq (.seq (oneLoop R) (R true false)) (zeroLoop R)
  | true,true => .alt (oneLoop R)
      (.seq (.seq (.seq (.seq (oneLoop R) (R true false)) (zeroLoop R))
        (R false true)) (oneLoop R))

theorem pathReg_correct (R : Bool→Bool→Reg α) (a b : Bool) (w : Word (MarkedSymbol α)) :
    denote (pathReg R a b) w ↔ Walk (fun x y=>denote (R x y)) a b w := by
  rw [← LiveLanguage.shape_iff_walk]
  cases a <;> cases b
  · exact congrFun (zeroLoop_denote R) w |> Iff.of_eq
  · change join (join (denote (zeroLoop R)) (denote (R false true)))
      (denote (oneLoop R)) w↔_
    rw [zeroLoop_denote,join3]
    rfl
  · change join (join (denote (oneLoop R)) (denote (R true false)))
      (denote (zeroLoop R)) w↔_
    rw [zeroLoop_denote,join3]
    rfl
  · change (denote (oneLoop R) w ∨
      join (join (join (join (denote (oneLoop R)) (denote (R true false)))
        (denote (zeroLoop R))) (denote (R false true))) (denote (oneLoop R)) w)↔_
    rw [zeroLoop_denote,join5]
    rfl

/-- Exact language of pruned derivations, indexed by both liveness flags. -/
def PrunedWord (p : Expr α) (a b : Bool) : Language (MarkedSymbol α) :=
  fun w=>∃ x, PlanOf p x ∧ (x.prune b).1=a ∧ (x.prune b).2.code=w

theorem atom_word (d : DFA α) (a b : Bool) (w : Word (MarkedSymbol α)) :
    PrunedWord (.atom d) a b w ↔ a=b ∧ denote (.atom d) w := by
  constructor
  · rintro ⟨x,hx,ha,hw⟩
    cases hx with
    | atom d u hu =>
      exact ⟨ha.symm,u,hu,hw.symm⟩
  · rintro ⟨rfl,u,hu,rfl⟩
    exact ⟨.literal u,.atom d u hu,rfl,rfl⟩

theorem ref_word (a b : Bool) (w : Word (MarkedSymbol α)) :
    PrunedWord (.reference : Expr α) a b w ↔ a=true ∧ w=[.inr .recall] := by
  constructor
  · rintro ⟨x,hx,ha,hw⟩
    cases hx
    exact ⟨ha.symm,hw.symm⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨.recall,.reference,rfl,rfl⟩

theorem seq_word (p q : Expr α) (a b : Bool) (w : Word (MarkedSymbol α)) :
    PrunedWord (p ⋙ q) a b w ↔
      ∃ mid u v,w=u++v ∧ PrunedWord p a mid u ∧ PrunedWord q mid b v := by
  constructor
  · rintro ⟨x,hx,ha,hw⟩
    cases hx with
    | @seq p q u v hu hv =>
      exact ⟨(v.prune b).1,(u.prune (v.prune b).1).2.code,(v.prune b).2.code,
        hw.symm,⟨u,hu,ha,rfl⟩,⟨v,hv,rfl,rfl⟩⟩
  · rintro ⟨mid,u,v,rfl,⟨x,hx,hxa,hxu⟩,⟨y,hy,hym,hyv⟩⟩
    refine ⟨.seq x y,.seq hx hy,?_,?_⟩
    · simpa only [Plan.prune,hym] using hxa
    · simp only [Plan.prune,Plan.code,hym,hxu,hyv]

theorem alt_word (p q : Expr α) (a b : Bool) (w : Word (MarkedSymbol α)) :
    PrunedWord (.alt p q) a b w ↔ PrunedWord p a b w ∨ PrunedWord q a b w := by
  constructor
  · rintro ⟨x,hx,ha,hw⟩
    cases hx with
    | altLeft h => exact Or.inl ⟨x,h,ha,hw⟩
    | altRight h => exact Or.inr ⟨x,h,ha,hw⟩
  · rintro (⟨x,hx,ha,hw⟩|⟨x,hx,ha,hw⟩)
    · exact ⟨x,.altLeft hx,ha,hw⟩
    · exact ⟨x,.altRight hx,ha,hw⟩

theorem cap_word (p : Expr α) (a b : Bool) (w : Word (MarkedSymbol α)) :
    PrunedWord (.capture p) a b w ↔
      if b then ∃ v,PrunedWord p a false v ∧ w=[.inr .openCap]++v++[.inr .closeCap]
      else PrunedWord p a false w := by
  cases b
  · constructor
    · rintro ⟨x,hx,ha,hw⟩
      cases hx with
      | @capture p u hu => exact ⟨u,hu,ha,hw⟩
    · rintro ⟨x,hx,ha,hw⟩
      exact ⟨.cap x,.capture hx,ha,hw⟩
  · constructor
    · rintro ⟨x,hx,ha,hw⟩
      cases hx with
      | @capture p u hu => exact ⟨(u.prune false).2.code,⟨u,hu,ha,rfl⟩,hw.symm⟩
    · rintro ⟨v,⟨x,hx,ha,hw⟩,rfl⟩
      exact ⟨.cap x,.capture hx,ha,by simp only [Plan.prune,if_true,Plan.code,hw]⟩

theorem star_plan_walk (p : Expr α) (x : Plan α) (h : PlanOf (.star p) x)
    (b : Bool) :
    Walk (PrunedWord p) (x.prune b).1 b (x.prune b).2.code := by
  induction x generalizing b with
  | nil =>
    exact Walk.nil b
  | literal u => cases h
  | recall => cases h
  | cap x ih => cases h
  | seq u v ihu ihv =>
    cases h with
    | starCons hu hv =>
      exact Walk.cons ⟨u,hu,rfl,rfl⟩ (ihv hv b)

theorem star_word (p : Expr α) (a b : Bool) (w : Word (MarkedSymbol α)) :
    PrunedWord (.star p) a b w ↔ Walk (PrunedWord p) a b w := by
  constructor
  · rintro ⟨x,hx,ha,hw⟩
    have hh := star_plan_walk p x hx b
    rwa [ha,hw] at hh
  · intro h
    induction h with
    | nil q => exact ⟨.nil,.starNil p,rfl,rfl⟩
    | cons hu hv ih =>
      obtain ⟨x,hx,hxa,hxu⟩ := hu
      obtain ⟨y,hy,hym,hyv⟩ := ih
      refine ⟨.seq x y,.starCons hx hy,?_,?_⟩
      · simpa only [Plan.prune,hym] using hxa
      · simp only [Plan.prune,Plan.code,hym,hxu,hyv]

/-- Compile the finite source syntax into ordinary regular syntax.
    Both liveness flags are finite, and a star uses the closed two-state
    path expression instead of unfolding the repetition. -/
def compile : Expr α → Bool → Bool → Reg α
  | .atom d,a,b => if a=b then .atom d else .empty
  | .reference,a,_ => if a then .mark .recall else .empty
  | .seq p q,a,b => .alt (.seq (compile p a false) (compile q false b))
      (.seq (compile p a true) (compile q true b))
  | .alt p q,a,b => .alt (compile p a b) (compile q a b)
  | .capture p,a,b => if b then .seq (.seq (.mark .openCap) (compile p a false))
      (.mark .closeCap) else compile p a false
  | .star p,a,b => pathReg (compile p) a b

theorem compile_correct (p : Expr α) (a b : Bool) (w : Word (MarkedSymbol α)) :
    denote (compile p a b) w ↔ PrunedWord p a b w := by
  induction p generalizing a b w with
  | atom d =>
    rw [atom_word]
    by_cases h : a=b <;> simp [compile,h,denote]
  | reference =>
    rw [ref_word]
    cases a <;> simp [compile,denote]
  | seq p q hp hq =>
    rw [seq_word]
    change (join (denote (compile p a false)) (denote (compile q false b)) w ∨
      join (denote (compile p a true)) (denote (compile q true b)) w)↔_
    simp only [join,hp,hq]
    constructor
    · rintro (⟨u,v,he,hu,hv⟩|⟨u,v,he,hu,hv⟩)
      · exact ⟨false,u,v,he,hu,hv⟩
      · exact ⟨true,u,v,he,hu,hv⟩
    · rintro ⟨mid,u,v,he,hu,hv⟩
      cases mid
      · exact Or.inl ⟨u,v,he,hu,hv⟩
      · exact Or.inr ⟨u,v,he,hu,hv⟩
  | alt p q hp hq =>
    rw [alt_word]
    change (denote (compile p a b) w ∨ denote (compile q a b) w)↔_
    rw [hp,hq]
  | capture p hp =>
    rw [cap_word]
    cases b
    · exact hp a false w
    · change join (join (denote (.mark .openCap)) (denote (compile p a false)))
        (denote (.mark .closeCap)) w↔_
      rw [join3]
      simp only [denote,hp]
      constructor
      · rintro ⟨x,y,z,he,rfl,hy,rfl⟩
        exact ⟨y,hy,he⟩
      · rintro ⟨v,hv,he⟩
        exact ⟨_,v,_,he,rfl,hv,rfl⟩
  | star p hp =>
    rw [star_word]
    change denote (pathReg (compile p) a b) w↔_
    rw [pathReg_correct]
    have he : (fun a b=>denote (compile p a b))=PrunedWord p := by
      funext a b
      exact lang_ext _ _ (hp a b)
    rw [he]

/-- Union both possible incoming liveness flags, since the initial
    register is the empty word and the final register is unobserved. -/
def compiled (p : Expr α) : Reg α :=
  .alt (compile p false false) (compile p true false)

theorem compiled_correct (p : Expr α) (w : Word (MarkedSymbol α)) :
    denote (compiled p) w ↔ ∃ a, PrunedWord p a false w := by
  change (denote (compile p false false) w ∨ denote (compile p true false) w)↔_
  rw [compile_correct,compile_correct]
  constructor
  · rintro (h|h)
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  · rintro ⟨a,h⟩
    cases a
    · exact Or.inl h
    · exact Or.inr h

end LiveCompiler
end REWB
