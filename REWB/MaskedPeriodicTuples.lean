import REWB.MaskedPeriodicDFA

/-! Extract joint tuples from the actual shared cut index. Interior cuts
    lie in [1,q-1]; ending cuts lie in [1,eta]. The two empty cases are
    handled before querying. A tuple is never removed merely because it
    equals the zero-cut tuple: different cuts may induce identical maps.
-/
namespace REWB.MaskedPeriodic
open REWB.MaskedFiniteAction.Maps REWB.FiniteRelation
open REWB.MaskedCut REWB.MaskedCut.DFAIndex REWB.Spec
variable {α : Type}

def fullTuple (b c e : DFA α) (p s : Joint b c e) : Joint b c e :=
  (p.1,s.2.1,s.2.2)

def fullContains (b c e : DFA α) (table : MatrixTable.Matrix (jointEnum b c e))
    (target : Joint b c e) : Bool :=
  any (jointEnum b c e) fun p=>any (jointEnum b c e) fun s=>
    MatrixTable.denote table p s && decide (fullTuple b c e p s=target)

def fullTuples (b c e : DFA α) (answer : Option (MatrixTable.Matrix (jointEnum b c e))) :
    List (Joint b c e) :=
  (answer.map fun table=>(jointEnum b c e).elems.filter (fullContains b c e table)).getD []

theorem fullTuples_mem (b c e : DFA α) (answer : Option (MatrixTable.Matrix (jointEnum b c e)))
    (target : Joint b c e) :
    target∈fullTuples b c e answer ↔ ∃ p s,
      answer.map (fun table=>MatrixTable.denote table p s)=some true ∧
        fullTuple b c e p s=target := by
  cases answer with
  | none => simp [fullTuples]
  | some table =>
    simp only [fullTuples,Option.map,Option.getD_some,List.mem_filter,fullContains,
      any_true,Bool.and_eq_true,decide_eq_true_eq,Option.some.injEq]
    exact and_iff_right ((jointEnum b c e).complete target)

theorem fullTuples_size (b c e : DFA α) (answer : Option (MatrixTable.Matrix (jointEnum b c e))) :
    (fullTuples b c e answer).length≤(jointEnum b c e).elems.length := by
  cases answer with
  | none => exact Nat.zero_le _
  | some table => exact List.length_filter_le _ _

structure TupleResult (b c e : DFA α) where
  values : List (Joint b c e)
  products : Nat
  visits : Nat

def interiorTuples (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start q : Nat) : TupleResult b c e :=
  if 1<q then
    let result := Index.query (jointOps b c e) (jointEnum b c e) idx
      start (start+1) (start+q-1) (start+q)
    ⟨fullTuples b c e result.answer,result.products,result.visits⟩
  else ⟨[],0,0⟩

def endingTuples (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start eta q : Nat) : TupleResult b c e :=
  let result := queryConstrained b c e idx start 1 eta q
  ⟨(result.answer.map (fun out=>(out.tuples b c e).toList)).getD [],result.products,result.visits⟩

theorem interiorTuples_size (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start q : Nat) :
    (interiorTuples b c e idx start q).values.length≤(jointEnum b c e).elems.length := by
  unfold interiorTuples
  split
  · exact fullTuples_size _ _ _ _
  · exact Nat.zero_le _

theorem endingTuples_size (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start eta q : Nat) :
    (endingTuples b c e idx start eta q).values.length≤(jointEnum b c e).elems.length := by
  unfold endingTuples
  dsimp only
  cases h : (queryConstrained b c e idx start 1 eta q).answer with
  | none => simp only [Option.map,Option.getD_none,List.length_nil,Nat.zero_le]
  | some out =>
    simpa only [Option.map,Option.getD_some,Array.length_toList,jointEnum_length] using
      out.tuples_size b c e

theorem interiorTuples_correct (b c e : DFA α) (w : Word α) (start q : Nat)
    (hn : start+q≤w.length) (target : Joint b c e) :
    target∈(interiorTuples b c e (DFAIndex.build b c e w).1 start q).values ↔
      ∃ rho,0<rho ∧ rho<q ∧ wordTuple b c e
        (slice w start (start+rho)) (slice w (start+rho) (start+q))
        (slice w (start+rho) (start+q))=target := by
  by_cases hq : 1<q
  · simp only [interiorTuples,hq,if_true]
    rw [fullTuples_mem]
    have hc (p s : Joint b c e) := DFAIndex.query_correct b c e w
      start (start+1) (start+q-1) (start+q) p s (by omega) (by omega) (by omega) hn
    simp only [hc]
    constructor
    · rintro ⟨p,s,⟨i,hi,hj,hp,hs⟩,ht⟩
      subst p
      subst s
      have hsi : start≤i := by omega
      refine ⟨i-start,by omega,by omega,?_⟩
      simpa only [Nat.add_sub_of_le hsi,fullTuple,jointWord,wordTuple] using ht
    · rintro ⟨rho,hlo,hhi,ht⟩
      exact ⟨jointWord b c e (slice w start (start+rho)),
        jointWord b c e (slice w (start+rho) (start+q)),
        ⟨start+rho,by omega,by omega,rfl,rfl⟩,ht⟩
  · simp only [interiorTuples,hq,if_false,List.not_mem_nil,false_iff]
    rintro ⟨rho,hlo,hhi,_⟩
    omega

theorem endingTuples_correct (b c e : DFA α) (w : Word α) (start eta q : Nat)
    (he : eta≤q) (hn : start+q≤w.length) (target : Joint b c e) :
    target∈(endingTuples b c e (DFAIndex.build b c e w).1 start eta q).values ↔
      ∃ rho,0<rho ∧ rho≤eta ∧ wordTuple b c e
        (slice w start (start+rho)) (slice w (start+rho) (start+q))
        (slice w (start+rho) (start+eta))=target := by
  have hc := queryConstrained_correct b c e w start 1 eta q he hn target
  have hm : target∈(endingTuples b c e (DFAIndex.build b c e w).1 start eta q).values ↔
      (queryConstrained b c e (DFAIndex.build b c e w).1 start 1 eta q).answer.map
        (fun out=>out.contains b c e target)=some true := by
    unfold endingTuples
    dsimp only
    cases h : (queryConstrained b c e (DFAIndex.build b c e w).1 start 1 eta q).answer with
    | none => simp
    | some out => simp only [Option.map,Option.getD_some,Option.some.injEq,out.tuples_mem b c e]
  rw [hm,hc]
  rfl

theorem interiorTuples_bounds (b c e : DFA α) (w : Word α) (start q : Nat)
    (hn : start+q≤w.length) :
    (interiorTuples b c e (DFAIndex.build b c e w).1 start q).products≤3 ∧
    (interiorTuples b c e (DFAIndex.build b c e w).1 start q).visits≤4*(Nat.log2 w.length+2) := by
  by_cases hq : 1<q
  · have hh := Index.query_bounds (jointOps b c e) (jointEnum b c e) (letters b c e w)
      start (start+1) (start+q-1) (start+q) (by omega) (by omega) (by omega)
      (by simpa only [letters_length] using hn)
    simp only [letters_length] at hh
    simp only [interiorTuples,hq,if_true,DFAIndex.build]
    constructor
    · exact hh.1
    · omega
  · simp only [interiorTuples,hq,if_false,Nat.zero_le,and_self]

theorem endingTuples_bounds (b c e : DFA α) (w : Word α) (start eta q : Nat)
    (he : eta≤q) (hn : start+q≤w.length) :
    (endingTuples b c e (DFAIndex.build b c e w).1 start eta q).products≤4 ∧
    (endingTuples b c e (DFAIndex.build b c e w).1 start eta q).visits≤4*(Nat.log2 w.length+2) :=
  queryConstrained_bounds b c e w start 1 eta q he hn

end REWB.MaskedPeriodic
