import REWB.MaskedAllStartFullCostInitialScan
import REWB.PeriodicConstructionPattern

/-! Actual measured periodic batch construction and its generated-run
budget. The run enumerator and source scan are executed once. The local
cut-index products are refined separately by the finite primitive layer. -/
namespace REWB.MaskedAllStart.FullCost.Initial
open REWB.MaskedPeriodic REWB.MaskedPeriodic.Batch REWB.PeriodicConstruction
open REWB.MaskedCut REWB.MaskedCut.DFAIndex
variable {α : Type} {σ : Nat}

def runs (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (n : Nat) (source target : Array Bool) :
    List RunGeometry.Bounds→Batch.State→Result Batch.State
  | [],out=>(out,1)
  | R::Rs,out=>
    let ⟨next,work⟩:=one B C E prepared idx n source target R out
    let ⟨last,rest⟩:=runs B C E prepared idx n source target Rs next
    (last,work+rest+4)

theorem runs_value (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (n : Nat) (source target : Array Bool)
    (Rs : List RunGeometry.Bounds) (out : Batch.State) :
    (runs B C E prepared idx n source target Rs out).1=
      Batch.runs B C E prepared idx n source target Rs out := by
  induction Rs generalizing out with
  | nil=>rfl
  | cons R Rs ih=>simp only [runs,ih,one_value,Batch.runs]

theorem runs_work (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (w : Word α) (source target : Array Bool) (Rs : List RunGeometry.Bounds)
    (hn : ∀R,R∈Rs→R.hi≤w.length) (out : Batch.State) :
    (runs B C E prepared (DFAIndex.build B C E w).1 w.length source target Rs out).2≤
      (oneLimit B C E prepared.K w.length+4)*totalSpan Rs+1 := by
  induction Rs generalizing out with
  | nil=>simp only [runs,totalSpan,Nat.mul_zero,Nat.zero_add,Nat.le_refl]
  | cons R Rs ih=>
    have ho:=one_work B C E prepared w source target R (hn R List.mem_cons_self) out
    have ht:=ih (fun T hT=>hn T (List.mem_cons_of_mem R hT))
      (one B C E prepared (DFAIndex.build B C E w).1 w.length source target R out).1
    have hs : 1≤span R := Nat.succ_le_succ (Nat.zero_le _)
    have hc:=Nat.mul_le_mul_left 4 hs
    dsimp only [runs,totalSpan]
    simp only [Nat.mul_one,Nat.mul_add,Nat.add_mul] at ho ht hc ⊢
    omega

def periodic (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : Result Batch.Result :=
  let ⟨prepared,pwork⟩:=Pattern.preparePattern B.stateCount C.stateCount E.stateCount
  let ⟨idx,products⟩:=DFAIndex.build B C E text.toList
  let found:=MaskedOrdered.Owner.enumerateAuto text fallback
  let ⟨out,work⟩:=runs B C E prepared idx text.size source target found.runs
    {hits:=Array.replicate (text.size+1) false,preparationWork:=text.size+1}
  (⟨out,found.work,products⟩,pwork+work+found.work+products+8*(text.size+1)+12)

theorem periodic_value (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (periodic B C E text fallback source target).1=Batch.solve B C E text fallback source target := by
  simp only [periodic,runs_value,Pattern.preparePattern_value,Batch.solve]

def periodicBudget (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  Pattern.patternCost B.stateCount C.stateCount E.stateCount+
    (oneLimit B C E (preparePattern B.stateCount C.stateCount E.stateCount).K n+4)*(6*n*(n.log2+1))+
    MaskedRunEnumerationCost.coefficient σ*(n+1)*((n+1).log2+1)^2+
    (n.log2+1)*n+8*(n+1)+13

theorem periodic_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (periodic B C E text fallback source target).2≤periodicBudget B C E text.size := by
  have hn : ∀R,R∈(MaskedOrdered.Owner.enumerateAuto text fallback).runs→R.hi≤text.toList.length := by
    intro R hR
    simpa only [Array.length_toList] using
      ((MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mp hR).1.2.1
  have hr:=runs_work B C E (preparePattern B.stateCount C.stateCount E.stateCount)
    text.toList source target (MaskedOrdered.Owner.enumerateAuto text fallback).runs hn
    {hits:=Array.replicate (text.size+1) false,preparationWork:=text.size+1}
  have hs:=Nat.mul_le_mul_left
    (oneLimit B C E (preparePattern B.stateCount C.stateCount E.stateCount).K text.size+4)
    (Batch.enumerated_span text fallback)
  have he:=MaskedRunEnumerationCost.enumerate_work text fallback
  have hi:=DFAIndex.build_products B C E text.toList
  simp only [Array.length_toList] at hr hi
  unfold periodic periodicBudget
  simp only [Pattern.preparePattern_value,Pattern.preparePattern_work,hi]
  omega

end REWB.MaskedAllStart.FullCost.Initial
