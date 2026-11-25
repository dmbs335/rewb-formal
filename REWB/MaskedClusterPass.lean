import REWB.MaskedClusterSourceMatrix
import REWB.MaskedClusterPoint

/-! Exact zero-jump transitions and source-clipped singleton transitions.
    Both use the shared materialized range indices, with explicit
    nonreversed interval bounds. The zero-jump transition ignores source
    reporting windows; only an actual source jump is clipped.
-/
namespace REWB.MaskedCluster
open REWB.MaskedFiniteAction.Maps REWB.Spec
variable {α : Type}

def passContext (C E : DFA α) (ci : BoundaryApplication.Range.Index C)
    (ei : BoundaryApplication.Range.Index E) (I O : Nat) : ReplayResult C E :=
  let c:=BoundaryApplication.Range.query C ci I O
  let e:=BoundaryApplication.Range.query E ei I O
  ⟨(c.map,e.map),c.products+e.products,c.visits+e.visits,c.work+e.work⟩

theorem passContext_value (C E : DFA α) (w : Word α) (I O : Nat) (hI : I≤O) (hn : O≤w.length) :
    (passContext C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) I O).maps=
      (wordMap C (slice w I O),wordMap E (slice w I O)) := by
  simp only [passContext]
  rw [range_map C w I O hI hn,range_map E w I O hI hn]

theorem passContext_work (C E : DFA α) (w : Word α) (I O : Nat) (hI : I≤O) (hn : O≤w.length) :
    (passContext C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) I O).work≤
      C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+2 := by
  have hc:=BoundaryApplication.Range.query_work C w I O hI hn
  have he:=BoundaryApplication.Range.query_work E w I O hI hn
  simp only [passContext]
  omega

def readMaps (C E : DFA α) (maps : Replay C E) :
    MaskedClusterStage.State C.stateCount E.stateCount→MaskedClusterStage.State C.stateCount E.stateCount
  | .waiting => .waiting
  | .gap q => .gap (maps.1.get q)
  | .suffix q => .suffix (maps.2.get q)

theorem readMaps_word (C E : DFA α) (w : Word α) (input : MaskedClusterStage.State C.stateCount E.stateCount) :
    readMaps C E (wordMap C w,wordMap E w) input=MaskedClusterStage.read C E w input := by
  cases input <;> simp only [readMaps,wordMap_get,MaskedClusterStage.read]

def passCell (C E : DFA α) (maps : Replay C E)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : MaskedProgression.Answer :=
  ⟨decide (readMaps C E maps input=output),0,3⟩

theorem passCell_correct (C E : DFA α) (w : Word α) (I O : Nat)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) (hI : I≤O) (hn : O≤w.length) :
    (passCell C E (passContext C E (BoundaryApplication.Range.build C w)
      (BoundaryApplication.Range.build E w) I O).maps input output).answer=true ↔
      MaskedClusterStage.read C E (slice w I O) input=output := by
  rw [passContext_value C E w I O hI hn]
  simp only [passCell,readMaps_word,decide_eq_true_eq]

def filteredPointCell (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (source target : Array Bool) (p : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : MaskedProgression.Answer :=
  ⟨decide (point C E maps tail
    (window.allows p && MaskedProgression.readMask source p)
    (MaskedProgression.readMask target p) input=some output),2,14⟩

theorem point_actual (C E : DFA α) (w : Word α) (anchor I p L H O : Nat)
    (source target : Bool) (input : MaskedClusterStage.State C.stateCount E.stateCount)
    (hI : I≤p) (hLH : L≤H) (hO : p+H≤O) (hn : O≤w.length) (hanchor : anchor+H≤w.length)
    (hcopy : slice w anchor (anchor+H)=slice w p (p+H)) :
    point C E
      (pointContexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        I p H O).maps
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        anchor L H).maps source target input=
      MaskedClusterStage.direct C E w I p L O source target input := by
  rw [pointContexts_value C E w I p H O hI hO hn,replay_value C E w anchor L H hLH hanchor,point_words]
  have hr : MaskedClusterStage.read C E
      (slice w (anchor+L) (anchor+H)++slice w (p+H) O)=
      fun t=>MaskedClusterStage.read C E (slice w (p+H) O)
        (MaskedClusterStage.read C E (slice w (anchor+L) (anchor+H)) t) := by
    funext t
    exact MaskedClusterStage.read_append C E _ _ t
  rw [hr]
  exact MaskedClusterStage.anchored_exact C E w anchor I p L H O source target input hLH hO hcopy

theorem filteredPointCell_direct (C E : DFA α) (w : Word α) (anchor I p L H O : Nat)
    (source target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hI : I≤p) (hLH : L≤H) (hO : p+H≤O) (hn : O≤w.length) (hanchor : anchor+H≤w.length)
    (hcopy : slice w anchor (anchor+H)=slice w p (p+H)) :
    (filteredPointCell C E
      (pointContexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        I p H O).maps
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        anchor L H).maps source target p window input output).answer=true ↔
      MaskedClusterStage.direct C E w I p L O
        (window.allows p && MaskedProgression.readMask source p)
        (MaskedProgression.readMask target p) input=some output := by
  simp only [filteredPointCell,decide_eq_true_eq]
  rw [point_actual C E w anchor I p L H O _ _ input hI hLH hO hn hanchor hcopy]

def either (a b : MaskedProgression.Answer) : MaskedProgression.Answer :=
  ⟨a.answer || b.answer,a.slots+b.slots,a.arithmetic+b.arithmetic+1⟩

theorem either_answer (a b : MaskedProgression.Answer) :
    (either a b).answer=true ↔ a.answer=true ∨ b.answer=true := by
  simp only [either,Bool.or_eq_true]

end REWB.MaskedCluster
