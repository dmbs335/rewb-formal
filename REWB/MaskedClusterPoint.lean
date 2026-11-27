import REWB.MaskedClusterMatrix

/-! Singleton clusters use a direct constant-point transfer. No
    periodicity, stepped-prefix array, or cycle decomposition is needed.
    The shared actual range indices supply its before/after maps, and
    the two masks are read directly at the one immutable text position.
-/
namespace REWB.MaskedCluster
open REWB.MaskedFiniteAction.Maps REWB.Spec
variable {α : Type}

def pointContexts (C E : DFA α) (ci : BoundaryApplication.Range.Index C)
    (ei : BoundaryApplication.Range.Index E) (I p H O : Nat) : ContextResult C E :=
  let a := BoundaryApplication.Range.query C ci I p
  let c := BoundaryApplication.Range.query C ci (p+H) O
  let e := BoundaryApplication.Range.query E ei (p+H) O
  ⟨⟨a.map,identity _,identity _,identity _,c.map,e.map⟩,
    a.products+c.products+e.products,a.visits+c.visits+e.visits,a.work+c.work+e.work+2⟩

theorem pointContexts_value (C E : DFA α) (w : Word α) (I p H O : Nat)
    (hI : I≤p) (hO : p+H≤O) (hn : O≤w.length) :
    (pointContexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      I p H O).maps=wordContext C E (slice w I p) [] [] (slice w (p+H) O) := by
  simp only [pointContexts,wordContext]
  rw [range_map C w I p hI (by omega),range_map C w (p+H) O hO hn,
    range_map E w (p+H) O hO hn]
  rfl

theorem pointContexts_bounds (C E : DFA α) (w : Word α) (I p H O : Nat)
    (hI : I≤p) (hO : p+H≤O) (hn : O≤w.length) :
    (pointContexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      I p H O).products≤3 ∧
    (pointContexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      I p H O).visits≤3*(Nat.log2 w.length+2) ∧
    (pointContexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      I p H O).work≤2*C.stateCount+E.stateCount+24*(Nat.log2 w.length+2)+5 := by
  have ha:=BoundaryApplication.Range.query_bounds C w I p hI (by omega)
  have hc:=BoundaryApplication.Range.query_bounds C w (p+H) O hO hn
  have he:=BoundaryApplication.Range.query_bounds E w (p+H) O hO hn
  have ha':=BoundaryApplication.Range.query_work C w I p hI (by omega)
  have hc':=BoundaryApplication.Range.query_work C w (p+H) O hO hn
  have he':=BoundaryApplication.Range.query_work E w (p+H) O hO hn
  simp only [pointContexts]
  constructor
  · omega
  · constructor <;> omega

def point (C E : DFA α) (maps : Context C E) (tail : Replay C E) (source target : Bool) :
    MaskedClusterStage.State C.stateCount E.stateCount→Option (MaskedClusterStage.State C.stateCount E.stateCount)
  | .waiting => if source then some (.gap (maps.afterC.get (tail.1.get C.initial))) else none
  | .gap input => if target && C.final (maps.before.get input) then
      some (.suffix (maps.afterE.get (tail.2.get E.initial))) else none
  | .suffix _ => none

theorem point_words (C E : DFA α) (pref Y after : Word α) (source target : Bool)
    (input : MaskedClusterStage.State C.stateCount E.stateCount) :
    point C E (wordContext C E pref [] [] after) (wordMap C Y,wordMap E Y) source target input=
      (MaskedClusterStage.jump C E source target (MaskedClusterStage.read C E pref input)).map
        (MaskedClusterStage.read C E (Y++after)) := by
  cases input <;> simp only [point,wordContext,wordMap_get,MaskedClusterStage.read,
    MaskedClusterStage.jump,DFA.run_append]
  · cases source <;> simp [Option.map,MaskedClusterStage.read,DFA.run_append]
  · split <;> simp only [Option.map,MaskedClusterStage.read,DFA.run_append]
  · rfl

/-- Two direct mask slots; the fixed scalar charge covers the bounded
    case analysis, map-cell lookups, final-state and equality checks. -/
def pointCell (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (source target : Array Bool) (p : Nat)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : MaskedProgression.Answer :=
  ⟨decide (point C E maps tail (MaskedProgression.readMask source p)
    (MaskedProgression.readMask target p) input=some output),2,12⟩

theorem pointCell_work (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (source target : Array Bool) (p : Nat)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (pointCell C E maps tail source target p input output).slots+
      (pointCell C E maps tail source target p input output).arithmetic=14 := rfl

theorem pointCell_direct (C E : DFA α) (w : Word α) (anchor I p L H O : Nat)
    (source target : Array Bool) (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hI : I≤p) (hLH : L≤H) (hO : p+H≤O) (hn : O≤w.length) (hanchor : anchor+H≤w.length)
    (hcopy : slice w anchor (anchor+H)=slice w p (p+H)) :
    (pointCell C E
      (pointContexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        I p H O).maps
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        anchor L H).maps source target p input output).answer=true ↔
      MaskedClusterStage.direct C E w I p L O
        (MaskedProgression.readMask source p) (MaskedProgression.readMask target p) input=some output := by
  rw [pointContexts_value C E w I p H O hI hO hn,replay_value C E w anchor L H hLH hanchor]
  simp only [pointCell,decide_eq_true_eq,point_words]
  have hr : MaskedClusterStage.read C E
      (slice w (anchor+L) (anchor+H)++slice w (p+H) O)=
      fun t=>MaskedClusterStage.read C E (slice w (p+H) O)
        (MaskedClusterStage.read C E (slice w (anchor+L) (anchor+H)) t) := by
    funext t
    exact MaskedClusterStage.read_append C E _ _ t
  rw [hr]
  change MaskedClusterStage.anchored C E w anchor I p L H O _ _ input=some output ↔ _
  rw [MaskedClusterStage.anchored_exact C E w anchor I p L H O _ _ input hLH hO hcopy]

def pointMatrix (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (source target : Array Bool) (p : Nat) : MatrixResult (MaskedClusterStage.dfa C E).stateCount :=
  let m:=(MaskedClusterStage.dfa C E).stateCount
  ⟨Vector.ofFn (fun input=>Vector.ofFn (fun output=>
    (pointCell C E maps tail source target p
      (MaskedClusterStage.decode C E input) (MaskedClusterStage.decode C E output)).answer)),m*(m*15)⟩

theorem pointMatrix_get (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (source target : Array Bool) (p : Nat)
    (input output : Fin (MaskedClusterStage.dfa C E).stateCount) :
    (((pointMatrix C E maps tail source target p).cells.get input).get output)=
      (pointCell C E maps tail source target p
        (MaskedClusterStage.decode C E input) (MaskedClusterStage.decode C E output)).answer := by
  simp only [pointMatrix,BoundaryIndex.Table.get_ofFn]

theorem pointMatrix_work (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (source target : Array Bool) (p : Nat) :
    (pointMatrix C E maps tail source target p).work=
      (1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*15) := by
  simp only [pointMatrix,MaskedClusterStage.dfa_size]

end REWB.MaskedCluster
