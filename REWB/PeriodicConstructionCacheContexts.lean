import REWB.PeriodicConstructionCacheEquality
import REWB.BoundaryContexts

/-! Actual exterior-context and per-run cache builders. These preserve the
entire legacy result, including its transition/comparison counter. The new
counter also measures list traversal, state-domain construction, array
materialization, and scalar assembly. The old shared context arrays are
read directly; no exterior word is rescanned while preparing one run. -/
namespace REWB.PeriodicConstruction.Cache
variable {α : Type}

def vector (d : DFA α) (f : Fin d.stateCount→Result (Fin d.stateCount)) :
    Result (DFACut.Row d) :=
  let domain:=CountedProjection.range d.stateCount
  let values:=CountedProjection.map (fun i=>
    let out:=f (PeriodicCache.state d i)
    (out.1,out.2+3)) domain.1
  let out:=array values.1
  (out.1,domain.2+values.2+out.2+3)

theorem vector_value (d : DFA α) (f : Fin d.stateCount→Result (Fin d.stateCount)) :
    (vector d f).1=DFACut.vector d (fun v=>(f v).1) := by
  simp only [vector,array_value,CountedProjection.map_value,
    CountedProjection.range_value,DFACut.vector]

def vectorCost (m C : Nat) : Nat :=
  (2*m+1)+(m*(C+4)+1)+(2*m+1)+3

theorem vector_work (d : DFA α) (f : Fin d.stateCount→Result (Fin d.stateCount))
    (C : Nat) (h : ∀v,(f v).2=C) :
    (vector d f).2=vectorCost d.stateCount C := by
  have hc:=CountedProjection.map_steps_constant
    (fun i=>let out:=f (PeriodicCache.state d i); (out.1,out.2+3))
    (List.range d.stateCount) (C+3) (by intro i _; simp only [h])
  rw [List.length_range] at hc
  simp only [vector,CountedProjection.range_value,range_work,array_work,
    CountedProjection.map_value,List.length_map,List.length_range,vectorCost]
  rw [hc]

def suffix (d : DFA α) : Word α→Result (List (DFACut.Row d)×Nat)
  | []=>
    let row:=vector d (fun v=>(v,1))
    (([row.1],d.stateCount),row.2+3)
  | c::cs=>
    let tail:=suffix d cs
    let row:=vector d (fun v=>
      (DFACut.read d (tail.1.1.headD #[]) (d.step v c),8))
    ((row.1::tail.1.1,d.stateCount+tail.1.2),tail.2+row.2+5)

theorem suffix_value (d : DFA α) (w : Word α) :
    (suffix d w).1=BoundaryContexts.suffix d w := by
  induction w with
  | nil=>simp only [suffix,vector_value,BoundaryContexts.suffix,id]
  | cons c cs ih=>simp only [suffix,vector_value,ih,BoundaryContexts.suffix]

theorem suffix_length (d : DFA α) (w : Word α) :
    (suffix d w).1.1.length=w.length+1 := by
  induction w with
  | nil=>rfl
  | cons c cs ih=>simp only [suffix,List.length_cons,ih]

def suffixCost (m n : Nat) : Nat :=
  n*(vectorCost m 8+5)+(vectorCost m 1+3)

theorem suffix_work (d : DFA α) (w : Word α) :
    (suffix d w).2=suffixCost d.stateCount w.length := by
  induction w with
  | nil=>
    simpa only [suffix,suffixCost,List.length_nil,Nat.zero_mul,Nat.zero_add] using
      congrArg (fun c=>c+3) (vector_work d (fun v=>(v,1)) 1 (by intro v; rfl))
  | cons c cs ih=>
    dsimp only [suffix]
    rw [ih,vector_work d _ 8 (by intro v; rfl)]
    simp only [suffixCost,List.length_cons,Nat.add_mul,Nat.one_mul] <;> omega

def contexts (P : SevenDFA α) (w : Word α) :
    Result (BoundaryContexts.Index P×Nat) :=
  let front:=prefixScan P.A P.A.initial w
  let back:=suffix P.H w
  let a:=array front.1.1
  let h:=array back.1.1
  ((⟨a.1,h.1⟩,front.1.2+1+back.1.2),front.2+back.2+a.2+h.2+5)

theorem contexts_value (P : SevenDFA α) (w : Word α) :
    (contexts P w).1=BoundaryContexts.build P w := by
  simp only [contexts,array_value,prefix_value,suffix_value,BoundaryContexts.build]

def contextsCost (m n : Nat) : Nat :=
  prefixCost n+suffixCost m n+(2*(n+1)+1)+(2*(n+1)+1)+5

theorem contexts_work (P : SevenDFA α) (w : Word α) :
    (contexts P w).2=contextsCost P.H.stateCount w.length := by
  simp only [contexts,prefix_work,suffix_work,array_work,prefix_length,suffix_length,
    contextsCost]

def prepareAt [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (I : BoundaryContexts.Index P) (lo hi : Nat) :
    Result (FullyCachedP2.Shared P×Nat) :=
  let a:=BoundaryContexts.contextA P I lo
  let h:=BoundaryContexts.contextH P I hi
  let ta:=transitions a s q
  let tb:=transitions P.B s q
  let tc:=transitions P.C s q
  let td:=transitions P.D s q
  let tf:=transitions P.F s q
  let tg:=transitions P.G s q
  let th:=transitions h s q
  let te:=equality s q
  ((⟨a,h,ta.1.1,tb.1.1,tc.1.1,td.1.1,tf.1.1,tg.1.1,th.1.1,te.1.1⟩,
      ta.1.2+tb.1.2+tc.1.2+td.1.2+tf.1.2+tg.1.2+th.1.2+te.1.2),
    ta.2+tb.2+tc.2+td.2+tf.2+tg.2+th.2+te.2+24)

theorem prepareAt_value [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (I : BoundaryContexts.Index P) (lo hi : Nat) :
    (prepareAt P s q I lo hi).1=BoundaryContexts.countedPrepareAt P s q I lo hi := by
  simp only [prepareAt,transitions_value,equality_value,BoundaryContexts.countedPrepareAt]

def prepareAtCost (P : SevenDFA α) (q : Nat) : Nat :=
  transitionsCost P.A.stateCount q+transitionsCost P.B.stateCount q+
  transitionsCost P.C.stateCount q+transitionsCost P.D.stateCount q+
  transitionsCost P.F.stateCount q+transitionsCost P.G.stateCount q+
  transitionsCost P.H.stateCount q+equalityCost q+24

theorem prepareAt_work [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (I : BoundaryContexts.Index P) (lo hi : Nat) :
    (prepareAt P s q I lo hi).2=prepareAtCost P q := by
  simp only [prepareAt,transitions_work,equality_work,prepareAtCost,
    BoundaryContexts.contextA,BoundaryContexts.contextH]

end REWB.PeriodicConstruction.Cache
