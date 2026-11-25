import REWB.PeriodicConstructionOrbit
import REWB.CachedP1

/-! Measured cached regular-formula construction. Fixed-state orbit
search and DNF products are real operations here, not a supplied cost
oracle. Bounds do not depend on endpoint literals or on the run period.
Affine nodes are persistent constructors; their later traversals are
counted by projection and window conversion. -/
namespace REWB.PeriodicConstruction.Formula
open REWB.PeriodicConstruction REWB.AffineProjection REWB.PhaseSolver
variable {α : Type}

structure Budget where
  branches : Nat
  atoms : Nat
  work : Nat

def Shape (F : AffineProjection.Formula) (B A : Nat) : Prop :=
  F.length≤B ∧ ∀C,C∈F→C.length≤A

def Covers (r : Result AffineProjection.Formula) (b : Budget) : Prop :=
  Shape r.1 b.branches b.atoms ∧ r.2≤b.work

def both (F G : AffineProjection.Formula) : Result AffineProjection.Formula :=
  CountedProjection.flatMap (fun A=>CountedProjection.map (CountedProjection.append A) G) F

theorem both_value (F G : AffineProjection.Formula) : (both F G).1=PhaseSolver.both F G := by
  simp only [both,CountedProjection.flatMap_value,CountedProjection.map_value,
    CountedProjection.append_value,PhaseSolver.both]

theorem both_work (F G : AffineProjection.Formula) (B A C D : Nat)
    (hf : Shape F B A) (hg : Shape G C D) :
    (both F G).2≤B*(C*(A+3)+3)+1 := by
  have h:=flatMap_bound (fun X=>CountedProjection.map (CountedProjection.append X) G)
    F (C*(A+2)+1) C (by
      intro X hx
      have hm:=map_bound (CountedProjection.append X) G (A+1) (by
        intro Y _
        rw [CountedProjection.append_steps]
        exact Nat.add_le_add_right (hf.2 X hx) 1)
      exact Nat.le_trans hm (Nat.add_le_add_right
        (Nat.mul_le_mul_right _ hg.1) 1)) (by
      intro X _
      simpa only [CountedProjection.map_value,List.length_map] using hg.1)
  have ht:=Nat.le_trans h (Nat.add_le_add_right (Nat.mul_le_mul_right _ hf.1) 1)
  have he : C*(A+2)+1+C+2=C*(A+3)+3 := by
    simp only [Nat.mul_add]
    omega
  simpa only [he] using ht

theorem both_shape (F G : AffineProjection.Formula) (B A C D : Nat)
    (hf : Shape F B A) (hg : Shape G C D) :
    Shape (both F G).1 (B*C) (A+D) := by
  rw [both_value]
  constructor
  · rw [PhaseSolver.both_length]
    exact Nat.mul_le_mul hf.1 hg.1
  · intro X hx
    obtain ⟨Y,hy,hm⟩ := List.mem_flatMap.mp hx
    obtain ⟨Z,hz,rfl⟩ := List.mem_map.mp hm
    simpa only [List.length_append] using Nat.add_le_add (hf.2 Y hy) (hg.2 Z hz)

def join (F G : Result AffineProjection.Formula) : Result AffineProjection.Formula :=
  let r:=both F.1 G.1
  (r.1,F.2+G.2+r.2+1)

def Budget.join (a b : Budget) : Budget :=
  ⟨a.branches*b.branches,a.atoms+b.atoms,
    a.work+b.work+a.branches*(b.branches*(a.atoms+3)+3)+2⟩

theorem join_value (F G : Result AffineProjection.Formula) :
    (join F G).1=PhaseSolver.both F.1 G.1 := both_value _ _

theorem join_covers (F G : Result AffineProjection.Formula) (a b : Budget)
    (hf : Covers F a) (hg : Covers G b) : Covers (join F G) (a.join b) := by
  refine ⟨both_shape F.1 G.1 _ _ _ _ hf.1 hg.1,?_⟩
  have h:=both_work F.1 G.1 _ _ _ _ hf.1 hg.1
  change F.2+G.2+(both F.1 G.1).2+1≤_
  simp only [Budget.join]
  have h1:=hf.2
  have h2:=hg.2
  omega

def charge (r : Result AffineProjection.Formula) (k : Nat) : Result AffineProjection.Formula :=
  (r.1,r.2+k)

def Budget.charge (b : Budget) (k : Nat) : Budget := {b with work:=b.work+k}

theorem charge_covers (r : Result AffineProjection.Formula) (b : Budget) (k : Nat)
    (h : Covers r b) : Covers (charge r k) (b.charge k) :=
  ⟨h.1,Nat.add_le_add_right h.2 k⟩

def le (a b : Aff) : Result AffineProjection.Formula := (PhaseSolver.le a b,5)
def leBudget : Budget := ⟨1,1,5⟩
theorem le_covers (a b : Aff) : Covers (le a b) leBudget := by
  simp [Covers,Shape,le,leBudget,PhaseSolver.le,PhaseSolver.unit]

def eq (a b : Aff) : Result AffineProjection.Formula := join (le a b) (le b a)
def eqBudget : Budget := leBudget.join leBudget
theorem eq_value (a b : Aff) : (eq a b).1=PhaseSolver.eq a b := by
  simp only [eq,join_value,le,PhaseSolver.eq]
theorem eq_covers (a b : Aff) : Covers (eq a b) eqBudget :=
  join_covers _ _ _ _ (le_covers _ _) (le_covers _ _)

def bound (a : Endpoint) (q n : Nat) : Result AffineProjection.Formula :=
  if a.phase<q ∧ a.phase≤n then
    charge (join (le (.lit 0) a.1) (le a.1 (.lit (Int.ofNat ((n-a.phase)/q))))) 7
  else ([],3)
def boundBudget : Budget := eqBudget.charge 7

theorem bound_value (a : Endpoint) (q n : Nat) : (bound a q n).1=a.bound q n := by
  unfold bound Endpoint.bound
  split <;> simp only [charge,join_value,le]

theorem bound_covers (a : Endpoint) (q n : Nat) : Covers (bound a q n) boundBudget := by
  unfold bound
  split
  · exact charge_covers _ _ _ (join_covers _ _ _ _ (le_covers _ _) (le_covers _ _))
  · simp [Covers,Shape,boundBudget,eqBudget,Budget.charge,Budget.join,leBudget]

def order (q n : Nat) (a b : Endpoint) : Result AffineProjection.Formula :=
  charge (join (join (bound a q n) (bound b q n)) (le (.lit 0) (countExpr a b))) 5
def orderBudget : Budget := ((boundBudget.join boundBudget).join leBudget).charge 5

theorem order_value (q n : Nat) (a b : Endpoint) :
    (order q n a b).1=orderFormula q n a b := by
  simp only [order,charge,join_value,bound_value,le,orderFormula]

theorem order_covers (q n : Nat) (a b : Endpoint) : Covers (order q n a b) orderBudget :=
  charge_covers _ _ _ (join_covers _ _ _ _
    (join_covers _ _ _ _ (bound_covers _ _ _) (bound_covers _ _ _)) (le_covers _ _))

def stateAt (d : DFA α) (T : PeriodicCache.Table d) (a r : Nat) (v : Fin d.stateCount) :
    Result (Fin d.stateCount) :=
  match T[a]? with
  | none => (d.initial,3)
  | some phase =>
    match phase[v.val]? with
    | none => (d.initial,6)
    | some row => (row[r]?.getD d.initial,9)

theorem stateAt_value (d : DFA α) (T : PeriodicCache.Table d) (a r : Nat)
    (v : Fin d.stateCount) : (stateAt d T a r v).1=PeriodicCache.stateAt d T a r v := by
  unfold stateAt PeriodicCache.stateAt PeriodicCache.lookup
  cases T[a]? with
  | none => rfl
  | some phase =>
    change (match phase[v.val]? with
      | none => (d.initial,6) | some row => (row[r]?.getD d.initial,9)).1=
      ((phase[v.val]?).bind (fun row=>row[r]?)).getD d.initial
    cases phase[v.val]? <;> rfl

theorem stateAt_work (d : DFA α) (T : PeriodicCache.Table d) (a r : Nat)
    (v : Fin d.stateCount) : (stateAt d T a r v).2≤9 := by
  unfold stateAt
  cases T[a]? with
  | none => simp
  | some phase =>
    dsimp only
    cases phase[v.val]? <;> simp

def descriptor (d : DFA α) (T : PeriodicCache.Table d) (q a rho : Nat) :
    Result (Option FiniteOrbit.Descriptor) :=
  Orbit.compress d.stateCount (stateAt d T a q) d.initial
    (fun v=>let r:=stateAt d T a rho v; (d.final r.1,r.2+2))

theorem descriptor_value (d : DFA α) (T : PeriodicCache.Table d) (q a rho : Nat) :
    (descriptor d T q a rho).1=PeriodicCache.descriptor d T q a rho := by
  have h:=Orbit.compress_value (FiniteRelation.finEnum d.stateCount)
    (stateAt d T a q) d.initial (fun v=>let r:=stateAt d T a rho v; (d.final r.1,r.2+2))
  simpa only [FiniteRelation.finEnum,List.length_ofFn,stateAt_value,descriptor,
    PeriodicCache.descriptor] using h

theorem descriptor_work (d : DFA α) (T : PeriodicCache.Table d) (q a rho : Nat) :
    (descriptor d T q a rho).2≤Orbit.compressBudget d.stateCount 11 := by
  apply Orbit.compress_work
  · intro v
    exact Nat.le_trans (stateAt_work d T a q v) (by decide)
  · intro v
    exact Nat.add_le_add_right (stateAt_work d T a rho v) 2

theorem descriptor_size (d : DFA α) (T : PeriodicCache.Table d) (q a rho : Nat)
    (D : FiniteOrbit.Descriptor) (h : (descriptor d T q a rho).1=some D) :
    D.initialCounts.length+D.residues.length≤d.stateCount := by
  rw [descriptor_value] at h
  simpa only [FiniteRelation.finEnum,List.length_ofFn] using
    FiniteOrbit.compress_size _ _ _ _ D h

def descriptorFormula (D : FiniteOrbit.Descriptor) (t : Aff) : Result AffineProjection.Formula :=
  let initial:=Orbit.filter (fun k=>(decide (k<D.threshold),2)) D.initialCounts
  let a:=CountedProjection.map (fun k=>(exactCount t k,13)) initial.1
  let b:=CountedProjection.map (fun r=>(progression t (D.threshold+r) D.period,14)) D.residues
  let out:=CountedProjection.append a.1 b.1
  (out.1,initial.2+a.2+b.2+out.2+5)

def descriptorBudget (S : Nat) : Budget := ⟨S,2,40*S+10⟩

theorem descriptorFormula_value (D : FiniteOrbit.Descriptor) (t : Aff) :
    (descriptorFormula D t).1=AffineProjection.descriptorFormula D t := by
  simp only [descriptorFormula,CountedProjection.append_value,CountedProjection.map_value,
    Orbit.filter_value,AffineProjection.descriptorFormula]

theorem descriptorFormula_covers (D : FiniteOrbit.Descriptor) (t : Aff) (S : Nat)
    (hs : D.initialCounts.length+D.residues.length≤S) :
    Covers (descriptorFormula D t) (descriptorBudget S) := by
  constructor
  · rw [descriptorFormula_value]
    constructor
    · exact Nat.le_trans (PhaseSolver.descriptor_length D t) hs
    · intro C hc
      rcases List.mem_append.mp hc with hc|hc
      · obtain ⟨k,_,rfl⟩:=List.mem_map.mp hc
        exact Nat.le_refl _
      · obtain ⟨r,_,rfl⟩:=List.mem_map.mp hc
        exact Nat.le_refl _
  · have hf:=Orbit.filter_work (fun k=>(decide (k<D.threshold),2)) D.initialCounts 2
      (fun _ _=>Nat.le_refl _)
    have hl:=List.length_filter_le (fun k=>decide (k<D.threshold)) D.initialCounts
    simp only [Orbit.filter_value] at hf
    unfold descriptorFormula descriptorBudget
    dsimp only
    rw [CountedProjection.append_steps,CountedProjection.map_plain_steps,
      CountedProjection.map_plain_steps,CountedProjection.map_value,List.length_map,Orbit.filter_value]
    simp only [Nat.reduceAdd,Nat.mul_comm _ 14,Nat.mul_comm _ 15] at *
    omega

def regular (q n : Nat) (d : DFA α) (T : PeriodicCache.Table d) (a b : Endpoint) :
    Result AffineProjection.Formula :=
  let desc:=descriptor d T q a.phase (tailLen q a b)
  let f:=match desc.1 with
    | none => ([],1)
    | some D => descriptorFormula D (countExpr a b)
  let out:=join (order q n a b) f
  (out.1,desc.2+out.2+6)

def regularBudget (S : Nat) : Budget :=
  (orderBudget.join (descriptorBudget S)).charge (Orbit.compressBudget S 11+6)

theorem regular_value (q n : Nat) (d : DFA α) (T : PeriodicCache.Table d) (a b : Endpoint) :
    (regular q n d T a b).1=CachedPhase.regular q n d T a b := by
  unfold regular CachedPhase.regular
  dsimp only
  rw [join_value,order_value,descriptor_value]
  cases PeriodicCache.descriptor d T q a.phase (tailLen q a b) <;>
    simp only [descriptorFormula_value]

theorem regular_covers (q n : Nat) (d : DFA α) (T : PeriodicCache.Table d) (a b : Endpoint) :
    Covers (regular q n d T a b) (regularBudget d.stateCount) := by
  have hd:=descriptor_work d T q a.phase (tailLen q a b)
  have hf : Covers (match (descriptor d T q a.phase (tailLen q a b)).1 with
      | none => ([],1) | some D=>descriptorFormula D (countExpr a b)) (descriptorBudget d.stateCount) := by
    cases he : (descriptor d T q a.phase (tailLen q a b)).1 with
    | none => simp [Covers,Shape,descriptorBudget]
    | some D => exact descriptorFormula_covers D _ _ (descriptor_size d T q _ _ D he)
  have hj:=join_covers _ _ _ _ (order_covers q n a b) hf
  exact ⟨hj.1,by
    have hw:=hj.2
    unfold regular regularBudget Budget.charge
    dsimp only
    omega⟩

end REWB.PeriodicConstruction.Formula
