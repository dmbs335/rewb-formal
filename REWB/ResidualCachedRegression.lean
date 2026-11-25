import REWB.ResidualCachedAuto
import REWB.BoundaryRangeCacheRegression
import REWB.OneUseRangeCacheRegression

/-! Closed endpoint row fixtures with proved provenance. These do not
assume Ready and do not enumerate unbounded cuts. General production
row construction remains separate from this empty-input regression. -/
namespace REWB.ResidualCached.Regression
open REWB.BoundaryRange
variable {σ : Nat}

def p1Empty (P : SevenDFA (Fin σ)) (width : Nat) : P1.Inputs P 0 width :=
  Vector.ofFn fun _=>BoundaryRange.Cache.Regression.emptyInputs P.G width

theorem p1Empty_ready (P : SevenDFA (Fin σ)) (width : Nat) :
    P1.Ready P [] width (p1Empty P width) := by
  intro g
  simp only [p1Empty,Table.vector_get_ofFn]
  exact BoundaryRange.Cache.Regression.emptyInputs_ready P.A P.B P.C (gap P g) P.D width

def p2Empty (P : SevenDFA (Fin σ)) (width : Nat) : P2.Inputs P 0 width :=
  ⟨Table.build (fun q=>
    let row:=Table.build fun c=>
      (OneUseRange.Cache.Regression.emptyInputs P.C P.D (suffix P q c) width,0)
    (row,row.work)),
   Table.build (fun a=>
    let row:=Table.build fun g=>
      (OneUseRange.Cache.Regression.emptyInputs (Automata.reverse P.C) (Automata.reverse P.D)
        (Automata.reverse (front P a g)) width,0)
    (row,row.work))⟩

theorem p2Empty_ready (P : SevenDFA (Fin σ)) (width : Nat) :
    P2.Ready P [] width (p2Empty P width) := by
  intro a g q c
  simp only [p2Empty,Table.get_build]
  exact OneUseRange.Cache.Regression.emptyInputs_ready (front P a g) P.C P.D (suffix P q c) width

def EmptyAccepts (P : SevenDFA (Fin σ)) : Prop :=
  P.A.accepts [] ∧ P.B.accepts [] ∧ P.C.accepts [] ∧ P.D.accepts [] ∧
    P.F.accepts [] ∧ P.G.accepts [] ∧ P.H.accepts []

theorem p1_empty (P : SevenDFA (Fin σ)) (fallback : Fin σ) (s : Nat) (hs : 0<s) :
    (P1.query (P1.build P [] fallback s hs (p1Empty P s)) ⟨0,0,0⟩).1=true ↔ EmptyAccepts P := by
  rw [P1.query_correct P [] fallback s hs _ (p1Empty_ready P s)]
  change (∃q,Spec.boundaryRange _ _ _ _ _ _ [] 0 0) ↔ _
  rw [ResidualSeparated.p1_iff P [] 0 0 0 ⟨by decide,by simp,by decide,rfl⟩]
  constructor
  · rintro ⟨v⟩
    have he : v.e=0 := by have h:=v.er; omega
    have ht : v.t=0 := by have h:=v.te; omega
    have hj : v.j=0 := by have h:=v.jt; omega
    have hp : v.p=0 := by have h:=v.pj; omega
    have ha : v.a=0 := by have h:=v.ap; omega
    have hi : v.i=0 := by have h:=v.ia; omega
    exact ⟨by simpa [he,ht,hj,hp,ha,hi,Spec.slice] using v.prefix_ok,
      by simpa [Spec.slice] using v.capture,by simpa [Spec.slice] using v.before,
      by simpa [Spec.slice] using v.middle,by simpa [Spec.slice] using v.after,
      by simpa [Spec.slice] using v.gap,by simpa [Spec.slice] using v.tail⟩
  · rintro ⟨hA,hB,hC,hD,hF,hG,hH⟩
    exact ⟨⟨0,0,0,0,0,0,by decide,by decide,by decide,by decide,by decide,by decide,by decide,
      rfl,hA,hB,hC,hD,hF,hG,hH⟩⟩

theorem p2_empty (P : SevenDFA (Fin σ)) (fallback : Fin σ) (s : Nat) (hs : 0<s) :
    (P2.query (P2.build P [] fallback s hs (p2Empty P s)) ⟨0,0,0⟩).1=true ↔ EmptyAccepts P := by
  rw [P2.query_correct P [] fallback s hs _ (p2Empty_ready P s)]
  change (∃q,Spec.oneUseRange _ _ _ _ [] 0 0) ↔ _
  rw [ResidualSeparated.p2_iff P [] 0 0 0 ⟨by decide,by simp,by decide,rfl⟩]
  constructor
  · rintro ⟨v⟩
    exact ⟨by simpa [Spec.slice] using v.prefix_ok,by simpa [Spec.slice] using v.before,
      by simpa [Spec.slice] using v.capture,by simpa [Spec.slice] using v.middle,
      by simpa [Spec.slice] using v.after,by simpa [Spec.slice] using v.gap,
      by simpa [Spec.slice] using v.tail⟩
  · rintro ⟨hA,hB,hC,hD,hF,hG,hH⟩
    exact ⟨⟨0,0,0,0,0,0,by decide,by decide,by decide,by decide,by decide,by decide,by decide,
      rfl,hA,hB,hC,hD,hF,hG,hH⟩⟩

theorem empty_widths : ThresholdBudget.block 0=8 ∧ ThresholdBudget.period 0=512 ∧
    ThresholdBudget.length 0=8192 := by
  have hh : (0+2).log2=1 := by exact Nat.log2_two_pow (n:=1)
  simp only [ThresholdBudget.block,ThresholdBudget.period,ThresholdBudget.length,
    ThresholdBudget.base,ThresholdBudget.scale,hh]
  decide

theorem any_empty (f : α→Bool×Nat) : any f []=(false,1) := rfl

theorem any_all_called : any (fun n : Nat=>(decide (n=2),n+1)) [0,1,2,3]=(true,23) := by decide

end REWB.ResidualCached.Regression
