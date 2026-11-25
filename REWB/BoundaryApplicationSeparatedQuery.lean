import REWB.BoundaryApplicationSeparatedIndex
import REWB.BoundaryApplicationSeparatedSuffix

/-! Closed separated-boundary index and E prefix queries. The exported
query predicate uses only original word slices and concrete cut/end
positions. Both the endpoint bits and their static E aggregate are
constructed internally. -/
namespace REWB.BoundaryApplication.Separated
open REWB.Spec (slice)
variable {σ : Nat} {w : Word (Fin σ)}

structure Index (E : DFA (Fin σ)) (w : Word (Fin σ)) where
  endpoints : BitIndex w
  suffix : Suffix.Index E
  work : Nat

def build (A B C D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h1 : g1≤w.length) : Index E w :=
  let endpoints:=buildBits A B C D w fallback g0 g1 h1
  let suffix:=Suffix.build E w endpoints.bits
  ⟨endpoints,suffix,endpoints.work+suffix.work+3⟩

def query (E : DFA (Fin σ)) (idx : Index E w) (right : Nat) : Bool×Nat :=
  Suffix.query E idx.suffix right

def QueryPredicate (A B C D E : DFA (Fin σ)) (w : Word (Fin σ)) (g0 g1 right : Nat) : Prop :=
  ∃target : Fin (w.length+1),target.val≤right ∧ Predicate A B C D w g0 g1 target ∧
    E.accepts (slice w target.val right)

theorem query_correct (A B C D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h01 : g0≤g1) (h1 : g1≤w.length) (right : Nat) (hr : right≤w.length) :
    (query E (build A B C D E w fallback g0 g1 h1) right).1=true ↔
      QueryPredicate A B C D E w g0 g1 right := by
  change (Suffix.query E (Suffix.build E w (buildBits A B C D w fallback g0 g1 h1).bits) right).1=true ↔ _
  rw [Suffix.query_correct E w _ right hr]
  simp only [buildBits_correct A B C D w fallback g0 g1 h01 h1,QueryPredicate]

theorem query_iff_cuts (A B C D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h01 : g0≤g1) (h1 : g1≤w.length) (right : Nat) (hr : right≤w.length) :
    (query E (build A B C D E w fallback g0 g1 h1) right).1=true ↔
      ∃a L t,a≤g0 ∧ L≤a ∧ g1+L≤t ∧ t≤right ∧
        slice w (a-L) a=slice w (t-L) t ∧
        A.accepts (slice w 0 (a-L)) ∧ B.accepts (slice w (a-L) a) ∧
        C.accepts (slice w a g0) ∧ D.accepts (slice w g1 (t-L)) ∧ E.accepts (slice w t right) := by
  rw [query_correct A B C D E w fallback g0 g1 h01 h1 right hr]
  constructor
  · rintro ⟨target,ht,⟨source,hs,hC,L,hL,hg,he,hA,hB,hD⟩,hE⟩
    exact ⟨source.val,L,target.val,hs,hL,hg,ht,he,hA,hB,hC,hD,hE⟩
  · rintro ⟨a,L,t,ha,hL,hg,ht,he,hA,hB,hC,hD,hE⟩
    exact ⟨⟨t,by omega⟩,ht,⟨⟨a,by omega⟩,ha,hC,L,hL,hg,he,hA,hB,hD⟩,hE⟩

theorem query_work (E : DFA (Fin σ)) (idx : Index E w) (right : Nat) :
    (query E idx right).2≤(idx.suffix.height+1)*BoundaryIndex.Tree.queryBudget 1 E.stateCount+E.stateCount+2 :=
  Suffix.query_work E idx.suffix right

theorem query_build_work (A B C D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h1 : g1≤w.length) (right : Nat) :
    (query E (build A B C D E w fallback g0 g1 h1) right).2≤
      ((w.length+1).log2+2)*BoundaryIndex.Tree.queryBudget 1 E.stateCount+E.stateCount+2 := by
  have hh:=query_work E (build A B C D E w fallback g0 g1 h1) right
  change (query E (build A B C D E w fallback g0 g1 h1) right).2≤
    ((Suffix.build E w (buildBits A B C D w fallback g0 g1 h1).bits).height+1)*
      BoundaryIndex.Tree.queryBudget 1 E.stateCount+E.stateCount+2 at hh
  rw [Suffix.build_height] at hh
  simpa only [BoundaryApplication.height,BoundaryIndex.Tree.heightFor,Nat.add_assoc] using hh

end REWB.BoundaryApplication.Separated
