import REWB.OneUseRangeCacheCost
import REWB.OneUseRangeBorderRegression

/-! Endpoint regressions for the full finite cache. The empty input rows
are actually constructed below and their provenance is proved directly
from the original cut predicate; no all-start hypothesis is supplied. -/
namespace REWB.OneUseRange.Cache.Regression
open REWB.BoundaryRange REWB.BoundaryIndex REWB.Spec
open REWB.OneUseRange.Border.Regression
variable {σ : Nat}

def emptyRows (B C E : DFA (Fin σ)) : FarBank.Input E :=
  Vector.ofFn fun c=>#[B.final B.initial && C.final C.initial && Colors.decode E c E.initial]

theorem emptyRows_ready (B C E : DFA (Fin σ)) :
    FarBank.Ready B C E [] 0 (emptyRows B C E) := by
  intro c i hi
  have he : i=0 := by omega
  subst i
  simp only [emptyRows,Table.get_ofFn]
  change (B.final B.initial && C.final C.initial && Colors.decode E c E.initial)=true ↔ _
  rw [Bool.and_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hB,hC⟩,hE⟩
    exact ⟨0,0,0,by decide,by decide,by decide,by simp,rfl,rfl,hB,hC,hE⟩
  · rintro ⟨a,j,t,_,haj,hjt,ht,_,_,hB,hC,hE⟩
    have ha : a=0 := by simpa using Nat.eq_zero_of_le_zero (Nat.le_trans haj (Nat.le_trans hjt ht))
    have hj : j=0 := by simpa using Nat.eq_zero_of_le_zero (Nat.le_trans hjt ht)
    have ht' : t=0 := by simpa using Nat.eq_zero_of_le_zero ht
    subst a; subst j; subst t
    exact ⟨⟨hB,hC⟩,hE⟩

def emptyInputs (B C E : DFA (Fin σ)) (width : Nat) : Inputs E 0 width :=
  Vector.ofFn fun _=>emptyRows B C E

theorem emptyInputs_ready (A B C E : DFA (Fin σ)) (width : Nat) :
    Ready A B C E [] width (emptyInputs B C E width)
      (emptyInputs (Automata.reverse B) (Automata.reverse C) (Automata.reverse A) width) := by
  constructor
  · intro slot
    simpa only [emptyInputs,Table.get_ofFn,Grid.position,List.length_nil,Nat.zero_min] using emptyRows_ready B C E
  · intro slot
    simpa only [emptyInputs,Table.get_ofFn,Grid.backward,List.length_nil,Nat.zero_sub,List.reverse_nil] using
      emptyRows_ready (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)

theorem empty_input :
    (query (build all all all all [] 0 3 (by decide)
      (emptyInputs all all all 3)
      (emptyInputs (Automata.reverse all) (Automata.reverse all) (Automata.reverse all) 3)) 0 0).1=true := by
  apply (query_correct all all all all [] 0 3 (by decide) _ _ (emptyInputs_ready all all all all 3) 0 0).mpr
  exact ⟨by decide,by decide,0,0,0,0,by decide,by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl⟩

theorem epsilon_rejected_by_prefix :
    (query (build positive all all all [] 0 1 (by decide)
      (emptyInputs all all all 1)
      (emptyInputs (Automata.reverse all) (Automata.reverse all) (Automata.reverse positive) 1)) 0 0).1=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨_,_,i,a,j,t,_,hia,haj,hjt,ht,_,hA,_⟩:=
    (query_correct positive all all all [] 0 1 (by decide) _ _
      (emptyInputs_ready positive all all all 1) 0 0).mp h
  have hi : i=0 := by omega
  subst i
  exact Bool.noConfusion hA

theorem invalid_range {A B C E : DFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index A B C E w) (left right : Nat) (h : ¬(left≤right ∧ right≤idx.length)) :
    query idx left right=(false,3) := by simp only [query,dif_neg h]

theorem clipped_terminal_grid :
    (Grid.choose 7 5 (by decide) 7 7 (by decide) (by decide)).leftGrid=7 ∧
      (Grid.choose 7 5 (by decide) 7 7 (by decide) (by decide)).rightGrid=5 := by decide

theorem width_exceeds_text :
    (Grid.choose 3 8 (by decide) 1 3 (by decide) (by decide)).leftGrid=3 ∧
      (Grid.choose 3 8 (by decide) 1 3 (by decide) (by decide)).rightGrid=0 := by decide

theorem selected_core_equal (E : DFA (Fin σ)) (w : Word (Fin σ)) (grid right : Nat) :
    FarSelection.key (FarSelection.build E w) grid right=
      FarSelection.keyCore E (FarSelection.build E w).ranges (FarSelection.build E w).colors grid right := rfl

theorem bank_core_equal (E : DFA (Fin σ)) (w : Word (Fin σ)) (bank : FarBank.Index E)
    (selection : FarSelection.Index E w) (left right : Nat) :
    FarBank.query bank selection left right=
      FarBank.queryCore E bank selection.ranges selection.colors selection.length left right := rfl

end REWB.OneUseRange.Cache.Regression
