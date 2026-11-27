import REWB.BoundaryRangeCacheCost
import REWB.OneUseRangeBorderRegression

/-! Kernel endpoint checks for the complete boundary cache. A closed
terminal mask has no positive all-start answers, so its actual empty
output rows have directly proved provenance. -/
namespace REWB.BoundaryRange.Cache.Regression
open REWB.Spec REWB.OneUseRange
open REWB.OneUseRange.Border.Regression
variable {σ : Nat}

def closedRows (K : DFA (Fin σ)) : FarRight.Input K := Vector.ofFn fun _=>Vector.ofFn fun _=>#[]

theorem closedRows_ready (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat)
    (hg : w.length≤grid) : FarRight.Ready A B C K D w grid (closedRows K) := by
  intro q k y hy
  simp only [closedRows,Table.vector_get_ofFn,FarAggregate.bit,Array.getElem?_empty,Option.getD_none,Bool.false_eq_true,false_iff]
  rintro ⟨a,j,t,_,_,hjt,ht,hm,_⟩
  rw [List.length_reverse] at ht
  rw [FarRight.readMask_correct K w grid q k j (by omega)] at hm
  have hFalse : ¬grid<w.length-j := by omega
  simp only [farMask,hFalse,decide_false,Bool.false_and,Bool.false_eq_true] at hm

def emptyInputs (K : DFA (Fin σ)) (width : Nat) : Inputs K 0 width := Vector.ofFn fun _=>closedRows K

theorem emptyInputs_ready (A B C K D : DFA (Fin σ)) (width : Nat) :
    Ready A B C K D [] width (emptyInputs K width) := by
  intro slot
  simp only [emptyInputs,Table.vector_get_ofFn]
  exact closedRows_ready A B C K D [] _ (Nat.zero_le _)

theorem empty_input :
    (query (build all all all all all all [] 0 4 (by decide) (emptyInputs all 4)) 0 0).1=true := by
  apply (query_correct all all all all all all [] 0 4 (by decide) _ (emptyInputs_ready all all all all all 4) 0 0).mpr
  exact ⟨by decide,by decide,0,0,0,0,0,by decide,by decide,by decide,by decide,by decide,by decide,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem empty_capture_rejected :
    (query (build all positive all all all all [] 0 1 (by decide) (emptyInputs all 1)) 0 0).1=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨_,_,i,a,p,j,t,hia,hap,hpj,hjt,htr,_,_,_,hB,_⟩:=
    (query_correct all positive all all all all [] 0 1 (by decide) _
      (emptyInputs_ready all positive all all all 1) 0 0).mp h
  have hi : i=0 := by omega
  have ha : a=0 := by omega
  subst i; subst a
  exact Bool.noConfusion hB

theorem finite_union_missing_bits :
    (FarRight.unionRow positive 2 ⟨#[#[true,false],#[false,true,true]],rfl⟩).bits=#[true,true,true] := by decide

theorem finite_union_empty :
    (FarRight.unionRow positive 0 ⟨#[#[],#[true]],rfl⟩).bits=#[true] := by decide

theorem zero_width_terminal_block :
    CacheGrid.lower 8 4 2=8 ∧ CacheGrid.upper 8 4 2=8 := by decide

theorem clipped_last_block :
    CacheGrid.lower 7 5 1=5 ∧ CacheGrid.upper 7 5 1=7 := by decide

theorem invalid_range {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index A B C K D E w) (left right : Nat) (h : ¬(left≤right ∧ right≤idx.prepared.length)) :
    query idx left right=(false,3) := by simp only [query,dif_neg h]

theorem two_stage (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs K w.length width) :
    build A B C K D E w fallback width hw bits=
      assemble A B C K D E w (prepare A B C K D E w fallback width hw) bits := rfl

theorem all_gap (k : Fin all.stateCount) (v : Word (Fin 2)) :
    (Automata.gap all all all all.initial k).accepts v := by
  rw [Automata.gap,Automata.join_accepts]
  refine ⟨[],v,rfl,?_,rfl⟩
  rw [Automata.meet_accepts]
  exact ⟨rfl,rfl⟩

private theorem all_state (q k : Fin all.stateCount) : q=k := by
  apply Fin.ext
  have hq : q.val<1 := q.isLt
  have hk : k.val<1 := k.isLt
  omega

theorem all_masked (w : Word (Fin 2)) (grid : Nat) (q k : Fin all.stateCount)
    (y : Nat) (hy : y≤w.length) :
    Spec.maskedStart (Automata.reverse all)
      (Automata.reverse (Automata.gap all all all all.initial k)) (Automata.reverse all)
      w.reverse (FarRight.readMask (FarRight.prepare all w grid) q k) y ↔ grid<w.length-y := by
  constructor
  · rintro ⟨a,j,t,hya,haj,hjt,ht,hm,_⟩
    rw [List.length_reverse] at ht
    rw [FarRight.readMask_correct all w grid q k j (by omega)] at hm
    have hh:=(farMask_true all w grid q k (w.length-j)).mp hm
    omega
  · intro hg
    refine ⟨y,y,y,Nat.le_refl _,Nat.le_refl _,Nat.le_refl _,by simpa using hy,?_,rfl,?_,?_,?_⟩
    · rw [FarRight.readMask_correct all w grid q k y hy]
      apply (farMask_true all w grid q k (w.length-y)).mpr
      exact ⟨hg,all_state _ _⟩
    · exact (Automata.reverse_accepts all _).mpr rfl
    · apply (Automata.reverse_accepts _ _).mpr
      exact all_gap k _
    · exact (Automata.reverse_accepts all _).mpr rfl

def copiedMasks {w : Word (Fin 2)} (requests : FarRight.Requests all w) : FarRight.Input all :=
  Vector.ofFn fun q=>Vector.ofFn fun k=>(Table.get (Table.get requests.masks q) k).bits.toArray

theorem copiedMasks_ready (w : Word (Fin 2)) (grid : Nat) :
    FarRight.Ready all all all all all w grid (copiedMasks (FarRight.prepare all w grid)) := by
  intro q k y hy
  simp only [copiedMasks,Table.vector_get_ofFn]
  change FarRight.readMask (FarRight.prepare all w grid) q k y=true ↔ _
  rw [FarRight.readMask_correct all w grid q k y hy,all_masked w grid q k y hy,farMask_true]
  have he : all.run q (slice w grid (w.length-y))=k := all_state _ _
  simp only [he,and_true]

end REWB.BoundaryRange.Cache.Regression
