import REWB.ResidualActualIndependentGeometry
import REWB.MaskedAllStartRowsCorrect
import REWB.ResidualCachedVariants
import REWB.OneUseRangeFarAggregateSound

/-! Two actual all-start computations and one backwards DFA aggregate
decide independent captures. The reversed output marks ends of the first
pair; the forward output marks starts of the second pair. A linear scan
joins these immutable bitmaps through D, with zero-length gaps included.
There is no supplied row, split list, equality key or answer oracle. -/
namespace REWB.ResidualActual.Independent
open REWB.BoundaryRange REWB.OneUseRange
variable {σ : Nat}

structure Index where
  length : Nat
  ends : Array Bool
  suffix : FarAggregate.Index
  work : Nat
  fixedPatternBuilds : Nat

def prepare (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : Index :=
  let marks:=MaskedAllStart.Rows.full text.size
  let reversed:=text.reverse
  let ends:=MaskedAllStart.Rows.row (Automata.reverse P.B) (Automata.reverse P.C)
    (Automata.reverse P.A) reversed fallback marks marks
  let starts:=MaskedAllStart.Rows.row P.F P.G P.H text fallback marks marks
  let suffix:=FarAggregate.build P.D text starts.bits
  ⟨text.size,ends.bits,suffix,ends.work+starts.work+suffix.work+4*text.size+12,
    ends.fixedPatternBuilds+starts.fixedPatternBuilds+3⟩

def query (idx : Index) (t : Nat) : Bool×Nat :=
  if t≤idx.length then
    let rest:=FarAggregate.query idx.suffix t
    (FarAggregate.bit idx.ends (idx.length-t) && rest.1,rest.2+6)
  else (false,1)

theorem ends_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (t : Nat) (ht : t≤text.size) :
    FarAggregate.bit (prepare P text fallback).ends (text.size-t)=true ↔
      BeforeEnd P.A P.B P.C text.toList (fun _=>true) t := by
  have hr:=MaskedAllStart.Rows.row_full_correct (Automata.reverse P.B) (Automata.reverse P.C)
    (Automata.reverse P.A) text.reverse fallback (text.size-t)
  simp only [Array.size_reverse,Array.toList_reverse] at hr
  change FarAggregate.bit (prepare P text fallback).ends (text.size-t)=true ↔ _ at hr
  have he:=masked_reverse P.A P.B P.C text.toList (fun _=>true) t
    (by simpa only [Array.length_toList] using ht)
  simp only [Array.length_toList] at he
  exact hr.trans he

theorem suffix_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (t : Nat) :
    (FarAggregate.query (prepare P text fallback).suffix t).1=true ↔
      ∃s,t≤s ∧ s≤text.size ∧ Spec.maskedStart P.F P.G P.H text.toList (fun _=>true) s ∧
        P.D.accepts (Spec.slice text.toList t s) := by
  apply FarAggregate.query_substitute
  intro s _
  exact MaskedAllStart.Rows.row_full_correct P.F P.G P.H text fallback s

theorem query_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (t : Nat) :
    (query (prepare P text fallback) t).1=true ↔
      ∃s,t≤s ∧ s≤text.size ∧ BeforeEnd P.A P.B P.C text.toList (fun _=>true) t ∧
        P.D.accepts (Spec.slice text.toList t s) ∧ Spec.maskedStart P.F P.G P.H text.toList (fun _=>true) s := by
  by_cases ht : t≤text.size
  · unfold query
    rw [show (prepare P text fallback).length=text.size from rfl,if_pos ht]
    dsimp only
    rw [Bool.and_eq_true,ends_correct P text fallback t ht,suffix_correct]
    constructor
    · rintro ⟨he,s,hts,hsn,hstart,hd⟩
      exact ⟨s,hts,hsn,he,hd,hstart⟩
    · rintro ⟨s,hts,hsn,he,hd,hstart⟩
      exact ⟨he,s,hts,hsn,hstart,hd⟩
  · unfold query
    rw [show (prepare P text fallback).length=text.size from rfl,if_neg ht]
    simp only [Bool.false_eq_true,false_iff]
    rintro ⟨s,hts,hsn,_⟩
    exact ht (Nat.le_trans hts hsn)

theorem query_work (idx : Index) (t : Nat) : (query idx t).2≤10 := by
  have h:=FarAggregate.query_work idx.suffix t
  unfold query
  split <;> dsimp only <;> omega

structure Execution where
  answer : Bool
  accountedWork : Nat
  fixedPatternBuilds : Nat

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : Execution :=
  let idx:=prepare P text fallback
  let checked:=ResidualCached.any (query idx) (List.range (idx.length+1))
  ⟨checked.1,idx.work+checked.2+idx.length+8,idx.fixedPatternBuilds⟩

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (execute P text fallback).answer=true ↔ MatchesWithin P.independent text.toList 2 := by
  rw [←joined_correct]
  change (ResidualCached.any (query (prepare P text fallback)) (List.range (text.size+1))).1=true ↔ _
  rw [ResidualCached.any_correct]
  simp only [List.mem_range,query_correct]
  constructor
  · rintro ⟨t,_,s,hts,hsn,he,hd,hstart⟩
    exact ⟨t,s,hts,by simpa only [Array.length_toList] using hsn,he,hd,hstart⟩
  · rintro ⟨t,s,hts,hsn,he,hd,hstart⟩
    rw [Array.length_toList] at hsn
    exact ⟨t,by omega,s,hts,hsn,he,hd,hstart⟩

theorem execute_work (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (execute P text fallback).accountedWork≤(prepare P text fallback).work+13*(text.size+1)+text.size+9 := by
  have h:=ResidualCached.any_work (query (prepare P text fallback)) (List.range (text.size+1)) 10
    (fun t _=>query_work _ t)
  rw [List.length_range] at h
  change (prepare P text fallback).work+
    (ResidualCached.any (query (prepare P text fallback)) (List.range (text.size+1))).2+text.size+8≤_
  omega

theorem prepare_work (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare P text fallback).work≤
      (MaskedAllStart.Rows.row (Automata.reverse P.B) (Automata.reverse P.C) (Automata.reverse P.A)
        text.reverse fallback (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)).work+
      (MaskedAllStart.Rows.row P.F P.G P.H text fallback
        (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)).work+
      (6*P.D.stateCount+7)*(text.size+1)+4*text.size+12 := by
  have h:=FarAggregate.build_work P.D text (MaskedAllStart.Rows.row P.F P.G P.H text fallback
    (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)).bits
  unfold prepare
  dsimp only
  omega

theorem execute_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (execute P text fallback).fixedPatternBuilds=(prepare P text fallback).fixedPatternBuilds := rfl

end REWB.ResidualActual.Independent
