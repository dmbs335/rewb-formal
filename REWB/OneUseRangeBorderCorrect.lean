import REWB.OneUseRangeBorderIndex

/-! Exact original-slice semantics for the two short endpoint blocks.
The midpoint split is existentially quantified over the actual finite
DFA state, so the two sides belong to one common C-gap. -/
namespace REWB.OneUseRange.Border
open REWB.BoundaryApplication REWB.BoundaryRange REWB.Spec
open REWB.BoundaryBorder.Regular (endAt)
variable {σ : Nat}

theorem middle_bounds (i t : Nat) (hi : i≤t) :
    i≤middle i t ∧ middle i t≤t ∧ middle i t≤t-(middle i t-i) := by
  unfold middle
  omega

theorem middle_cut (i t L : Nat) (hi : i≤t) :
    i+2*L≤t ↔ i+L≤middle i t := by
  unfold middle
  omega

theorem split_gap (C : DFA (Fin σ)) (w : Word (Fin σ)) (a m p : Nat)
    (ham : a≤m) (hmp : m≤p) :
    (∃q : Fin C.stateCount,(Automata.start C q).accepts (slice w m p) ∧
      (Automata.stop C q).accepts (slice w a m)) ↔ C.accepts (slice w a p) := by
  simp only [Automata.start_accepts,Automata.stop_accepts]
  rw [OuterColumn.slice_split w a m p ham hmp]
  simp only [DFA.accepts,DFA.run_append]
  constructor
  · rintro ⟨q,hq,he⟩
    rwa [he]
  · intro hh
    exact ⟨C.run C.initial (slice w a m),hh,rfl⟩

def Inner (B C : DFA (Fin σ)) (w : Word (Fin σ)) (i t : Nat) : Prop :=
  ∃L,i+2*L≤t ∧ slice w i (i+L)=slice w (t-L) t ∧
    B.accepts (slice w i (i+L)) ∧ C.accepts (slice w (i+L) (t-L))

def At (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (left right i t : Nat) : Prop :=
  left≤i ∧ i≤t ∧ t≤right ∧ A.accepts (slice w left i) ∧
    E.accepts (slice w t right) ∧ Inner B C w i t

theorem state_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (i : Fin (w.toArray.size+1)) (t : Nat) (hi : i.val≤t) (ht : t≤w.length)
    (q : Fin C.stateCount) :
    (state (build A B C E w fallback) i t q).1=true ↔
      ∃p,p<t ∧ endAt i.val t p≤middle i.val t ∧
        slice w p t=slice w i.val (endAt i.val t p) ∧
        (Automata.start C q).accepts (slice w (middle i.val t) p) ∧
        B.accepts (slice w p t) ∧
        (Automata.stop C q).accepts (slice w (endAt i.val t p) (middle i.val t)) := by
  have hm:=middle_bounds i.val t hi
  change (Regular.dyadic (Automata.start C q) B (Automata.stop C q)
    (BoundaryBorder.WindowIndex.prepare w.toArray fallback)
    (startRanges C (Range.build C w) q) (Range.build B w) (stopRanges C (Range.build C w) q)
    (middle i.val t) t i (middle i.val t)).1=true ↔ _
  rw [startRanges_build,stopRanges_build]
  exact Regular.dyadic_correct (Automata.start C q) B (Automata.stop C q) w fallback
    (middle i.val t) t i (middle i.val t) hm.2.2 ht (by omega)

theorem positive_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (i : Fin (w.toArray.size+1)) (t : Nat) (hi : i.val≤t) (ht : t≤w.length) :
    (any (state (build A B C E w fallback) i t) (build A B C E w fallback).states).1=true ↔
      ∃L,0<L ∧ i.val+2*L≤t ∧ slice w i.val (i.val+L)=slice w (t-L) t ∧
        B.accepts (slice w i.val (i.val+L)) ∧ C.accepts (slice w (i.val+L) (t-L)) := by
  rw [any_correct]
  change (∃q,q∈List.finRange C.stateCount ∧ _) ↔ _
  simp only [List.finRange,List.mem_ofFn,exists_eq,true_and]
  simp only [state_correct A B C E w fallback i t hi ht]
  constructor
  · rintro ⟨q,p,hpt,hfinish,he,hC,hB,hstop⟩
    have hm:=middle_bounds i.val t hi
    have hbase:=Regular.source_bound (middle i.val t) t i.val (middle i.val t) p hm.2.2 hfinish
    have hL : i.val+2*(t-p)≤t := (middle_cut i.val t (t-p) hi).mpr hfinish
    have hp : t-(t-p)=p := by omega
    have hc:=(split_gap C w (endAt i.val t p) (middle i.val t) p hfinish hbase).mp
      ⟨q,hC,hstop⟩
    refine ⟨t-p,by omega,hL,?_,?_,?_⟩
    · simpa only [hp,endAt] using he.symm
    · simpa only [endAt] using he ▸ hB
    · simpa only [hp,endAt] using hc
  · rintro ⟨L,hL,hLen,he,hB,hC⟩
    have hLt : L≤t := by omega
    have hp : t-(t-L)=L := by omega
    have hfinish : endAt i.val t (t-L)≤middle i.val t := by
      simpa only [endAt,hp] using (middle_cut i.val t L hi).mp hLen
    have hm:=middle_bounds i.val t hi
    have hbase:=Regular.source_bound (middle i.val t) t i.val (middle i.val t) (t-L) hm.2.2 hfinish
    have hc : C.accepts (slice w (endAt i.val t (t-L)) (t-L)) := by
      simpa only [endAt,hp] using hC
    obtain ⟨q,hstart,hstop⟩:=(split_gap C w (endAt i.val t (t-L)) (middle i.val t) (t-L)
      hfinish hbase).mpr hc
    refine ⟨q,t-L,by omega,hfinish,?_,hstart,?_,hstop⟩
    · simpa only [endAt,hp] using he.symm
    · rwa [←he]

theorem inner_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (i : Fin (w.toArray.size+1)) (t : Nat) (hi : i.val≤t) (ht : t≤w.length) :
    (inner (build A B C E w fallback) i t).1=true ↔ Inner B C w i.val t := by
  change ((any (state (build A B C E w fallback) i t) (build A B C E w fallback).states).1 ||
    (B.final B.initial && (NearIndex.regular C (Range.build C w) i.val t).1))=true ↔ _
  rw [Bool.or_eq_true,Bool.and_eq_true,positive_correct A B C E w fallback i t hi ht,
    NearIndex.regular_correct C w i.val t hi ht]
  constructor
  · rintro (⟨L,_,h⟩|⟨hB,hC⟩)
    · exact ⟨L,h⟩
    · refine ⟨0,by omega,?_,?_,?_⟩
      · simp only [Nat.add_zero,Nat.sub_zero,OuterColumn.slice_self]
      · simpa only [Nat.add_zero,OuterColumn.slice_self,DFA.accepts,DFA.run] using hB
      · simpa only [Nat.add_zero,Nat.sub_zero] using hC
  · rintro ⟨L,hLen,he,hB,hC⟩
    by_cases hL : L=0
    · subst L
      right
      constructor
      · simpa only [Nat.add_zero,OuterColumn.slice_self,DFA.accepts,DFA.run] using hB
      · simpa only [Nat.add_zero,Nat.sub_zero] using hC
    · exact Or.inl ⟨L,by omega,hLen,he,hB,hC⟩

theorem queryAt_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right i t : Nat) (hr : right≤w.length) :
    (queryAt (build A B C E w fallback) left right i t).1=true ↔ At A B C E w left right i t := by
  by_cases hb : left≤i ∧ i≤t ∧ t≤right
  · have hg : left≤i ∧ i≤t ∧ t≤right ∧ right≤(build A B C E w fallback).size := by
      simpa only [build,List.size_toArray] using And.intro hb.1 (And.intro hb.2.1 (And.intro hb.2.2 hr))
    unfold queryAt
    rw [dif_pos hg]
    change ((NearIndex.regular A (Range.build A w) left i).1 &&
      (inner (build A B C E w fallback) ⟨i,_⟩ t).1 &&
      (NearIndex.regular E (Range.build E w) t right).1)=true ↔ _
    rw [Bool.and_eq_true,Bool.and_eq_true,
      NearIndex.regular_correct A w left i hb.1 (by omega),
      inner_correct A B C E w fallback ⟨i,_⟩ t hb.2.1 (by omega),
      NearIndex.regular_correct E w t right hb.2.2 hr]
    exact ⟨fun ⟨⟨hA,hI⟩,hE⟩=>⟨hb.1,hb.2.1,hb.2.2,hA,hE,hI⟩,
      fun ⟨_,_,_,hA,hE,hI⟩=>⟨⟨hA,hI⟩,hE⟩⟩
  · have hg : ¬(left≤i ∧ i≤t ∧ t≤right ∧ right≤(build A B C E w fallback).size) :=
      fun hh=>hb ⟨hh.1,hh.2.1,hh.2.2.1⟩
    simp only [queryAt,dif_neg hg,Bool.false_eq_true,false_iff]
    intro h
    exact hb ⟨h.1,h.2.1,h.2.2.1⟩

theorem row_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right rightGrid i : Nat) (hr : right≤w.length) :
    (row (build A B C E w fallback) left right rightGrid i).1=true ↔
      ∃t,rightGrid<t ∧ At A B C E w left right i t := by
  unfold row
  rw [NearIndex.scan_correct]
  simp only [queryAt_correct A B C E w fallback left right _ _ hr]
  constructor
  · rintro ⟨t,ht,_,h⟩
    exact ⟨t,by omega,h⟩
  · rintro ⟨t,hgt,h⟩
    have htr:=h.2.2.1
    exact ⟨t,by omega,by omega,h⟩

theorem query_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right leftGrid rightGrid : Nat) (hr : right≤w.length) :
    (query (build A B C E w fallback) left right leftGrid rightGrid).1=true ↔
      ∃i t,At A B C E w left right i t ∧ i<leftGrid ∧ rightGrid<t := by
  unfold query
  rw [NearIndex.scan_correct]
  simp only [row_correct A B C E w fallback left right rightGrid _ hr]
  constructor
  · rintro ⟨i,hli,hig,t,hgt,h⟩
    exact ⟨i,t,h,by omega,hgt⟩
  · rintro ⟨i,t,h,hig,hgt⟩
    exact ⟨i,h.1,by have hh:=h.1; omega,t,hgt,h⟩

theorem at_iff_cuts (A B C E : DFA (Fin σ)) (w : Word (Fin σ))
    (left right i t : Nat) (hr : right≤w.length) :
    At A B C E w left right i t ↔
      ∃a j,left≤i ∧ i≤a ∧ a≤j ∧ j≤t ∧ t≤right ∧
        slice w i a=slice w j t ∧ A.accepts (slice w left i) ∧
        B.accepts (slice w i a) ∧ C.accepts (slice w a j) ∧ E.accepts (slice w t right) := by
  constructor
  · rintro ⟨hli,hit,htr,hA,hE,L,hLen,he,hB,hC⟩
    exact ⟨i+L,t-L,hli,by omega,by omega,by omega,htr,he,hA,hB,hC,hE⟩
  · rintro ⟨a,j,hli,hia,haj,hjt,htr,he,hA,hB,hC,hE⟩
    have hlen:=congrArg List.length he
    rw [OuterColumn.slice_length w i a hia (by omega),OuterColumn.slice_length w j t hjt (by omega)] at hlen
    have ha : i+(a-i)=a := by omega
    have hj : t-(a-i)=j := by omega
    refine ⟨hli,by omega,htr,hA,hE,a-i,by omega,?_,?_,?_⟩
    · simpa only [ha,hj] using he
    · simpa only [ha] using hB
    · simpa only [ha,hj] using hC

theorem oneUse_iff (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (left right : Nat) :
    Spec.oneUseRange A B C E w left right ↔
      left≤right ∧ right≤w.length ∧ ∃i t,At A B C E w left right i t := by
  constructor
  · rintro ⟨hl,hr,i,a,j,t,hli,hia,haj,hjt,htr,he,hA,hB,hC,hE⟩
    exact ⟨hl,hr,i,t,(at_iff_cuts A B C E w left right i t hr).mpr
      ⟨a,j,hli,hia,haj,hjt,htr,he,hA,hB,hC,hE⟩⟩
  · rintro ⟨hl,hr,i,t,h⟩
    obtain ⟨a,j,hc⟩:=(at_iff_cuts A B C E w left right i t hr).mp h
    exact ⟨hl,hr,i,a,j,t,hc⟩

theorem query_iff_cuts (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right leftGrid rightGrid : Nat) (hr : right≤w.length) :
    (query (build A B C E w fallback) left right leftGrid rightGrid).1=true ↔
      ∃i a j t,left≤i ∧ i≤a ∧ a≤j ∧ j≤t ∧ t≤right ∧ i<leftGrid ∧ rightGrid<t ∧
        slice w i a=slice w j t ∧ A.accepts (slice w left i) ∧
        B.accepts (slice w i a) ∧ C.accepts (slice w a j) ∧ E.accepts (slice w t right) := by
  rw [query_correct A B C E w fallback left right leftGrid rightGrid hr]
  constructor
  · rintro ⟨i,t,h,hig,hgt⟩
    obtain ⟨a,j,hli,hia,haj,hjt,htr,hrest⟩:=(at_iff_cuts A B C E w left right i t hr).mp h
    exact ⟨i,a,j,t,hli,hia,haj,hjt,htr,hig,hgt,hrest⟩
  · rintro ⟨i,a,j,t,hli,hia,haj,hjt,htr,hig,hgt,hrest⟩
    exact ⟨i,t,(at_iff_cuts A B C E w left right i t hr).mpr
      ⟨a,j,hli,hia,haj,hjt,htr,hrest⟩,hig,hgt⟩

end REWB.OneUseRange.Border
