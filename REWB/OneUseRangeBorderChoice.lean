import REWB.OneUseRangeBorderQuery

/-! The existing constant-work AP clipping is compatible with an A
prefix beginning at `base` whenever the target cutoff forces every
remaining source position to be at least `base`. -/
namespace REWB.OneUseRange.Border.Regular
open REWB.BoundaryBorder REWB.BoundaryBorder.Regular REWB.Spec
variable {α : Type}

theorem source_bound (base a j r p : Nat) (hbase : base≤a-(r-j))
    (ht : endAt j a p≤r) : base≤p := by
  unfold endAt at ht
  omega

def choice (A B E : DFA α) (ai : BoundaryApplication.Range.Index A)
    (bi : BoundaryApplication.Range.Index B) (ei : BoundaryApplication.Range.Index E)
    (c : Choice) (base a j r : Nat) : Bool×Nat :=
  if r<j then (false,1)
  else match c with
  | .empty => (false,2)
  | .point p =>
      if p≤a ∧ endAt j a p≤r then
        let out:=point A B E ai bi ei base p a j r
        (out.1,out.2+8)
      else (false,6)
  | .progression first q lo hi =>
      let aligned:=align first q (max lo (a-(r-j))) (min hi a)
      match aligned.1 with
      | none => (false,aligned.2+8)
      | some (start,m) =>
          let out:=query A B E ai bi ei base start q m a j r
          (out.1,aligned.2+out.2+10)

theorem choice_correct (A B E : DFA α) (w : Word α) (fallback : α) (c : Choice) (base a j r : Nat)
    (hbase : base≤a-(r-j)) (hs : Supported (ArrayText.read w.toArray fallback) a j c)
    (ha : a≤w.length) (hr : r≤w.length) :
    (choice A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) c base a j r).1=true ↔
        ∃p,c.Holds p ∧ p≤a ∧ endAt j a p≤r ∧ Predicate A B E w base p a j r := by
  by_cases hj : r<j
  · rw [choice.eq_def,if_pos hj]
    simp only [Bool.false_eq_true,false_iff]
    rintro ⟨p,_,_,hp,_⟩
    unfold endAt at hp
    omega
  · have hjr : j≤r := by omega
    cases c with
    | empty =>
      simp only [choice,if_neg hj,Choice.Holds,false_and,exists_false]
      decide
    | point p =>
      by_cases hp : p≤a ∧ endAt j a p≤r
      · simp only [choice,if_neg hj,if_pos hp,Choice.Holds,exists_eq_left]
        rw [point_correct A B E w base p a j r (source_bound base a j r p hbase hp.2) hp.1 ha hp.2 hr]
        exact ⟨fun hh=>⟨hp.1,hp.2,hh⟩,fun hh=>hh.2.2⟩
      · simp only [choice,if_neg hj,if_neg hp,Choice.Holds,exists_eq_left,
          Bool.false_eq_true,false_iff]
        intro hh
        exact hp ⟨hh.1,hh.2.1⟩
    | progression first q lo hi =>
      have hq : 0<q := hs.1
      cases he : (align first q (max lo (a-(r-j))) (min hi a)).1 with
      | none =>
        simp only [choice,if_neg hj,he,Bool.false_eq_true,false_iff]
        rintro ⟨p,hp,hpa,hpr,_⟩
        have hm:=(clip_member first q lo hi a j r p hjr).mpr ⟨hp,hpa,hpr⟩
        obtain ⟨start,m,hh,_⟩:=(align_correct first q _ _ hq p).mp hm
        rw [he] at hh
        contradiction
      | some pair =>
        rcases pair with ⟨start,m⟩
        have hg:=aligned_geometry w fallback first q lo hi a j r start m hs hjr ha hr he
        have hc:=query_correct A B E w fallback base start q m a j r (source_bound base a j r start hbase hg.2.1) hg.1 ha hg.2.1 hr hg.2.2
        simp only [choice,if_neg hj,he]
        rw [hc]
        constructor
        · rintro ⟨k,hk,hpred⟩
          have hp:=(align_member first q _ _ start m (start+k*q) he).mpr ⟨k,hk,rfl⟩
          have hh:=(clip_member first q lo hi a j r _ hjr).mp hp
          exact ⟨start+k*q,hh.1,hh.2.1,hh.2.2,hpred⟩
        · rintro ⟨p,hp,hpa,hpr,hpred⟩
          have hclip:=(clip_member first q lo hi a j r p hjr).mpr ⟨hp,hpa,hpr⟩
          obtain ⟨k,hk,rfl⟩:=(align_member first q _ _ start m p he).mp hclip
          exact ⟨k,hk,hpred⟩

def choiceBudget (A B E : DFA α) (n : Nat) : Nat := denseBudget A B E n+30

theorem choice_work (A B E : DFA α) (w : Word α) (fallback : α) (c : Choice) (base a j r : Nat)
    (hbase : base≤a-(r-j)) (hs : Supported (ArrayText.read w.toArray fallback) a j c)
    (ha : a≤w.length) (hr : r≤w.length) :
    (choice A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) c base a j r).2≤choiceBudget A B E w.length := by
  by_cases hj : r<j
  · simp only [choice.eq_def,if_pos hj,choiceBudget]; omega
  · have hjr : j≤r := by omega
    cases c with
    | empty => simp only [choice,if_neg hj,choiceBudget]; omega
    | point p =>
      by_cases hp : p≤a ∧ endAt j a p≤r
      · have hw:=point_work A B E w base p a j r (source_bound base a j r p hbase hp.2) hp.1 ha hp.2 hr
        simp only [choice,if_neg hj,if_pos hp,choiceBudget,denseBudget]
        omega
      · simp only [choice,if_neg hj,if_neg hp,choiceBudget]; omega
    | progression first q lo hi =>
      have hw:=align_work first q (max lo (a-(r-j))) (min hi a)
      cases he : (align first q (max lo (a-(r-j))) (min hi a)).1 with
      | none => simp only [choice,if_neg hj,he,choiceBudget]; omega
      | some pair =>
        rcases pair with ⟨start,m⟩
        have hg:=aligned_geometry w fallback first q lo hi a j r start m hs hjr ha hr he
        have hq:=query_work A B E w fallback base start q m a j r (source_bound base a j r start hbase hg.2.1) hg.1 ha hg.2.1 hr hg.2.2
        simp only [choice,if_neg hj,he,choiceBudget]
        omega


end REWB.OneUseRange.Border.Regular
