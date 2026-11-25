import REWB.LCEIndex
import REWB.RankIndexDivisors
import REWB.GlobalCoverage

/-! Determine the minimum period of an overlapping maximal equality
strip by testing its displacement's precomputed divisors. Each test is
one exact indexed LCE query; the text span is never scanned. -/
namespace REWB.RankIndexPeriod
open REWB.Periodic REWB.RunGeometry REWB.LCEIndex REWB.RankIndex
variable {α : Type} {σ : Nat}

theorem period_iff_equal (f : Nat→α) (l r q : Nat) :
    Period (shift f l) (r-l) q ↔
      segment f l (r-l-q)=segment f (l+q) (r-l-q) := by
  constructor
  · intro h
    apply (segment_eq_points f l (l+q) (r-l-q)).mpr
    intro i hi
    have he := h i (by omega)
    simpa only [shift,Nat.add_assoc,Nat.add_comm q i] using he
  · intro h i hi
    have he := (segment_eq_points f l (l+q) (r-l-q)).mp h i (by omega)
    simpa only [shift,Nat.add_assoc,Nat.add_comm i q] using he

def test (I : Index) (n l r q : Nat) : Bool×Nat :=
  if 0<q ∧ q≤r-l then
    let a:=lceMeasured I n l (l+q)
    (decide (r-l-q≤a.length),a.countedWork+3)
  else (false,1)

theorem test_correct (f : Nat→Fin σ) (n l r q : Nat) (hlr : l≤r) (hrn : r≤n) :
    (test (prepare f n) n l r q).1=true ↔
      0<q ∧ q≤r-l ∧ Period (shift f l) (r-l) q := by
  by_cases hp : 0<q ∧ q≤r-l
  · rw [test,if_pos hp]
    simp only [decide_eq_true_eq]
    have hx := lceMeasured_correct f n l (l+q) (by omega) (by omega)
    constructor
    · intro hlen
      have he := agree_shorten f n l (l+q) _ (r-l-q) hx.1 hlen
      exact ⟨hp.1,hp.2,(period_iff_equal f l r q).mpr he.2.2⟩
    · rintro ⟨_,_,hP⟩
      exact hx.2 (r-l-q) ⟨by omega,by omega,(period_iff_equal f l r q).mp hP⟩
  · rw [test,if_neg hp]
    constructor
    · intro h; contradiction
    · rintro ⟨hq,hqr,_⟩
      exact False.elim (hp ⟨hq,hqr⟩)

theorem test_work (I : Index) (n l r q : Nat) :
    (test I n l r q).2≤13*(n.log2+1)+4 := by
  unfold test
  split
  · have hh:=lceMeasured_work I n l (l+q)
    change (lceMeasured I n l (l+q)).countedWork+3≤_
    omega
  · omega

/-- Tail-recursive minimum selection. The initial sentinel is larger
than the displacement; a true least period is guaranteed to replace it
in the overlapping-strip theorem below. -/
def selectGo (I : Index) (n l r : Nat) : List Nat→Nat→Nat→Nat×Nat
  | [],best,work => (best,work)
  | q::qs,best,work =>
    let t:=test I n l r q
    selectGo I n l r qs (if t.1 then min q best else best) (work+t.2+2)

theorem selectGo_le (I : Index) (n l r : Nat) (qs : List Nat) (best work : Nat) :
    (selectGo I n l r qs best work).1≤best := by
  induction qs generalizing best work with
  | nil => exact Nat.le_refl _
  | cons q qs ih =>
    rw [selectGo]
    have hh:=ih (if (test I n l r q).1 then min q best else best)
      (work+(test I n l r q).2+2)
    have hm : (if (test I n l r q).1 then min q best else best)≤best := by
      split
      · exact Nat.min_le_right _ _
      · exact Nat.le_refl _
    exact Nat.le_trans hh hm

theorem selectGo_member_le (I : Index) (n l r : Nat) (qs : List Nat)
    (best work q : Nat) (hq : q∈qs) (ht : (test I n l r q).1=true) :
    (selectGo I n l r qs best work).1≤q := by
  induction qs generalizing best work with
  | nil => simp at hq
  | cons a as ih =>
    rcases List.mem_cons.mp hq with he|hm
    · subst a
      rw [selectGo,ht,if_pos rfl]
      exact Nat.le_trans (selectGo_le I n l r as (min q best) _)
        (Nat.min_le_left _ _)
    · rw [selectGo]
      exact ih _ _ hm

theorem selectGo_origin (I : Index) (n l r : Nat) (qs : List Nat) (best work : Nat) :
    (selectGo I n l r qs best work).1=best ∨
      ∃ q,q∈qs ∧ (selectGo I n l r qs best work).1=q ∧ (test I n l r q).1=true := by
  induction qs generalizing best work with
  | nil => exact Or.inl rfl
  | cons q qs ih =>
    rw [selectGo]
    by_cases ht : (test I n l r q).1=true
    · simp only [ht,ite_true]
      rcases ih (min q best) (work+(test I n l r q).2+2) with he|⟨a,ha,he,hpass⟩
      · by_cases hqb : q≤best
        · exact Or.inr ⟨q,by simp,by simpa only [Nat.min_eq_left hqb] using he,ht⟩
        · exact Or.inl (by simpa only [Nat.min_eq_right (by omega : best≤q)] using he)
      · exact Or.inr ⟨a,by simp [ha],he,hpass⟩
    · have hf : (test I n l r q).1=false := by
        cases he : (test I n l r q).1
        · rfl
        · exact False.elim (ht he)
      simp only [hf,Bool.false_eq_true,if_false]
      rcases ih best (work+(test I n l r q).2+2) with he|⟨a,ha,he,hpass⟩
      · exact Or.inl he
      · exact Or.inr ⟨a,by simp [ha],he,hpass⟩

theorem selectGo_work (I : Index) (n l r : Nat) (qs : List Nat) (best work : Nat) :
    (selectGo I n l r qs best work).2≤work+qs.length*(13*(n.log2+1)+6) := by
  induction qs generalizing best work with
  | nil => simp [selectGo]
  | cons q qs ih =>
    rw [selectGo]
    have hh:=ih (if (test I n l r q).1 then min q best else best)
      (work+(test I n l r q).2+2)
    have ht:=test_work I n l r q
    rw [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem minimum_period (f : Nat→Fin σ) (n l r d p : Nat) (qs : List Nat)
    (hlr : l≤r) (hrn : r≤n) (hp : LeastPeriod (shift f l) (r-l) p)
    (hpr : p≤r-l) (hpd : p≤d) (hmem : p∈qs) :
    (selectGo (prepare f n) n l r qs (d+1) 0).1=p := by
  have ht := (test_correct f n l r p hlr hrn).mpr ⟨hp.1,hpr,hp.2.1⟩
  have hle := selectGo_member_le (prepare f n) n l r qs (d+1) 0 p hmem ht
  rcases selectGo_origin (prepare f n) n l r qs (d+1) 0 with he|⟨q,hq,he,htq⟩
  · omega
  · obtain ⟨hqp,hqr,hperiod⟩ := (test_correct f n l r q hlr hrn).mp htq
    have hge := hp.2.2 q hqp hperiod
    omega

def fromStrip (I : Index) (bs : Array (List Nat)) (n l r d : Nat) : Bounds×Nat :=
  let result:=selectGo I n l (r+d) (RankIndexDivisors.bucket bs d) (d+1) 0
  (⟨l,r+d,result.1⟩,result.2)

theorem fromStrip_lo (I : Index) (bs : Array (List Nat)) (n l r d : Nat) :
    (fromStrip I bs n l r d).1.lo=l := rfl

theorem fromStrip_hi (I : Index) (bs : Array (List Nat)) (n l r d : Nat) :
    (fromStrip I bs n l r d).1.hi=r+d := rfl

/-- Actual divisor buckets contain the least period forced by overlap;
the selected period is therefore the true least period of the maximal
run. No externally supplied minimum-period answer is required. -/
theorem fromStrip_spec (f : Nat→Fin σ) (n l r d : Nat)
    (hs : GlobalCoverage.MaximalStrip f n l r d) (ho : d≤r-l) :
    let R:=(fromStrip (prepare f n) (RankIndexDivisors.buckets n).1 n l r d).1
    R.Valid f n ∧ R.period∣d ∧ R.period≤d := by
  obtain ⟨R,hR,hl,hr,hdiv,hpd⟩ := GlobalCoverage.overlapping_run f n l r d hs ho
  have hmin := hR.2.2.2.1
  rw [hl,hr] at hmin
  have hmem : R.period∈RankIndexDivisors.bucket (RankIndexDivisors.buckets n).1 d := by
    apply (RankIndexDivisors.buckets_mem n d R.period).mpr
    exact ⟨hs.1,by have hh:=hs.2.2.1; omega,hmin.1,hdiv⟩
  have hper := minimum_period f n l (r+d) d R.period
    (RankIndexDivisors.bucket (RankIndexDivisors.buckets n).1 d)
    (by have hh:=hs.2.1; omega) hs.2.2.1 hmin (by omega) hpd hmem
  change Run f n l (r+d) _ ∧ _∣d ∧ _≤d
  simp only [fromStrip,hper]
  exact ⟨by simpa only [Bounds.Valid,hl,hr] using hR,hdiv,hpd⟩

theorem fromStrip_work (I : Index) (bs : Array (List Nat)) (n l r d : Nat) :
    (fromStrip I bs n l r d).2≤
      (RankIndexDivisors.bucket bs d).length*(13*(n.log2+1)+6) := by
  have hh:=selectGo_work I n l (r+d) (RankIndexDivisors.bucket bs d) (d+1) 0
  simpa only [fromStrip,Nat.zero_add] using hh

end REWB.RankIndexPeriod
