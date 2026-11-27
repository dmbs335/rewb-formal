import REWB.LCEIndex
import REWB.GlobalCoverage

/-! Grid equality strips from concrete forward/backward rank indexes.
    The two linear reference extension scans are replaced by logarithmic
    longest-common-extension queries. Duplicate strips may be returned;
    they are charged to the explicit probe list. Minimum-period discovery
    and the residual matching queries are separate operations. -/
namespace REWB.IndexedGrid
open REWB.Periodic REWB.LCEIndex
variable {α : Type} {σ : Nat}

theorem lcs_left [DecidableEq α] (f : Nat→α) (i j B : Nat)
    (hij : i≤j) (hb : IsLCS f i j B) :
    i-B=GridCoverage.regionLeft f (j-i) i := by
  let l := GridCoverage.regionLeft f (j-i) i
  have hs := RunExtension.left_spec f (j-i) i
  change l≤i ∧ (∀ a,l≤a→a<i→f a=f (a+(j-i))) ∧
    (l=0 ∨ f (l-1)≠f (l-1+(j-i))) at hs
  have hB := hb.1.1
  have href : SuffixAgree f i j (i-l) := by
    refine ⟨by omega,by omega,?_⟩
    apply (segment_eq_points f (i-(i-l)) (j-(i-l)) (i-l)).mpr
    intro a ha
    have he := hs.2.1 (l+a) (by omega) (by omega)
    simpa only [show i-(i-l)=l by omega,
      show j-(i-l)+a=l+a+(j-i) by omega] using he
  have hmax := hb.2 (i-l) href
  have hle : l≤i-B := by
    by_cases hn : l≤i-B
    · exact hn
    · have hpt := (segment_eq_points f (i-B) (j-B) B).mp hb.1.2.2
        (l-1-(i-B)) (by omega)
      have he : f (l-1)=f (l-1+(j-i)) := by
        simpa only [show i-B+(l-1-(i-B))=l-1 by omega,
          show j-B+(l-1-(i-B))=l-1+(j-i) by omega] using hpt
      rcases hs.2.2 with hz|hbad
      · omega
      · exact False.elim (hbad he)
  change i-B=l
  omega

theorem lce_end [DecidableEq α] (f : Nat→α) (n i j F : Nat)
    (hij : i≤j) (hjn : j≤n) (hf : IsLCE f n i j F) :
    i+F=GridCoverage.regionEnd f n (j-i) i := by
  let r := GridCoverage.regionEnd f n (j-i) i
  have hs := RunExtension.right_spec f (j-i) (n-(j-i)-i) i
  change i≤r ∧ r≤i+(n-(j-i)-i) ∧ (∀ a,i≤a→a<r→f a=f (a+(j-i))) ∧
    (r=i+(n-(j-i)-i) ∨ f r≠f (r+(j-i))) at hs
  have hbound := hf.1.2.1
  have href : Agree f n i j (r-i) := by
    refine ⟨by omega,by omega,?_⟩
    apply (segment_eq_points f i j (r-i)).mpr
    intro a ha
    have he := hs.2.2.1 (i+a) (by omega) (by omega)
    simpa only [show i+a+(j-i)=j+a by omega] using he
  have hmax := hf.2 (r-i) href
  have hle : i+F≤r := by
    by_cases hn : i+F≤r
    · exact hn
    · have hpt := (segment_eq_points f i j F).mp hf.1.2.2 (r-i) (by omega)
      have he : f r=f (r+(j-i)) := by
        simpa only [show i+(r-i)=r by omega,show j+(r-i)=r+(j-i) by omega] using hpt
      rcases hs.2.2.2 with hz|hbad
      · omega
      · exact False.elim (hbad he)
  change i+F=r
  omega

structure Strip where
  lo : Nat
  hi : Nat
  distance : Nat
  deriving Repr, DecidableEq

def extend (forward backward : RankIndex.Index) (n i j : Nat) : Strip×Nat :=
  let a := lceMeasured forward n i j
  let b := lcsMeasured backward n i j
  (⟨i-b.length,i+a.length,j-i⟩,a.countedWork+b.countedWork)

theorem extend_eq (f : Nat→Fin σ) (n i j : Nat) (hij : i≤j) (hjn : j≤n) :
    (extend (prepare f n) (prepareReverse f n) n i j).1=
      ⟨GridCoverage.regionLeft f (j-i) i,GridCoverage.regionEnd f n (j-i) i,j-i⟩ := by
  simp only [extend]
  rw [lcs_left f i j _ hij (lcsMeasured_correct f n i j (by omega) hjn),
    lce_end f n i j _ hij hjn (lceMeasured_correct f n i j (by omega) hjn)]

theorem extend_work (f : Nat→Fin σ) (n i j : Nat) :
    (extend (prepare f n) (prepareReverse f n) n i j).2≤26*(n.log2+1)+2 := by
  have ha := lceMeasured_work (prepare f n) n i j
  have hb := lcsMeasured_work (prepareReverse f n) n i j
  simp only [extend]
  omega

def candidate (forward backward : RankIndex.Index) (n : Nat) (ij : Nat×Nat) : Option Strip×Nat :=
  if ij.1<ij.2 ∧ ij.2≤n then
    let r := extend forward backward n ij.1 ij.2
    (if ij.1<r.1.hi then some r.1 else none,r.2)
  else (none,0)

theorem candidate_work (f : Nat→Fin σ) (n : Nat) (ij : Nat×Nat) :
    (candidate (prepare f n) (prepareReverse f n) n ij).2≤26*(n.log2+1)+2 := by
  unfold candidate
  split
  · exact extend_work f n ij.1 ij.2
  · simp

theorem candidate_sound (f : Nat→Fin σ) (n : Nat) (ij : Nat×Nat) (R : Strip)
    (h : (candidate (prepare f n) (prepareReverse f n) n ij).1=some R) :
    GlobalCoverage.MaximalStrip f n R.lo R.hi R.distance := by
  unfold candidate at h
  split at h
  next hv =>
    dsimp only at h
    rw [extend_eq f n ij.1 ij.2 (by omega) hv.2] at h
    dsimp only at h
    split at h
    next hpos =>
      cases h
      dsimp only [GlobalCoverage.MaximalStrip]
      have hl := RunExtension.left_spec f (ij.2-ij.1) ij.1
      have hr := RunExtension.right_spec f (ij.2-ij.1) (n-(ij.2-ij.1)-ij.1) ij.1
      simp only [GridCoverage.regionLeft,GridCoverage.regionEnd] at hpos ⊢
      refine ⟨by omega,by omega,by omega,?_,hl.2.2,?_⟩
      · intro a ha hb
        by_cases hlt : a<ij.1
        · exact hl.2.1 a ha hlt
        · exact hr.2.2.1 a (by omega) hb
      · rcases hr.2.2.2 with hend|hbad
        · exact Or.inl (by omega)
        · exact Or.inr hbad
    next hn => contradiction
  next hn => contradiction

theorem candidate_contains (f : Nat→Fin σ) (n i j a L : Nat)
    (hreg : GridCoverage.EqualityRegion f n a L (j-i))
    (ha : a≤i) (hi : i<a+L) (hij : i<j) :
    ∃ R,(candidate (prepare f n) (prepareReverse f n) n (i,j)).1=some R ∧
      R.lo≤a ∧ a+L≤R.hi ∧ R.distance=j-i := by
  have hn := hreg.2.1
  have hjn : j≤n := by omega
  have hc := GridCoverage.extend_covers f n a L (j-i) i hreg ha hi
  unfold candidate
  rw [if_pos (show i<j ∧ j≤n from ⟨hij,hjn⟩)]
  dsimp only
  rw [extend_eq f n i j (by omega) hjn]
  dsimp only
  rw [if_pos (by omega)]
  exact ⟨_,rfl,hc.1,hc.2,rfl⟩

structure Batch where
  strips : List Strip := []
  queryWork : Nat := 0
  probes : Nat := 0
  deriving Repr

def collect (forward backward : RankIndex.Index) (n : Nat) : List (Nat×Nat)→Batch
  | [] => {}
  | x::xs =>
    let a := candidate forward backward n x
    let r := collect forward backward n xs
    ⟨match a.1 with | none=>r.strips | some R=>R::r.strips,
      a.2+r.queryWork,r.probes+1⟩

def collectTR (forward backward : RankIndex.Index) (n : Nat) (xs : List (Nat×Nat)) : Batch :=
  xs.foldr (fun x r=>
    let a:=candidate forward backward n x
    ⟨match a.1 with | none=>r.strips | some R=>R::r.strips,
      a.2+r.queryWork,r.probes+1⟩) {}

@[csimp] theorem collect_eq_collectTR : @collect=@collectTR := by
  funext forward backward n xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [collect,collectTR,List.foldr_cons] at ih ⊢
    rw [ih]

theorem collect_mem (forward backward : RankIndex.Index) (n : Nat)
    (xs : List (Nat×Nat)) (R : Strip) :
    R∈(collect forward backward n xs).strips ↔
      ∃ x∈xs,(candidate forward backward n x).1=some R := by
  induction xs with
  | nil => simp [collect]
  | cons x xs ih =>
    simp only [collect]
    cases h : (candidate forward backward n x).1 with
    | none => simp [h,ih]
    | some v =>
      simp only [h,List.mem_cons,ih]
      constructor
      · rintro (he|ht)
        · subst R
          exact ⟨x,Or.inl rfl,h⟩
        · obtain ⟨y,hy,hc⟩ := ht
          exact ⟨y,Or.inr hy,hc⟩
      · rintro ⟨y,(he|ht),hc⟩
        · subst y
          rw [h] at hc
          exact Or.inl (Option.some.inj hc).symm
        · exact Or.inr ⟨y,ht,hc⟩

theorem collect_counts (f : Nat→Fin σ) (n : Nat) (xs : List (Nat×Nat)) :
    (collect (prepare f n) (prepareReverse f n) n xs).probes=xs.length ∧
    (collect (prepare f n) (prepareReverse f n) n xs).strips.length≤xs.length ∧
    (collect (prepare f n) (prepareReverse f n) n xs).queryWork≤(26*(n.log2+1)+2)*xs.length := by
  induction xs with
  | nil => exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩
  | cons x xs ih =>
    have hc := candidate_work f n x
    refine ⟨?_,?_,?_⟩
    · change (collect (prepare f n) (prepareReverse f n) n xs).probes+1=xs.length+1
      omega
    · simp only [collect]
      cases he : (candidate (prepare f n) (prepareReverse f n) n x).1 <;>
        simp only [he,List.length_cons] <;> omega
    · change (candidate (prepare f n) (prepareReverse f n) n x).2+
        (collect (prepare f n) (prepareReverse f n) n xs).queryWork≤
          (26*(n.log2+1)+2)*(xs.length+1)
      rw [Nat.mul_succ (26*(n.log2+1)+2) xs.length]
      omega

structure Result extends Batch where
  preparation : Nat

/-- The two indexes are shared by every generated grid probe. -/
def generate (f : Nat→Fin σ) (n s : Nat) : Result :=
  let F:=prepare f n
  let B:=prepareReverse f n
  ⟨collect F B n (GridCoverage.probes n s),F.countedWork+B.countedWork⟩

theorem generate_sound (f : Nat→Fin σ) (n s : Nat) (R : Strip)
    (h : R∈(generate f n s).strips) : GlobalCoverage.MaximalStrip f n R.lo R.hi R.distance := by
  obtain ⟨ij,_,hc⟩ := (collect_mem (prepare f n) (prepareReverse f n) n (GridCoverage.probes n s) R).mp h
  exact candidate_sound f n ij R hc

theorem generate_complete (f : Nat→Fin σ) (n s p e k : Nat)
    (hs : 0<s) (hc : GlobalCoverage.Copy f n p e k) (hlong : s≤e-p) :
    ∃ R,R∈(generate f n s).strips ∧ R.lo≤p ∧ e≤R.hi ∧ R.distance=k-p := by
  obtain ⟨i,hmem,hpi,hie,_⟩ := GlobalCoverage.long_copy_seed f n s p e k hc hs hlong
  have hp := hc.positive
  have hk := hc.separated
  have heq : i+(k-p)-i=k-p := by omega
  have hreg := GlobalCoverage.copy_region f n p e k hc
  rw [← heq] at hreg
  obtain ⟨R,hr,ha,hb,hd⟩ := candidate_contains f n i (i+(k-p)) p (e-p)
    hreg hpi (by omega) (by omega)
  refine ⟨R,(collect_mem _ _ n _ R).mpr ⟨_,hmem,hr⟩,ha,by omega,?_⟩
  rwa [heq] at hd

theorem generate_counts (f : Nat→Fin σ) (n s : Nat) :
    (generate f n s).probes=(n/s+1)*(n+1) ∧
    (generate f n s).strips.length≤(n/s+1)*(n+1) ∧
    (generate f n s).queryWork≤(26*(n.log2+1)+2)*((n/s+1)*(n+1)) ∧
    (generate f n s).preparation≤2*((n+1)*((n.log2+1)*(16*RankIndex.width σ n+4)+1)) := by
  have hc := collect_counts f n (GridCoverage.probes n s)
  rw [GridCoverage.probes_length] at hc
  have hp := prepare_work f n
  have hb := prepareReverse_work f n
  exact ⟨hc.1,hc.2.1,hc.2.2,by change (prepare f n).countedWork+(prepareReverse f n).countedWork≤_; omega⟩

end REWB.IndexedGrid
