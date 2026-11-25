import REWB.ClusterGeometry
import REWB.IndexedGrid

/-! Discover a cubic run from a surviving dense adjacency of the complete
occurrence set. The executable part performs one pair of indexed LCE/LCS
queries and uses the adjacency gap as its period. The least-period proof
uses true consecutiveness, not adjacency in a partial merge. No period
finder or divisor enumeration is executed by this construction. -/
namespace REWB.MaskedRunDiscovery
open REWB.Periodic REWB.RunGeometry REWB.LCEIndex
variable {α : Type} {σ : Nat}

/-- Existence of a least period is used solely in this proof. Dense true
consecutiveness forces that period to be the supplied positive gap. -/
theorem dense_least (f : Nat→α) (L delta : Nat) (hd : 0<delta)
    (hL : 2*delta≤L) (hc : Consecutive f L delta) : LeastPeriod f L delta := by
  have hP : Period f L delta := restrict (overlap_period f L delta hc.1) (by omega)
  obtain ⟨q,_,hq⟩:=GlobalCoverage.least_of_period f L delta hd hP
  have he:=dense_consecutive_gap hd hL hc hq
  rwa [he]

def bounds (S : IndexedGrid.Strip) : Bounds := ⟨S.lo,S.hi+S.distance,S.distance⟩

/-- A periodic superinterval containing a factor of the same least period
cannot acquire a smaller period. -/
theorem strip_least (f : Nat→α) (n : Nat) (S : IndexedGrid.Strip) (i L : Nat)
    (hs : GlobalCoverage.MaximalStrip f n S.lo S.hi S.distance)
    (hlo : S.lo≤i) (hhi : i+L≤S.hi+S.distance)
    (hmin : LeastPeriod (shift f i) L S.distance) :
    LeastPeriod (shift f S.lo) (S.hi+S.distance-S.lo) S.distance := by
  have hp : OnPeriod f S.lo (S.hi+S.distance) S.distance := by
    intro j hj hj'
    exact hs.2.2.2.1 j hj (by omega)
  refine ⟨hmin.1,(on_iff f S.lo (S.hi+S.distance) S.distance).mp hp,?_⟩
  intro q hq hQ
  have ho:=(on_iff f S.lo (S.hi+S.distance) q).mpr hQ
  have hr:=on_restrict f S.lo (S.hi+S.distance) q i (i+L) ho hlo hhi
  have hf:=(on_iff f i (i+L) q).mp hr
  rw [show i+L-i=L by omega] at hf
  exact hmin.2.2 q hq hf

theorem strip_valid (f : Nat→α) (n : Nat) (S : IndexedGrid.Strip) (i L : Nat)
    (hs : GlobalCoverage.MaximalStrip f n S.lo S.hi S.distance)
    (hoverlap : S.distance≤S.hi-S.lo) (hlo : S.lo≤i)
    (hhi : i+L≤S.hi+S.distance) (hmin : LeastPeriod (shift f i) L S.distance) :
    (bounds S).Valid f n := by
  have hlr:=hs.2.1
  have hn:=hs.2.2.1
  have hm:=strip_least f n S i L hs hlo hhi hmin
  have hm' : LeastPeriod (shift f S.lo) (S.hi-S.lo+S.distance) S.distance := by
    rwa [show S.hi-S.lo+S.distance=S.hi+S.distance-S.lo by omega]
  have he : S.lo+(S.hi-S.lo)=S.hi := by omega
  have hcopy : ∀j,j<S.hi-S.lo→f (S.lo+j)=f (S.lo+j+S.distance) := by
    intro j hj
    exact hs.2.2.2.1 (S.lo+j) (by omega) (by omega)
  have hr : S.lo+(S.hi-S.lo)+S.distance=n ∨
      f (S.lo+(S.hi-S.lo))≠f (S.lo+(S.hi-S.lo)+S.distance) := by
    simpa only [he] using hs.2.2.2.2.2
  have hv:=maximal_equality_run f n S.lo (S.hi-S.lo) S.distance S.distance
    hs.1 hoverlap (by omega) hcopy hs.2.2.2.2.1 hr hm'
  simpa only [bounds,Bounds.Valid,he] using hv.2

/-- The actual indexed candidate contains both equal copies and has the
adjacency gap as its least period. Its full interval is already cubic. -/
theorem candidate_dense (f : Nat→Fin σ) (n i L delta : Nat)
    (hd : 0<delta) (hL : 2*delta≤L) (hn : i+delta+L≤n)
    (hc : Consecutive (shift f i) L delta) :
    ∃ S,(IndexedGrid.candidate (prepare f n) (prepareReverse f n) n (i,i+delta)).1=some S ∧
      S.distance=delta ∧ S.lo≤i ∧ i+L≤S.hi ∧
      (bounds S).Valid f n ∧ 3*delta≤(bounds S).hi-(bounds S).lo := by
  have hreg : GridCoverage.EqualityRegion f n i L delta := by
    refine ⟨hd,by omega,?_⟩
    intro j hji hjL
    have he:=hc.1 (j-i) (by omega)
    simpa only [shift,show i+(j-i)=j by omega,
      show i+(j-i+delta)=j+delta by omega] using he
  have hdiff : i+delta-i=delta := by omega
  obtain ⟨S,hs,hl,hr,hdelta⟩:=IndexedGrid.candidate_contains f n i (i+delta) i L
    (by simpa only [hdiff] using hreg) (Nat.le_refl _) (by omega) (by omega)
  have hdist : S.distance=delta := by omega
  have hmax:=IndexedGrid.candidate_sound f n (i,i+delta) S hs
  have hm:=dense_least (shift f i) L delta hd hL hc
  have hm' : LeastPeriod (shift f i) L S.distance := by simpa only [hdist] using hm
  have hv:=strip_valid f n S i L hmax (by omega) hl (by omega) hm'
  refine ⟨S,hs,hdist,hl,hr,hv,?_⟩
  simp only [bounds]
  omega

/-- Twelve scalar slots cover the density/bounds guard, the existing
candidate guard, and constructing the returned interval. The variable
query work comes from the actual two indexed extension calls. -/
def discover (forward backward : RankIndex.Index) (n i j L : Nat) : Option Bounds×Nat :=
  if i<j ∧ j+L≤n ∧ 2*(j-i)≤L then
    let c:=IndexedGrid.candidate forward backward n (i,j)
    (c.1.map bounds,c.2+12)
  else (none,12)

theorem discover_work (f : Nat→Fin σ) (n i j L : Nat) :
    (discover (prepare f n) (prepareReverse f n) n i j L).2≤26*(n.log2+1)+14 := by
  have hc:=IndexedGrid.candidate_work f n (i,j)
  simp only [discover]
  split
  · omega
  · omega

theorem discover_dense (f : Nat→Fin σ) (n i L delta : Nat)
    (hd : 0<delta) (hL : 2*delta≤L) (hn : i+delta+L≤n)
    (hc : Consecutive (shift f i) L delta) :
    ∃ R,(discover (prepare f n) (prepareReverse f n) n i (i+delta) L).1=some R ∧
      R.Valid f n ∧ R.period=delta ∧ R.lo≤i ∧ i+delta+L≤R.hi ∧
      3*R.period≤R.hi-R.lo := by
  obtain ⟨S,hs,hdist,hl,hr,hv,hcubic⟩:=candidate_dense f n i L delta hd hL hn hc
  refine ⟨bounds S,?_,hv,hdist,hl,?_,?_⟩
  · simp only [discover,show i<i+delta ∧ i+delta+L≤n ∧ 2*(i+delta-i)≤L by omega,
      true_and,if_true,hs,Option.map_some]
    rfl
  · change i+delta+L≤S.hi+S.distance
    omega
  · simpa only [bounds,hdist] using hcubic

/-- The source's length-2*delta prefix is the primitive-square charge
available for later density-reset or run-span accounting. -/
theorem dense_primitive_square (f : Nat→α) (n i L delta : Nat)
    (hd : 0<delta) (hL : 2*delta≤L) (hn : i+delta+L≤n)
    (hc : Consecutive (shift f i) L delta) : PrimitiveSquare f n i delta := by
  have hm:=dense_least (shift f i) L delta hd hL hc
  have hs:=least_factor (shift f i) L delta 0 (2*delta) hm (Nat.le_refl _) (by omega)
  have he : shift (shift f i) 0=shift f i := by
    funext j
    simp only [shift,Nat.zero_add]
  rw [he] at hs
  exact ⟨by omega,hs⟩

end REWB.MaskedRunDiscovery
