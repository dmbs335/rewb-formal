import REWB.MaskedRunDiscovery
import REWB.MaskedEventBudget

/-! Discovery coverage at completed occurrence-set merges. Completeness
always refers to all bounded text occurrences, independently of masks.
The tree lemmas concern the existing concrete merge schedule; attaching
complete substring labels to a constructed suffix tree is separate. -/
namespace REWB.MaskedRunDiscovery
open REWB.Periodic REWB.RunGeometry REWB.LCEIndex
open REWB.MaskedEventBudget
variable {α : Type} {σ : Nat}

def Occurs (f : Nat→α) (n base L k : Nat) : Prop :=
  k+L≤n ∧ segment f k L=segment f base L

def Complete (f : Nat→α) (n base L : Nat) (xs : List Nat) : Prop :=
  ∀ k,k∈xs ↔ Occurs f n base L k

def Adjacent (xs : List Nat) (i j : Nat) : Prop :=
  i∈xs ∧ j∈xs ∧ i<j ∧ ∀ k,k∈xs→i<k→k<j→False

/-- Equal-depth binary refinement nodes are incomplete prefix classes.
Only the root or a strict depth increase may finish a full class. The
semantic `Complete` certificate is still required by correctness. -/
def classBoundary (parentDepth : Option Nat) (depth : Nat) : Bool :=
  match parentDepth with
  | none => true
  | some p => decide (p<depth)

def discoverClass (forward backward : RankIndex.Index) (n i j depth : Nat)
    (parentDepth : Option Nat) : Option Bounds×Nat :=
  if classBoundary parentDepth depth then
    let r:=discover forward backward n i j depth
    (r.1,r.2+2)
  else (none,2)

theorem equal_depth_skipped (forward backward : RankIndex.Index) (n i j depth : Nat) :
    discoverClass forward backward n i j depth (some depth)=(none,2) := by
  simp only [discoverClass,classBoundary,Nat.lt_irrefl,decide_false,Bool.false_eq_true,if_false]

theorem discoverClass_work (f : Nat→Fin σ) (n i j depth : Nat) (parentDepth : Option Nat) :
    (discoverClass (prepare f n) (prepareReverse f n) n i j depth parentDepth).2≤
      26*(n.log2+1)+16 := by
  have hh:=discover_work f n i j depth
  simp only [discoverClass]
  split <;> omega

theorem adjacent_subset (xs ys : List Nat) (i j : Nat) (ha : Adjacent ys i j)
    (hsub : ∀ k,k∈xs→k∈ys) (hi : i∈xs) (hj : j∈xs) : Adjacent xs i j :=
  ⟨hi,hj,ha.2.2.1,fun k hk hik hkj=>ha.2.2.2 k (hsub k hk) hik hkj⟩

theorem complete_consecutive (f : Nat→α) (n base L : Nat) (xs : List Nat) (i j : Nat)
    (hfull : Complete f n base L xs) (ha : Adjacent xs i j) :
    Consecutive (shift f i) L (j-i) := by
  have hi:=(hfull i).mp ha.1
  have hj:=(hfull j).mp ha.2.1
  have hij:=ha.2.2.1
  have he : segment f i L=segment f j L := hi.2.trans hj.2.symm
  refine ⟨?_,?_⟩
  · intro a ha'
    have hh:=(segment_eq_points f i j L).mp he a ha'
    simpa only [shift,show i+(a+(j-i))=j+a by omega] using hh
  · intro s hs hsj hcopy
    have hnew : Occurs f n base L (i+s) := by
      refine ⟨by have hh:=hj.1; omega,?_⟩
      apply Eq.trans _ hi.2
      apply (segment_eq_points f (i+s) i L).mpr
      intro a ha'
      have hh:=hcopy a ha'
      simpa only [shift,show i+(a+s)=i+s+a by omega] using hh.symm
    exact ha.2.2.2 (i+s) ((hfull (i+s)).mpr hnew) (by omega) (by omega)

theorem complete_discovery (f : Nat→Fin σ) (n base L : Nat) (xs : List Nat) (i j : Nat)
    (hfull : Complete f n base L xs) (ha : Adjacent xs i j) (hdense : 2*(j-i)≤L) :
    ∃ R,(discover (prepare f n) (prepareReverse f n) n i j L).1=some R ∧
      R.Valid f n ∧ R.period=j-i ∧ R.lo≤i ∧ j+L≤R.hi ∧
      3*R.period≤R.hi-R.lo := by
  have hj:=(hfull j).mp ha.2.1
  have hij:=ha.2.2.1
  have he : i+(j-i)=j := by omega
  have hh:=discover_dense f n i L (j-i) (by omega) hdense (by have h:=hj.1; omega)
    (complete_consecutive f n base L xs i j hfull ha)
  simpa only [he] using hh

/-- A surviving later adjacency is still consecutive at an earlier
completed coexistence node. Longer represented words preserve density. -/
theorem completed_coexistence_discovery (f : Nat→Fin σ) (n base H L : Nat)
    (completed later : List Nat) (i j : Nat)
    (hfull : Complete f n base H completed) (ha : Adjacent later i j)
    (hsub : ∀k,k∈completed→k∈later) (hi : i∈completed) (hj : j∈completed)
    (hLH : L≤H) (hdense : 2*(j-i)≤L) :
    ∃ R,(discover (prepare f n) (prepareReverse f n) n i j H).1=some R ∧
      R.Valid f n ∧ R.period=j-i ∧ R.lo≤i ∧ j+H≤R.hi ∧
      3*R.period≤R.hi-R.lo :=
  complete_discovery f n base H completed i j hfull
    (adjacent_subset completed later i j ha hsub hi hj) (by omega)

theorem completed_class_discovery (f : Nat→Fin σ) (n base H L : Nat)
    (completed later : List Nat) (i j : Nat) (parentDepth : Option Nat)
    (hgate : classBoundary parentDepth H=true)
    (hfull : Complete f n base H completed) (ha : Adjacent later i j)
    (hsub : ∀k,k∈completed→k∈later) (hi : i∈completed) (hj : j∈completed)
    (hLH : L≤H) (hdense : 2*(j-i)≤L) :
    ∃ R,(discoverClass (prepare f n) (prepareReverse f n) n i j H parentDepth).1=some R ∧
      R.Valid f n ∧ R.period=j-i ∧ R.lo≤i ∧ j+H≤R.hi ∧
      3*R.period≤R.hi-R.lo := by
  obtain ⟨R,hr,hrest⟩:=completed_coexistence_discovery f n base H L completed later i j
    hfull ha hsub hi hj hLH hdense
  exact ⟨R,by simpa only [discoverClass,hgate,if_true] using hr,hrest⟩

end REWB.MaskedRunDiscovery
