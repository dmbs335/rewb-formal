import REWB.BoundaryTrieKeys
import REWB.BoundaryTrieSearch

/-! Split a sorted descriptor interval by its first next-symbol class.
The common stem is computed once from its endpoints. Prefix convexity
then makes the next-symbol predicate monotone, so a measured binary
search replaces a scan of all keys in the interval. -/
namespace REWB.BoundaryTrie.Partition
variable {σ n : Nat} {ρ : Type}

def keyAt (xs : Array (Key n ρ)) (fallback : Key n ρ) (i : Nat) : Key n ρ :=
  xs[i]?.getD fallback

def Sorted (f : Nat→Fin σ) (xs : Array (Key n ρ)) (fallback : Key n ρ) : Prop :=
  ∀ i j,i≤j→j<xs.size→Key.ordered f (keyAt xs fallback i) (keyAt xs fallback j)

def readSymbol (text : Array (Fin σ)) (fallback : Fin σ)
    (a : Key text.size ρ) (d : Nat) : Nat×Nat :=
  if d<a.length then ((ArrayText.read text fallback (a.start+d)).val+1,4) else (0,1)

theorem readSymbol_value (text : Array (Fin σ)) (fallback : Fin σ)
    (a : Key text.size ρ) (d : Nat) :
    (readSymbol text fallback a d).1=Key.symbol (ArrayText.read text fallback) a d := by
  simp only [readSymbol,Key.symbol]
  split <;> rfl

theorem readSymbol_work (text : Array (Fin σ)) (fallback : Fin σ)
    (a : Key text.size ρ) (d : Nat) : (readSymbol text fallback a d).2≤4 := by
  simp only [readSymbol]
  split <;> simp only <;> decide

def probe (text : Array (Fin σ)) (fallback : Fin σ)
    (xs : Array (Key text.size ρ)) (defaultKey : Key text.size ρ) (d v i : Nat) : Bool×Nat :=
  let r:=readSymbol text fallback (keyAt xs defaultKey i) d
  (decide (r.1≤v),r.2+3)

theorem probe_value (text : Array (Fin σ)) (fallback : Fin σ)
    (xs : Array (Key text.size ρ)) (defaultKey : Key text.size ρ) (d v i : Nat) :
    (probe text fallback xs defaultKey d v i).1=true ↔
      Key.symbol (ArrayText.read text fallback) (keyAt xs defaultKey i) d≤v := by
  simp only [probe,decide_eq_true_eq,readSymbol_value]

theorem probe_work (text : Array (Fin σ)) (fallback : Fin σ)
    (xs : Array (Key text.size ρ)) (defaultKey : Key text.size ρ) (d v i : Nat) :
    (probe text fallback xs defaultKey d v i).2≤7 := by
  have hh:=readSymbol_work text fallback (keyAt xs defaultKey i) d
  simp only [probe]
  omega

structure Result where
  split : Nat
  depth : Nat
  work : Nat
  deriving Repr

def run (text : Array (Fin σ)) (fallback : Fin σ) (ranks : RankIndex.Index)
    (xs : Array (Key text.size ρ)) (defaultKey : Key text.size ρ) (lo hi : Nat) : Result :=
  let a:=keyAt xs defaultKey lo
  let b:=keyAt xs defaultKey (hi-1)
  let c:=commonPrefix ranks a b
  if a.length=c.1 ∧ b.length=c.1 then ⟨lo+1,c.1,c.2+8⟩
  else
    let v:=readSymbol text fallback a c.1
    let s:=Search.run (probe text fallback xs defaultKey c.1 v.1) lo hi
    ⟨s.split,c.1,c.2+v.2+s.work+10⟩

theorem run_work (text : Array (Fin σ)) (fallback : Fin σ) (ranks : RankIndex.Index)
    (xs : Array (Key text.size ρ)) (defaultKey : Key text.size ρ) (lo hi : Nat) :
    (run text fallback ranks xs defaultKey lo hi).work≤
      13*(text.size.log2+1)+15*((hi-lo).log2+1)+22 := by
  have hc:=commonPrefix_work ranks (keyAt xs defaultKey lo) (keyAt xs defaultKey (hi-1))
  simp only [run]
  split
  · dsimp only
    omega
  · dsimp only
    have hv:=readSymbol_work text fallback (keyAt xs defaultKey lo)
      (commonPrefix ranks (keyAt xs defaultKey lo) (keyAt xs defaultKey (hi-1))).1
    have hs:=Search.run_work
      (probe text fallback xs defaultKey
        (commonPrefix ranks (keyAt xs defaultKey lo) (keyAt xs defaultKey (hi-1))).1
        (readSymbol text fallback (keyAt xs defaultKey lo)
          (commonPrefix ranks (keyAt xs defaultKey lo) (keyAt xs defaultKey (hi-1))).1).1)
      7 (probe_work text fallback xs defaultKey _ _) lo hi
    omega

def Spec (f : Nat→Fin σ) (xs : Array (Key n ρ)) (fallback : Key n ρ)
    (lo hi : Nat) (r : Result) : Prop :=
  lo<r.split ∧ r.split<hi ∧
    Key.Exact f (keyAt xs fallback lo) (keyAt xs fallback (hi-1)) r.depth ∧
    (∀ i,lo≤i→i<hi→Key.Common f (keyAt xs fallback lo) (keyAt xs fallback i) r.depth) ∧
    (∀ i j,lo≤i→i<r.split→r.split≤j→j<hi→
      Key.Exact f (keyAt xs fallback i) (keyAt xs fallback j) r.depth)

theorem run_correct (text : Array (Fin σ)) (fallback : Fin σ)
    (xs : Array (Key text.size ρ)) (defaultKey : Key text.size ρ) (lo hi : Nat)
    (hlo : lo+1<hi) (hhi : hi≤xs.size)
    (hs : Sorted (ArrayText.read text fallback) xs defaultKey) :
    Spec (ArrayText.read text fallback) xs defaultKey lo hi
      (run text fallback (LCEIndex.prepare (ArrayText.read text fallback) text.size)
        xs defaultKey lo hi) := by
  let f:=ArrayText.read text fallback
  let ranks:=LCEIndex.prepare f text.size
  let a:=keyAt xs defaultKey lo
  let b:=keyAt xs defaultKey (hi-1)
  let d:=(commonPrefix ranks a b).1
  have hd : Key.Exact f a b d := commonPrefix_correct f a b
  have hcommon : ∀i,lo≤i→i<hi→Key.Common f a (keyAt xs defaultKey i) d := by
    intro i hil hir
    exact Key.common_between f a b (keyAt xs defaultKey i) d
      (hs lo i hil (by omega)) (hs i (hi-1) (by omega) (by omega)) hd.1
  have hpairs : ∀i j,lo≤i→i<hi→lo≤j→j<hi→
      Key.Common f (keyAt xs defaultKey i) (keyAt xs defaultKey j) d := by
    intro i j hil hir hjl hjr
    exact Key.common_trans f (keyAt xs defaultKey i) a (keyAt xs defaultKey j) d
      ((Key.common_symmetric _ _ _ _).mp (hcommon i hil hir)) (hcommon j hjl hjr)
  have hsymbols : ∀i j,lo≤i→i≤j→j<hi→
      Key.symbol f (keyAt xs defaultKey i) d≤Key.symbol f (keyAt xs defaultKey j) d := by
    intro i j hil hij hjr
    exact Key.symbol_order f _ _ d (hpairs i j hil (by omega) (by omega) hjr)
      (hs i j hij (by omega))
  simp only [run]
  change Spec f xs defaultKey lo hi
    (if a.length=d ∧ b.length=d then ⟨lo+1,d,(commonPrefix ranks a b).2+8⟩ else
      let v:=readSymbol text fallback a d
      let s:=Search.run (probe text fallback xs defaultKey d v.1) lo hi
      ⟨s.split,d,(commonPrefix ranks a b).2+v.2+s.work+10⟩)
  by_cases he : a.length=d ∧ b.length=d
  · rw [if_pos he]
    dsimp only [Spec]
    refine ⟨by omega,hlo,hd,hcommon,?_⟩
    intro i j hil hir hjl hjr
    have hilen : (keyAt xs defaultKey i).length=d := by
      have h1:=hcommon i hil (by omega)
      have h2:=hsymbols i (hi-1) hil (by omega) (by omega)
      change Key.symbol f (keyAt xs defaultKey i) d≤Key.symbol f b d at h2
      have hb : ¬d<b.length := by have hh:=he.2; omega
      simp only [Key.symbol,hb,if_false] at h2
      by_cases hlt : d<(keyAt xs defaultKey i).length
      · rw [if_pos hlt] at h2
        omega
      · have hh:=h1.2.1
        omega
    refine ⟨hpairs i j hil (by omega) (by omega) hjr,?_⟩
    intro e he'
    have hh:=he'.1
    omega
  · rw [if_neg he]
    let v:=(readSymbol text fallback a d).1
    let p:=probe text fallback xs defaultKey d v
    have hv : v=Key.symbol f a d := readSymbol_value text fallback a d
    have hp : Search.Prefix p lo hi := by
      intro i j hil hij hjr hj
      have hj':=(probe_value text fallback xs defaultKey d v j).mp hj
      exact (probe_value text fallback xs defaultKey d v i).mpr
        (Nat.le_trans (hsymbols i j hil hij hjr) hj')
    have hbne : Key.symbol f a d≠Key.symbol f b d :=
      Key.symbol_ne_of_exact f a b d hd (by omega)
    have hab : Key.symbol f a d<Key.symbol f b d := by
      have hh:=hsymbols lo (hi-1) (Nat.le_refl _) (by omega) (by omega)
      change Key.symbol f a d≤Key.symbol f b d at hh
      omega
    have hsplit:=Search.run_correct p lo hi (by omega) hp
    have htrue : (p lo).1=true := (probe_value text fallback xs defaultKey d v lo).mpr
      (by change Key.symbol f a d≤v; rw [hv]; exact Nat.le_refl _)
    have hfalse : ¬(p (hi-1)).1=true := by
      intro hh
      have hh':=(probe_value text fallback xs defaultKey d v (hi-1)).mp hh
      change Key.symbol f b d≤v at hh'
      omega
    have hl : lo<(Search.run p lo hi).split :=
      (hsplit.2.2 lo (Nat.le_refl _) (by omega)).mp htrue
    have hr : (Search.run p lo hi).split<hi := by
      have hh:=hsplit.2.2 (hi-1) (by omega) (by omega)
      have hbound:=hsplit.2.1
      have hnot : ¬hi-1<(Search.run p lo hi).split := fun h=>hfalse (hh.mpr h)
      omega
    dsimp only [Spec]
    refine ⟨hl,hr,hd,hcommon,?_⟩
    intro i j hil hir hjl hjr
    change i<(Search.run p lo hi).split at hir
    change (Search.run p lo hi).split≤j at hjl
    have hit:=(hsplit.2.2 i hil (by omega)).mpr hir
    have hjf : ¬(p j).1=true := by
      intro hh
      have hh':=(hsplit.2.2 j (by omega) hjr).mp hh
      omega
    have hi':=(probe_value text fallback xs defaultKey d v i).mp hit
    change Key.symbol f (keyAt xs defaultKey i) d≤v at hi'
    have hj' : ¬Key.symbol f (keyAt xs defaultKey j) d≤v := by
      intro hh
      exact hjf ((probe_value text fallback xs defaultKey d v j).mpr hh)
    exact Key.exact_of_symbol_ne f _ _ d
      (hpairs i j hil (by omega) (by omega) hjr) (by omega)

end REWB.BoundaryTrie.Partition
