import REWB.MaskedRunDiscoveryCoverage

/-! Reset geometry for local cluster anchors. All occurrence adjacency
is taken in the complete, unmasked class. A reset uses the current copy
length, and derives the two cursor bounds from actual neighboring copies.
The scheduling of resets during a changing traversal is separate. -/
namespace REWB.MaskedLocalAnchor
open REWB.Periodic REWB.MaskedRunDiscovery REWB.RunGeometry
variable {α : Type}

theorem period_copy (f : Nat→α) (i j L q : Nat)
    (he : segment f i L=segment f j L) (hp : Period (shift f i) L q) :
    Period (shift f j) L q := by
  have hh:=(segment_eq_points f i j L).mp he
  intro a ha
  change f (j+a)=f (j+(a+q))
  exact (hh a (by omega)).symm.trans ((hp a ha).trans (hh (a+q) ha))

theorem least_copy (f : Nat→α) (i j L q : Nat)
    (he : segment f i L=segment f j L) (hp : LeastPeriod (shift f i) L q) :
    LeastPeriod (shift f j) L q := by
  refine ⟨hp.1,period_copy f i j L q he hp.2.1,?_⟩
  intro p hp0 hP
  exact hp.2.2 p hp0 (period_copy f j i L p he.symm hP)

/-- A dense gap anywhere in a complete class fixes the minimum period
of every copy in that class, even across a sparse cluster boundary. -/
theorem complete_least (f : Nat→α) (n base L : Nat) (xs : List Nat)
    (hfull : Complete f n base L xs) (i j k : Nat)
    (ha : Adjacent xs i j) (hd : 2*(j-i)≤L) (hk : k∈xs) :
    LeastPeriod (shift f k) L (j-i) := by
  have hm:=dense_least (shift f i) L (j-i) (by have h:=ha.2.2.1; omega) hd
    (complete_consecutive f n base L xs i j hfull ha)
  have hi:=(hfull i).mp ha.1
  have hk':=(hfull k).mp hk
  exact least_copy f i k L (j-i) (hi.2.trans hk'.2.symm) hm

theorem sparse_gap (f : Nat→α) (n base L : Nat) (xs : List Nat)
    (hfull : Complete f n base L xs) (i j q : Nat)
    (ha : Adjacent xs i j) (hs : L<2*(j-i)) (hd : 2*q≤L)
    (hm : LeastPeriod (shift f i) L q) : i+L<j+q := by
  have hij:=ha.2.2.1
  have hq:=hm.1
  by_cases ho : j-i≤L
  · have hh:=separated_cluster_gap (by omega) ho (by omega)
      (complete_consecutive f n base L xs i j hfull ha) hm
    omega
  · omega

/-- Only the last member of a dense cluster can overlap the following
cluster after resetting its anchor to the actual copy length. -/
theorem reset_penultimate (f : Nat→α) (n base L : Nat) (xs : List Nat)
    (hfull : Complete f n base L xs) (p i j : Nat)
    (hp : Adjacent xs p i) (hd : 2*(i-p)≤L)
    (ha : Adjacent xs i j) (hs : L<2*(j-i)) : p+L<j := by
  have hm:=complete_least f n base L xs hfull p i i hp hd hp.2.1
  have hh:=sparse_gap f n base L xs hfull i j (i-p) ha hs hd hm
  have hpi:=hp.2.2.1
  omega

/-- An anchored jump at the last member skips at most the first member
of the next cluster. This includes both a dense next cluster and a
singleton next cluster followed by another sparse boundary. -/
theorem reset_following (f : Nat→α) (n base L : Nat) (xs : List Nat)
    (hfull : Complete f n base L xs) (i j k : Nat)
    (ha : Adjacent xs i j) (hs : L<2*(j-i))
    (hb : Adjacent xs j k) : i+L<k := by
  have hij:=ha.2.2.1
  have hjk:=hb.2.2.1
  by_cases hd : 2*(k-j)≤L
  · have hm:=complete_least f n base L xs hfull j k i hb hd ha.1
    have hh:=sparse_gap f n base L xs hfull i j (k-j) ha hs hd hm
    omega
  · omega

/-- The data retained by a local anchor. `copies` may be a single
cluster's membership list; its anchored word need not agree with a
different cluster beyond the current copy length. -/
structure Certificate (f : Nat→α) (n base L : Nat) (copies : List Nat)
    (last next : Nat) (previous following : Option Nat) (H : Nat) : Prop where
  current : L≤H
  words : ∀k,k∈copies→Occurs f n base H k
  lastBound : last+H≤n
  overlap : (next<last+H ↔ next<last+L)
  previousSafe : ∀p,previous=some p→p+H≤next
  followingSafe : ∀p,following=some p→last+H≤p

/-- A concrete reset H=L obtains every field from the full occurrence
class and the local dense/sparse adjacency certificates. Masks do not
appear in the premises. -/
theorem reset (f : Nat→α) (n base L : Nat) (xs copies : List Nat)
    (hfull : Complete f n base L xs) (hsub : ∀k,k∈copies→k∈xs)
    (last next : Nat) (previous following : Option Nat)
    (ha : Adjacent xs last next) (hs : L<2*(next-last))
    (hp : ∀p,previous=some p→Adjacent xs p last ∧ 2*(last-p)≤L)
    (hf : ∀p,following=some p→Adjacent xs next p) :
    Certificate f n base L copies last next previous following L := by
  refine ⟨Nat.le_refl _,fun k hk=>(hfull k).mp (hsub k hk),
    ((hfull last).mp ha.1).1,Iff.rfl,?_,?_⟩
  · intro p h
    have hh:=hp p h
    exact Nat.le_of_lt (reset_penultimate f n base L xs hfull p last next hh.1 hh.2 ha hs)
  · intro p h
    exact Nat.le_of_lt (reset_following f n base L xs hfull last next p ha hs (hf p h))

/-- At the end of text there is no outgoing overshoot and no successor
to skip. Every earlier cluster member's endpoint is also bounded. -/
theorem reset_terminal (f : Nat→α) (n base L : Nat) (xs copies : List Nat)
    (hfull : Complete f n base L xs) (hsub : ∀k,k∈copies→k∈xs)
    (last : Nat) (hlast : last∈xs) (previous : Option Nat)
    (hp : ∀p,previous=some p→p∈xs) :
    Certificate f n base L copies last n previous none L := by
  refine ⟨Nat.le_refl _,fun k hk=>(hfull k).mp (hsub k hk),
    ((hfull last).mp hlast).1,Iff.rfl,?_,?_⟩
  · intro p h
    exact ((hfull p).mp (hp p h)).1
  · intro p h
    cases h

/-- With fixed neighbors and unchanged overlap mode, shortening needs
no geometric reset. This preserves the existing anchored words. -/
theorem shorten (f : Nat→α) (n base oldL newL : Nat) (copies : List Nat)
    (last next : Nat) (previous following : Option Nat) (H : Nat)
    (hc : Certificate f n base oldL copies last next previous following H)
    (hle : newL≤oldL) (hmode : (next<last+oldL ↔ next<last+newL)) :
    Certificate f n base newL copies last next previous following H :=
  ⟨Nat.le_trans hle hc.current,hc.words,hc.lastBound,hc.overlap.trans hmode,
    hc.previousSafe,hc.followingSafe⟩

/-- The square exposed by a density split really has the adjacency
gap as its minimum period; the certificate is attached to every copy. -/
theorem reset_square (f : Nat→α) (n base L : Nat) (xs : List Nat)
    (hfull : Complete f n base L xs) (i j k : Nat)
    (ha : Adjacent xs i j) (hd : 2*(j-i)≤L) (hk : k∈xs) :
    PrimitiveSquare f n k (j-i) := by
  have hm:=complete_least f n base L xs hfull i j k ha hd hk
  have hf:=least_factor (shift f k) L (j-i) 0 (2*(j-i)) hm (Nat.le_refl _) (by omega)
  have he : shift (shift f k) 0=shift f k := by funext a; simp only [shift,Nat.zero_add]
  rw [he] at hf
  exact ⟨by have hh:=((hfull k).mp hk).1; omega,hf⟩

end REWB.MaskedLocalAnchor
