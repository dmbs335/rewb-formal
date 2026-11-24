import REWB.FiniteOrbit
import REWB.ClusterGeometry

/-! Quotient/phase coordinates for arbitrary endpoints of one periodic
    interval. The borrow is determined entirely by the fixed phases.
    Each factor length is a linear expression in the block coordinates
    plus a fixed residue. -/
namespace REWB.Periodic
variable {α : Type}

structure Coord where
  block : Nat
  phase : Nat
  deriving Repr

def Coord.pos (x : Coord) (p : Nat) : Nat := x.block*p+x.phase

def coord (p i : Nat) : Coord := ⟨i/p,i%p⟩

theorem coord_pos (p i : Nat) : (coord p i).pos p=i := by
  unfold coord Coord.pos
  rw [Nat.mul_comm (i/p) p,Nat.add_comm]
  exact Nat.mod_add_div i p

theorem coord_phase (p i : Nat) (hp : 0<p) : (coord p i).phase<p :=
  Nat.mod_lt i hp

def borrow (a b : Coord) : Nat := if a.phase≤b.phase then 0 else 1

def residual (p : Nat) (a b : Coord) : Nat :=
  if a.phase≤b.phase then b.phase-a.phase else p+b.phase-a.phase

def copies (a b : Coord) : Nat := b.block-a.block-borrow a b

theorem block_order (p : Nat) (a b : Coord)
    (hb : b.phase<p) (h : a.pos p≤b.pos p) :
    a.block≤b.block := by
  by_cases he : a.block≤b.block
  · exact he
  · have hm := Nat.mul_le_mul_right p (show b.block+1≤a.block by omega)
    rw [Nat.add_mul,Nat.one_mul] at hm
    unfold Coord.pos at h
    omega

theorem borrow_order (p : Nat) (a b : Coord)
    (hb : b.phase<p) (h : a.pos p≤b.pos p) :
    a.block+borrow a b≤b.block := by
  have hle := block_order p a b hb h
  by_cases he : a.phase≤b.phase
  · simpa [borrow,he] using hle
  · have hh : a.block<b.block := by
      by_cases hh : a.block<b.block
      · exact hh
      · have hsame : a.block=b.block := by omega
        unfold Coord.pos at h
        rw [hsame] at h
        omega
    simp only [borrow,he,if_false]
    omega

/-- The quotient difference is nonnegative, and the residual is strictly
    shorter than one period. This is the linear length formula used in
    fixed-phase Presburger constraints. -/
theorem coordinate_length (p : Nat) (a b : Coord)
    (hp : 0<p) (ha : a.phase<p) (hb : b.phase<p)
    (h : a.pos p≤b.pos p) :
    a.block+borrow a b≤b.block ∧ residual p a b<p ∧
      b.pos p-a.pos p=copies a b*p+residual p a b := by
  have ho := borrow_order p a b hb h
  have hs : b.block=a.block+borrow a b+copies a b := by
    unfold copies
    omega
  have hm : b.block*p=a.block*p+borrow a b*p+copies a b*p := by
    have he := congrArg (fun k=>k*p) hs
    simpa only [Nat.add_mul] using he
  unfold Coord.pos at h ⊢
  by_cases he : a.phase≤b.phase
  · simp only [residual,he,if_true,borrow,Nat.zero_mul,Nat.add_zero] at hm ⊢
    exact ⟨by omega,by omega,by omega⟩
  · simp only [residual,he,if_false,borrow,Nat.one_mul] at hm ⊢
    exact ⟨ho,by omega,by omega⟩

/-- A factor at an arbitrary absolute coordinate is exactly its canonical
    phase factor with the same length. -/
theorem factor_at_phase {f : Nat→α} {n p : Nat}
    (h : Period f n p) (a L : Nat) (hn : a+L≤n) :
    segment f a L=segment f (a%p) L := by
  have he : a%p+(a/p)*p=a := by
    rw [Nat.mul_comm (a/p) p]
    exact Nat.mod_add_div a p
  have hh := segment_same_phase h (a%p) (a/p) L (by rwa [he])
  rw [he] at hh
  exact hh.symm

theorem coordinate_factor {f : Nat→α} {n p : Nat}
    (h : Period f n p) (a b : Coord)
    (hp : 0<p) (ha : a.phase<p) (hb : b.phase<p)
    (ho : a.pos p≤b.pos p) (hn : b.pos p≤n) :
    segment f (a.pos p) (b.pos p-a.pos p) =
      segment f a.phase (copies a b*p+residual p a b) := by
  have hl := (coordinate_length p a b hp ha hb ho).2.2
  have hpos : a.phase+a.block*p=a.pos p := by unfold Coord.pos; omega
  have hlen : a.phase+a.block*p+(b.pos p-a.pos p)≤n := by rw [hpos]; omega
  have he := segment_same_phase h a.phase a.block (b.pos p-a.pos p) hlen
  rw [hpos] at he
  rw [← he,hl]

theorem segment_eq_points (f : Nat→α) (a b L : Nat) :
    segment f a L=segment f b L ↔ ∀ i,i<L → f (a+i)=f (b+i) := by
  induction L generalizing a b with
  | zero =>
    constructor
    · intro _ i hi
      omega
    · intro _
      rfl
  | succ L ih =>
    change (f a::segment f (a+1) L=f b::segment f (b+1) L)↔_
    rw [List.cons.injEq,ih]
    constructor
    · rintro ⟨h0,hrest⟩ i hi
      cases i with
      | zero => simpa only [Nat.add_zero] using h0
      | succ i =>
        have hh := hrest i (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hh
    · intro he
      refine ⟨by simpa only [Nat.add_zero] using he 0 (by omega),?_⟩
      intro i hi
      have hh := he (i+1) (by omega)
      simpa only [Nat.add_assoc,Nat.add_comm i 1] using hh

/-- Equality inside a least-period run is compressed without losing short
    matches of distinct phases. Long factors must share their phase;
    short factors are compared in the canonical period blocks. -/
theorem factor_equality {f : Nat→α} {n p : Nat}
    (hmin : LeastPeriod f n p) (a b L : Nat)
    (hab : a≤b) (hb : b+L≤n) :
    segment f a L=segment f b L ↔
      p∣b-a ∨ (L<p ∧ segment f (a%p) L=segment f (b%p) L) := by
  constructor
  · intro he
    by_cases hL : p≤L
    · exact Or.inl (equal_long_factor_same_phase hmin hab hb hL
        ((segment_eq_points f a b L).mp he))
    · refine Or.inr ⟨by omega,?_⟩
      rw [← factor_at_phase hmin.2.1 a L (by omega),
        ← factor_at_phase hmin.2.1 b L hb]
      exact he
  · rintro (h|⟨_,h⟩)
    · exact compress_same_phase hmin.2.1 a b L hab hb h
    · rw [factor_at_phase hmin.2.1 a L (by omega),
        factor_at_phase hmin.2.1 b L hb]
      exact h

/-- The DFA descriptor for a fixed pair of endpoint phases is valid for
    every choice of block coordinates with those phases. -/
theorem coordinate_descriptor (d : DFA α) {f : Nat→α} {n p : Nat}
    (h : Period f n p) (a b : Coord)
    (hp : 0<p) (ha : a.phase<p) (hb : b.phase<p)
    (ho : a.pos p≤b.pos p) (hn : b.pos p≤n) :
    ∃ D, factorDescriptor d f a.phase p (residual p a b)=some D ∧
      D.threshold+D.period≤d.stateCount ∧ 0<D.period ∧
      (D.test (copies a b)=true ↔ d.accepts
        (segment f (a.pos p) (b.pos p-a.pos p))) := by
  obtain ⟨D,hD,hpD,hsize,_,hcorrect⟩ :=
    factorDescriptor_spec d f n a.phase p (residual p a b) h
  refine ⟨D,hD,hsize,hpD,?_⟩
  rw [coordinate_factor h a b hp ha hb ho hn]
  have hl := (coordinate_length p a b hp ha hb ho).2.2
  have ha0 : a.phase≤a.pos p := by unfold Coord.pos; omega
  apply hcorrect
  omega

end REWB.Periodic
