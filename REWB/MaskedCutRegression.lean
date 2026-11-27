import REWB.MaskedCutTuples

/-! Independent finite references for the joint-cut index. -/
namespace REWB.MaskedCut.Regression
open REWB.FiniteRelation
open REWB.RangeProducts (Ops product)
open REWB.Spec (slice)

def parity : Ops Bool where
  one := false
  mul := Bool.xor
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

def enumeration : Enumeration Bool := ⟨[false,true],by intro x; cases x <;> simp⟩

def direct (xs : List Bool) (l lo hi r : Nat) (p s : Bool) : Bool :=
  (List.range (hi+1)).any (fun i=>
    decide (lo≤i ∧ product parity (slice xs l i)=p ∧ product parity (slice xs i r)=s))

theorem direct_correct (xs : List Bool) (l lo hi r : Nat) (p s : Bool) :
    direct xs l lo hi r p s=true ↔
      ∃ i,lo≤i ∧ i≤hi ∧ product parity (slice xs l i)=p ∧ product parity (slice xs i r)=s := by
  simp only [direct,List.any_eq_true,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,hl,hp,hs⟩
    exact ⟨i,hl,by omega,hp,hs⟩
  · rintro ⟨i,hl,hi,hp,hs⟩
    exact ⟨i,by omega,hl,hp,hs⟩

theorem query_eq_direct (xs : List Bool) (l lo hi r : Nat) (p s : Bool)
    (hl : l≤lo) (hb : lo≤hi) (hr : hi≤r) (hn : r≤xs.length) :
    ((Index.query parity enumeration (Index.build parity enumeration xs).1 l lo hi r).answer.map
      (fun table=>MatrixTable.denote table p s)).getD false=direct xs l lo hi r p s := by
  apply Bool.eq_iff_iff.mpr
  have h := Index.query_correct parity enumeration xs l lo hi r p s hl hb hr hn
  rw [Index.query_value parity enumeration xs l lo hi r hl hb hr hn] at h ⊢
  simpa only [Option.map,Option.getD_some,Option.some.injEq,direct_correct] using h

/-- Each coordinate can independently be false at some cut, but the pair
(false,false) occurs at no common cut. A Cartesian product would be wrong. -/
theorem correlated_cut :
    closed parity (trace parity enumeration [true]) false true=true ∧
    closed parity (trace parity enumeration [true]) true false=true ∧
    closed parity (trace parity enumeration [true]) false false=false := by decide

def oneIndex := (Index.build parity enumeration [true]).1

theorem positive_cut :
    ((Index.query parity enumeration oneIndex 0 1 1 1).answer.map
      (fun table=>MatrixTable.denote table false true))=some false ∧
    ((Index.query parity enumeration oneIndex 0 1 1 1).answer.map
      (fun table=>MatrixTable.denote table true false))=some true := by
  unfold oneIndex
  rw [Index.query_value parity enumeration [true] 0 1 1 1 (by decide)
    (by decide) (by decide) (by decide)]
  decide

theorem empty_cut :
    ((Index.query parity enumeration (Index.build parity enumeration []).1 0 0 0 0).answer.map
      (fun table=>MatrixTable.denote table false false))=some true := by
  rw [Index.query_value parity enumeration [] 0 0 0 0 (by decide)
    (by decide) (by decide) (by decide)]
  decide

theorem rotation_count :
    (Rotations.batch parity enumeration [true,false,true]).values.size=3 ∧
    (Rotations.batch parity enumeration []).values.size=0 := by
  simp only [Rotations.batch_size]
  decide

end REWB.MaskedCut.Regression
