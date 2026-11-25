import REWB.BoundaryBorderSeed
import REWB.MaskedOrderedEraseQuery

/-! Constant-query occurrence extraction from a closed position window.
The caller supplies one retained complete occurrence tree, not a leader
tree for each requested length. A dense first adjacency determines the
period; one measured LCE determines its maximal right extent. Two such
components suffice when the window width is smaller than the copy length.
No occurrence list, source phase, or capture length is traversed here. -/
namespace REWB.BoundaryBorder.Window
open REWB.MaskedOrdered
variable {h : Nat}

structure Band where
  first : Nat
  last : Nat
  step : Nat
  deriving Repr, DecidableEq

def Band.Holds (b : Band) (p : Nat) : Prop := Member b.first b.step b.first b.last p

def rounded (first cap step : Nat) : Nat := first+((cap-first)/step)*step

def component (idx : RankIndex.Index) (t : Tree h) (capacity n L hi first : Nat) : Band×Nat :=
  let next:=Tree.succ t capacity first
  match next.1 with
  | none => (⟨first,first,1⟩,next.2+4)
  | some u =>
    if first<u ∧ u≤hi ∧ 2*(u-first)≤L then
      let q:=u-first
      let extension:=extend idx n first q
      let cap:=min hi (first+extension.extent-L)
      (⟨first,rounded first cap q,q⟩,next.2+extension.work+18)
    else (⟨first,first,1⟩,next.2+7)

theorem component_work (idx : RankIndex.Index) (t : Tree h) (capacity n L hi first : Nat) :
    (component idx t capacity n L hi first).2≤7*h+13*(n.log2+1)+25 := by
  have hs:=Tree.succ_work t capacity first
  simp only [component]
  cases he : (Tree.succ t capacity first).1 with
  | none => simp only [he]; omega
  | some u =>
    simp only [he]
    have hx:=extend_work idx n first (u-first)
    split <;> omega

structure Extracted where
  first : Option Band
  second : Option Band
  work : Nat
  deriving Repr, DecidableEq

def Extracted.Holds (out : Extracted) (p : Nat) : Prop :=
  (∃b,out.first=some b ∧ b.Holds p) ∨ (∃b,out.second=some b ∧ b.Holds p)

def extract (idx : RankIndex.Index) (t : Tree h) (capacity n L lo hi : Nat) : Extracted :=
  let first:=Tree.interval t capacity lo hi
  match first.1 with
  | none => ⟨none,none,first.2+2⟩
  | some p =>
    let left:=component idx t capacity n L hi p
    let next:=Tree.interval t capacity (left.1.last+1) hi
    match next.1 with
    | none => ⟨some left.1,none,first.2+left.2+next.2+5⟩
    | some q =>
      let right:=component idx t capacity n L hi q
      ⟨some left.1,some right.1,first.2+left.2+next.2+right.2+7⟩

theorem extract_work (idx : RankIndex.Index) (t : Tree h) (capacity n L lo hi : Nat) :
    (extract idx t capacity n L lo hi).work≤28*h+26*(n.log2+1)+71 := by
  have hf:=Tree.interval_work t capacity lo hi
  simp only [extract]
  cases he : (Tree.interval t capacity lo hi).1 with
  | none => simp only [he]; omega
  | some p =>
    simp only [he]
    have hl:=component_work idx t capacity n L hi p
    have hn:=Tree.interval_work t capacity ((component idx t capacity n L hi p).1.last+1) hi
    cases hn' : (Tree.interval t capacity ((component idx t capacity n L hi p).1.last+1) hi).1 with
    | none => simp only [hn']; omega
    | some q =>
      simp only [hn']
      have hr:=component_work idx t capacity n L hi q
      omega

end REWB.BoundaryBorder.Window
