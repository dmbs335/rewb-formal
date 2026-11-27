import REWB.MaskedClusterCutCorrect
import REWB.MaskedMutableProgressionCost

/-! A ghost finite mask for one persistent source-index snapshot.
    This array is used only in proofs to reuse the immutable physical
    cursor semantics. No executable mutable cell, matrix or bank calls
    `snapshot`, and erasing a source does not rebuild this array.
-/
namespace REWB.MaskedCluster.Mutable
abbrev Index := MaskedMutableProgression.Index

def snapshot (idx : Index) : Array Bool :=
  Array.ofFn fun i : Fin (idx.base+idx.len)=>(MaskedMutableProgression.member idx i.val).1

theorem snapshot_read (idx : Index) (p : Nat) :
    MaskedProgression.readMask (snapshot idx) p=(MaskedMutableProgression.member idx p).1 := by
  by_cases h : p<idx.base+idx.len
  · simp only [MaskedProgression.readMask,snapshot,Array.getElem?_ofFn,h,dif_pos,Option.getD_some]
  · have hb : p<idx.base ∨ idx.base+idx.len≤p := Or.inr (by omega)
    simp [MaskedProgression.readMask,snapshot,Array.getElem?_ofFn,h,dif_neg,
      Option.getD_none,MaskedMutableProgression.member,hb,if_true]

theorem snapshot_live (idx : Index) (hv : idx.Valid) (p : Nat) :
    MaskedProgression.readMask (snapshot idx) p=true ↔ idx.Live p := by
  rw [snapshot_read,MaskedMutableProgression.member_correct idx hv p]

theorem snapshot_erase (idx : Index) (hv : idx.Valid) (p x : Nat) :
    MaskedProgression.readMask (snapshot (MaskedMutableProgression.erase idx p).index) x=
      (decide (x≠p) && MaskedProgression.readMask (snapshot idx) x) := by
  apply Bool.eq_iff_iff.mpr
  rw [snapshot_live _ (MaskedMutableProgression.erase_valid idx hv p),
    MaskedMutableProgression.erase_live idx hv p x,Bool.and_eq_true,decide_eq_true_eq,snapshot_live idx hv x]

structure Answer where
  answer : Bool
  work : Nat
  deriving Repr

def ofStatic (a : MaskedProgression.Answer) : Answer := ⟨a.answer,a.slots+a.arithmetic⟩

def either (a b : Answer) : Answer := ⟨a.answer || b.answer,a.work+b.work+1⟩

end REWB.MaskedCluster.Mutable
