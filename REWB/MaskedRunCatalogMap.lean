import REWB.RunDedup
import REWB.CountedProjection

/-! A measured sparse binary map from exact run triples to direct array
IDs. Key bits, copied concatenation cells, child-slot reads and updates
are all executed by the returned counters. The width is supplied from a
cached text-size bound; lookup never computes powers or scans runs. -/
namespace REWB.MaskedRunCatalog
open REWB.RunGeometry REWB.ExactKeys

namespace Map

def bits : Nat→Nat→List (Fin 2)×Nat
  | 0,_ => ([],1)
  | h+1,x =>
      let tail:=bits h (x/2)
      (⟨x%2,Nat.mod_lt _ (by decide)⟩::tail.1,tail.2+5)

theorem bits_value (h x : Nat) : (bits h x).1=RankIndex.bits h x := by
  induction h generalizing x with
  | zero => rfl
  | succ h ih => simp only [bits,RankIndex.bits,ih]

theorem bits_work (h x : Nat) : (bits h x).2=5*h+1 := by
  induction h generalizing x with
  | zero => rfl
  | succ h ih => simp only [bits,ih]; omega

def key (h : Nat) (R : Bounds) : KeyWord 2×Nat :=
  let lo:=bits h R.lo
  let hi:=bits h R.hi
  let period:=bits h R.period
  let tail:=CountedProjection.append hi.1 period.1
  let all:=CountedProjection.append lo.1 tail.1
  (all.1,lo.2+hi.2+period.2+tail.2+all.2+1)

theorem key_value (h : Nat) (R : Bounds) : (key h R).1=RunDedup.key h R := by
  simp only [key,CountedProjection.append_value,bits_value,RunDedup.key]

theorem key_work (h : Nat) (R : Bounds) : (key h R).2=17*h+6 := by
  simp only [key,bits_work,CountedProjection.append_steps,bits_value,RankIndex.bits_length]
  omega

def put : KeyWord 2→Trie 2→Nat→Trie 2×Nat
  | [],t,id => (withLabel t id,1)
  | a::w,t,id =>
      let slots:=pad 2 (children t)
      let old:=readSlot slots.1 a.val
      let out:=put w old.1 id
      let changed:=replaceSlot slots.1 a.val out.1
      (.node (label t) changed.1,slots.2+old.2+out.2+changed.2+1)

theorem put_cons (a : Fin 2) (w : KeyWord 2) (t : Trie 2) (id : Nat) :
    (put (a::w) t id).1=withChild t a (put w (child t a) id).1 := by
  simp only [put,readSlot_value,pad_read 2 a.val _ a.isLt,child,withChild]

theorem put_lookup (w : KeyWord 2) (t : Trie 2) (id : Nat) (v : KeyWord 2) :
    lookup (put w t id).1 v=if v=w then some id else lookup t v := by
  induction w generalizing t v with
  | nil =>
    cases v with
    | nil => rfl
    | cons a v => simp only [put,lookup,withLabel,child,children,reduceCtorEq,if_false]
  | cons a w ih =>
    rw [put_cons]
    cases v with
    | nil => rfl
    | cons b v =>
      rw [lookup_withChild_cons]
      by_cases he : b=a
      · subst b
        rw [if_pos rfl,ih]
        simp only [List.cons.injEq,true_and,lookup]
      · simp only [he,if_false,List.cons.injEq,false_and,lookup]

theorem put_work (w : KeyWord 2) (t : Trie 2) (id : Nat) :
    (put w t id).2≤7*w.length+1 := by
  induction w generalizing t with
  | nil => exact Nat.le_refl _
  | cons a w ih =>
    have hp:=pad_cost 2 (children t)
    have hr:=readSlot_cost (pad 2 (children t)).1 a.val
    have hs:=replaceSlot_cost (pad 2 (children t)).1 a.val
      (put w (readSlot (pad 2 (children t)).1 a.val).1 id).1
    have ht:=ih (readSlot (pad 2 (children t)).1 a.val).1
    have ha:=a.isLt
    simp only [put,List.length_cons]
    omega

def read : Trie 2→KeyWord 2→Option Nat×Nat
  | t,[] => (label t,1)
  | t,a::w =>
      let next:=readSlot (children t) a.val
      let out:=read next.1 w
      (out.1,next.2+out.2+1)

theorem read_value (t : Trie 2) (w : KeyWord 2) : (read t w).1=lookup t w := by
  induction w generalizing t with
  | nil => rfl
  | cons a w ih => simp only [read,ih,readSlot_value,child,lookup]

theorem read_work (t : Trie 2) (w : KeyWord 2) : (read t w).2≤3*w.length+1 := by
  induction w generalizing t with
  | nil => exact Nat.le_refl _
  | cons a w ih =>
    have hh:=readSlot_cost (children t) a.val
    have ht:=ih (readSlot (children t) a.val).1
    have ha:=a.isLt
    simp only [read,List.length_cons]
    omega

end Map
end REWB.MaskedRunCatalog
