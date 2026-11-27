import REWB.OneUseRangeBorderPartition
import REWB.BoundaryRangeReverse

/-! Reversing one-use range queries preserves both external bounds.
In particular a source lower cutoff becomes a target upper cutoff.
The B acceptance test is transferred across the two equal copies. -/
namespace REWB.OneUseRange.Reverse
open REWB.BoundaryRange REWB.Spec
variable {α : Type} {σ : Nat}

theorem accepts_slice (d : DFA α) (w : Word α) (a b : Nat)
    (hab : a≤b) (hb : b≤w.length) :
    (Automata.reverse d).accepts (slice w.reverse a b) ↔
      d.accepts (slice w (w.length-b) (w.length-a)) := by
  rw [Automata.reverse_accepts,reverse_slice w a b hab hb,List.reverse_reverse]

theorem accepts_complement (d : DFA α) (w : Word α) (a b : Nat)
    (hab : a≤b) (hb : b≤w.length) :
    (Automata.reverse d).accepts (slice w.reverse (w.length-b) (w.length-a)) ↔
      d.accepts (slice w a b) := by
  rw [accepts_slice d w (w.length-b) (w.length-a) (by omega) (by omega),
    Nat.sub_sub_self (show a≤w.length by omega),Nat.sub_sub_self hb]

theorem at_congr (A B C E A' B' C' E' : DFA (Fin σ)) (w : Word (Fin σ))
    (left right i t : Nat)
    (ha : ∀v,A.accepts v↔A'.accepts v) (hb : ∀v,B.accepts v↔B'.accepts v)
    (hc : ∀v,C.accepts v↔C'.accepts v) (he : ∀v,E.accepts v↔E'.accepts v) :
    Border.At A B C E w left right i t↔Border.At A' B' C' E' w left right i t := by
  simp only [Border.At,Border.Inner,ha,hb,hc,he]

theorem at_forward (A B C E : DFA (Fin σ)) (w : Word (Fin σ))
    (left right i t : Nat) (hr : right≤w.length) (h : Border.At A B C E w left right i t) :
    Border.At (Automata.reverse E) (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
      w.reverse (w.length-right) (w.length-left) (w.length-t) (w.length-i) := by
  obtain ⟨a,j,hli,hia,haj,hjt,htr,he,hA,hB,hC,hE⟩:=
    (Border.at_iff_cuts A B C E w left right i t hr).mp h
  apply (Border.at_iff_cuts _ _ _ _ w.reverse (w.length-right) (w.length-left)
    (w.length-t) (w.length-i) (by rw [List.length_reverse]; omega)).mpr
  refine ⟨w.length-j,w.length-a,by omega,by omega,by omega,by omega,by omega,?_,?_,?_,?_,?_⟩
  · rw [reverse_slice w (w.length-t) (w.length-j) (by omega) (by omega),
      reverse_slice w (w.length-a) (w.length-i) (by omega) (by omega),
      Nat.sub_sub_self (show j≤w.length by omega),Nat.sub_sub_self (show t≤w.length by omega),
      Nat.sub_sub_self (show i≤w.length by omega),Nat.sub_sub_self (show a≤w.length by omega)]
    exact congrArg List.reverse he.symm
  · exact (accepts_complement E w t right htr hr).mpr hE
  · apply (accepts_complement B w j t hjt (by omega)).mpr
    rwa [←he]
  · exact (accepts_complement C w a j haj (by omega)).mpr hC
  · exact (accepts_complement A w left i hli (by omega)).mpr hA

theorem twice (d : DFA α) (v : Word α) :
    (Automata.reverse (Automata.reverse d)).accepts v↔d.accepts v := by
  rw [Automata.reverse_accepts,Automata.reverse_accepts,List.reverse_reverse]

theorem at_reverse (A B C E : DFA (Fin σ)) (w : Word (Fin σ))
    (left right i t : Nat) (hl : left≤w.length) (hr : right≤w.length)
    (hi : i≤w.length) (ht : t≤w.length) :
    Border.At A B C E w left right i t ↔
      Border.At (Automata.reverse E) (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
        w.reverse (w.length-right) (w.length-left) (w.length-t) (w.length-i) := by
  constructor
  · exact at_forward A B C E w left right i t hr
  · intro h
    have hh:=at_forward (Automata.reverse E) (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
      w.reverse (w.length-right) (w.length-left) (w.length-t) (w.length-i)
      (by rw [List.length_reverse]; omega) h
    simp only [List.length_reverse,List.reverse_reverse,Nat.sub_sub_self hl,Nat.sub_sub_self hr,
      Nat.sub_sub_self hi,Nat.sub_sub_self ht] at hh
    exact (at_congr _ _ _ _ A B C E w left right i t (twice A) (twice B) (twice C) (twice E)).mp hh

theorem oneUseRange_reverse (A B C E : DFA (Fin σ)) (w : Word (Fin σ))
    (left right : Nat) (hlr : left≤right) (hr : right≤w.length) :
    Spec.oneUseRange A B C E w left right ↔
      Spec.oneUseRange (Automata.reverse E) (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
        w.reverse (w.length-right) (w.length-left) := by
  rw [Border.oneUse_iff,Border.oneUse_iff]
  constructor
  · rintro ⟨_,_,i,t,h⟩
    exact ⟨by omega,by rw [List.length_reverse]; omega,w.length-t,w.length-i,
      at_forward A B C E w left right i t hr h⟩
  · rintro ⟨_,_,u,v,h⟩
    have hu : u≤w.length := by have hb:=h.2.1; have hc:=h.2.2.1; omega
    have hv : v≤w.length := by have hc:=h.2.2.1; omega
    have hh : Border.At (Automata.reverse E) (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
        w.reverse (w.length-right) (w.length-left) (w.length-(w.length-u)) (w.length-(w.length-v)) := by
      simpa only [Nat.sub_sub_self hu,Nat.sub_sub_self hv] using h
    exact ⟨hlr,hr,w.length-v,w.length-u,
      (at_reverse A B C E w left right (w.length-v) (w.length-u) (by omega) hr
        (by omega) (by omega)).mpr hh⟩

theorem farSource_reverse (A B C E : DFA (Fin σ)) (w : Word (Fin σ))
    (left right grid : Nat) (hl : left≤w.length) (hr : right≤w.length) (hg : grid≤w.length) :
    Border.FarSource A B C E w left right grid ↔
      Border.FarTarget (Automata.reverse E) (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
        w.reverse (w.length-right) (w.length-left) (w.length-grid) := by
  constructor
  · rintro ⟨i,t,h,hgI⟩
    exact ⟨w.length-t,w.length-i,at_forward A B C E w left right i t hr h,by omega⟩
  · rintro ⟨u,v,h,hvG⟩
    have hu : u≤w.length := by have hb:=h.2.1; have hc:=h.2.2.1; omega
    have hv : v≤w.length := by omega
    have hh : Border.At (Automata.reverse E) (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
        w.reverse (w.length-right) (w.length-left) (w.length-(w.length-u)) (w.length-(w.length-v)) := by
      simpa only [Nat.sub_sub_self hu,Nat.sub_sub_self hv] using h
    exact ⟨w.length-v,w.length-u,
      (at_reverse A B C E w left right (w.length-v) (w.length-u) hl hr (by omega) (by omega)).mpr hh,
      by omega⟩

end REWB.OneUseRange.Reverse
