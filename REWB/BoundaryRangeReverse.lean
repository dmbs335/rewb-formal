import REWB.BoundaryRangeAutomata

/-! Reversing a masked all-start instance marks eligible second-copy
ends in the original word. This is the exact bridge needed when the
first-copy end lies beyond the next block boundary. -/
namespace REWB.BoundaryRange
open REWB.Spec (slice)
variable {α : Type}

theorem reverse_slice (w : Word α) (a b : Nat) (hab : a≤b) (hb : b≤w.length) :
    slice w.reverse a b=(slice w (w.length-b) (w.length-a)).reverse := by
  unfold slice
  rw [List.drop_reverse,List.take_reverse,List.length_take]
  have hmin : min (w.length-a) w.length=w.length-a := Nat.min_eq_left (by omega)
  have hsub : w.length-a-(b-a)=w.length-b := by omega
  rw [hmin,hsub,List.drop_take]

def BeforeEnd (A B C : DFA α) (w : Word α) (mask : Nat→Bool) (t : Nat) : Prop :=
  ∃i a j,i≤a ∧ a≤j ∧ j≤t ∧ mask a=true ∧
    slice w i a=slice w j t ∧ A.accepts (slice w 0 i) ∧
    B.accepts (slice w i a) ∧ C.accepts (slice w a j)

theorem masked_reverse (A B C : DFA α) (w : Word α) (mask : Nat→Bool)
    (t : Nat) (ht : t≤w.length) :
    Spec.maskedStart (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
      w.reverse (fun y=>mask (w.length-y)) (w.length-t) ↔ BeforeEnd A B C w mask t := by
  constructor
  · rintro ⟨b,y,u,hsb,hby,hyu,hu,hmask,he,hB,hC,hA⟩
    rw [List.length_reverse] at hu
    have hst : w.length-(w.length-t)=t := by omega
    have he' : slice w (w.length-u) (w.length-y)=slice w (w.length-b) t := by
      rw [reverse_slice w (w.length-t) b hsb (by omega),
        reverse_slice w y u hyu hu,hst] at he
      exact (List.reverse_inj.mp he).symm
    have hB':=(Automata.reverse_accepts B _).mp hB
    rw [reverse_slice w (w.length-t) b hsb (by omega),List.reverse_reverse,hst] at hB'
    have hC':=(Automata.reverse_accepts C _).mp hC
    rw [reverse_slice w b y hby (by omega),List.reverse_reverse] at hC'
    have hA':=(Automata.reverse_accepts A _).mp hA
    rw [List.length_reverse,reverse_slice w u w.length hu (Nat.le_refl _),
      List.reverse_reverse,Nat.sub_self] at hA'
    refine ⟨w.length-u,w.length-y,w.length-b,by omega,by omega,by omega,hmask,he',hA',?_,hC'⟩
    rwa [he']
  · rintro ⟨i,a,j,hia,haj,hjt,hmask,he,hA,hB,hC⟩
    have hi : i≤w.length := by omega
    have ha : a≤w.length := by omega
    have hj : j≤w.length := by omega
    have hst : w.length-(w.length-t)=t := by omega
    have hsI : w.length-(w.length-i)=i := by omega
    have hsA : w.length-(w.length-a)=a := by omega
    have hsJ : w.length-(w.length-j)=j := by omega
    refine ⟨w.length-j,w.length-a,w.length-i,by omega,by omega,by omega,?_,?_,?_,?_,?_,?_⟩
    · simp only [List.length_reverse]; omega
    · simpa only [hsA] using hmask
    · rw [reverse_slice w (w.length-t) (w.length-j) (by omega) (by omega),
        reverse_slice w (w.length-a) (w.length-i) (by omega) (by omega),hst,hsI,hsA,hsJ]
      exact congrArg List.reverse he.symm
    · apply (Automata.reverse_accepts B _).mpr
      rw [reverse_slice w (w.length-t) (w.length-j) (by omega) (by omega),
        List.reverse_reverse,hst,hsJ]
      rwa [←he]
    · apply (Automata.reverse_accepts C _).mpr
      rw [reverse_slice w (w.length-j) (w.length-a) (by omega) (by omega),
        List.reverse_reverse,hsA,hsJ]
      exact hC
    · apply (Automata.reverse_accepts A _).mpr
      rw [List.length_reverse,reverse_slice w (w.length-i) w.length (by omega) (Nat.le_refl _),
        List.reverse_reverse,Nat.sub_self,hsI]
      exact hA

theorem beforeEnd_copy (A B C E : DFA α) (w : Word α) (mask : Nat→Bool)
    (right : Nat) (hr : right≤w.length) :
    (∃t,t≤right ∧ BeforeEnd A B C w mask t ∧ E.accepts (slice w t right)) ↔
      ∃a j,mask a=true ∧ a≤j ∧ Copy A B E w a j right ∧ C.accepts (slice w a j) := by
  constructor
  · rintro ⟨t,htr,⟨i,a,j,hia,haj,hjt,hm,he,hA,hB,hC⟩,hE⟩
    have heLen:=congrArg List.length he
    rw [OuterColumn.slice_length w i a hia (by omega),
      OuterColumn.slice_length w j t hjt (by omega)] at heLen
    have hi : a-(a-i)=i := by omega
    have ht : j+(a-i)=t := by omega
    refine ⟨a,j,hm,haj,⟨a-i,by omega,by omega,?_,?_,?_,?_⟩,hC⟩
    · simpa only [hi,ht] using he
    · simpa only [hi] using hA
    · simpa only [hi] using hB
    · simpa only [ht] using hE
  · rintro ⟨a,j,hm,haj,⟨L,hL,hR,he,hA,hB,hE⟩,hC⟩
    exact ⟨j+L,hR,⟨a-L,a,j,by omega,haj,by omega,hm,he,hA,hB,hC⟩,hE⟩

end REWB.BoundaryRange
