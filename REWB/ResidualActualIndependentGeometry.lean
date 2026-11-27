import REWB.BoundaryRangeReverse
import REWB.NestedColumns

/-! The independent-capture normal form factors at the end of its first
copy pair and the start of its second copy pair. The two captured words
are unrelated; only the intervening regular D factor is joined. -/
namespace REWB.ResidualActual.Independent
open REWB.Spec (slice)
open REWB.BoundaryRange
variable {α : Type}

def Joined (P : SevenDFA α) (w : Word α) : Prop :=
  ∃t s,t≤s ∧ s≤w.length ∧ BeforeEnd P.A P.B P.C w (fun _=>true) t ∧
    P.D.accepts (slice w t s) ∧ Spec.maskedStart P.F P.G P.H w (fun _=>true) s

theorem joined_sound (P : SevenDFA α) (w : Word α) (h : Joined P w) :
    MatchesWithin P.independent w 2 := by
  obtain ⟨t,s,hts,hsn,⟨i,a,j,hia,haj,hjt,_,hu,ha,hb,hc⟩,hd,
    ⟨b,k,l,hsb,hbk,hkl,hln,_,hv,hf,hg,hh⟩⟩:=h
  apply (Witness.independent_iff P w).mpr
  refine ⟨slice w 0 i,slice w i a,slice w a j,slice w t s,
    slice w s b,slice w b k,slice w l w.length,ha,hb,hc,hd,hf,hg,hh,?_⟩
  calc
    w = slice w 0 w.length := (NestedColumns.slice_full w).symm
    _ = _ := by
      rw [OuterColumn.slice_split w 0 i w.length (by omega) (by omega),
        OuterColumn.slice_split w i a w.length hia (by omega),
        OuterColumn.slice_split w a j w.length haj (by omega),
        OuterColumn.slice_split w j t w.length hjt (by omega),
        OuterColumn.slice_split w t s w.length hts hsn,
        OuterColumn.slice_split w s b w.length hsb (by omega),
        OuterColumn.slice_split w b k w.length hbk (by omega),
        OuterColumn.slice_split w k l w.length hkl hln,←hu,←hv]
      simp only [List.append_assoc]

theorem words_joined (P : SevenDFA α) (a u c d v g h : Word α)
    (ha : P.A.accepts a) (hu : P.B.accepts u) (hc : P.C.accepts c)
    (hd : P.D.accepts d) (hv : P.F.accepts v) (hg : P.G.accepts g) (hh : P.H.accepts h) :
    Joined P (a++u++c++u++d++v++g++v++h) := by
  let w:=a++u++c++u++d++v++g++v++h
  let i:=a.length
  let x:=a.length+u.length
  let j:=a.length+u.length+c.length
  let t:=a.length+u.length+c.length+u.length
  let s:=a.length+u.length+c.length+u.length+d.length
  let b:=a.length+u.length+c.length+u.length+d.length+v.length
  let k:=a.length+u.length+c.length+u.length+d.length+v.length+g.length
  let l:=a.length+u.length+c.length+u.length+d.length+v.length+g.length+v.length
  have hn : w.length=l+h.length := by simp only [w,l,List.length_append]
  have hA : slice w 0 i=a := by
    simpa only [w,i,List.nil_append,List.length_nil,Nat.zero_add,List.append_assoc] using
      NestedColumns.slice_block ([] : Word α) a (u++c++u++d++v++g++v++h)
  have hB : slice w i x=u := by
    simpa only [w,i,x,List.append_assoc] using NestedColumns.slice_block a u (c++u++d++v++g++v++h)
  have hC : slice w x j=c := by
    simpa only [w,x,j,List.length_append,List.append_assoc,Nat.add_assoc] using
      NestedColumns.slice_block (a++u) c (u++d++v++g++v++h)
  have hU : slice w j t=u := by
    simpa only [w,j,t,List.length_append,List.append_assoc,Nat.add_assoc] using
      NestedColumns.slice_block (a++u++c) u (d++v++g++v++h)
  have hD : slice w t s=d := by
    simpa only [w,t,s,List.length_append,List.append_assoc,Nat.add_assoc] using
      NestedColumns.slice_block (a++u++c++u) d (v++g++v++h)
  have hF : slice w s b=v := by
    simpa only [w,s,b,List.length_append,List.append_assoc,Nat.add_assoc] using
      NestedColumns.slice_block (a++u++c++u++d) v (g++v++h)
  have hG : slice w b k=g := by
    simpa only [w,b,k,List.length_append,List.append_assoc,Nat.add_assoc] using
      NestedColumns.slice_block (a++u++c++u++d++v) g (v++h)
  have hV : slice w k l=v := by
    simpa only [w,k,l,List.length_append,List.append_assoc,Nat.add_assoc] using
      NestedColumns.slice_block (a++u++c++u++d++v++g) v h
  have hH : slice w l w.length=h := by
    simpa only [w,l,List.length_append,List.append_nil,List.append_assoc,Nat.add_assoc] using
      NestedColumns.slice_block (a++u++c++u++d++v++g++v) h []
  have ordered : i≤x ∧ x≤j ∧ j≤t ∧ t≤s ∧ s≤b ∧ b≤k ∧ k≤l := by
    dsimp only [i,x,j,t,s,b,k,l]
    omega
  refine ⟨t,s,ordered.2.2.2.1,by change s≤w.length; rw [hn]; dsimp only [s,l]; omega,
    ⟨i,x,j,ordered.1,ordered.2.1,ordered.2.2.1,rfl,?_,?_,?_,?_⟩,?_,
    ⟨b,k,l,ordered.2.2.2.2.1,ordered.2.2.2.2.2.1,ordered.2.2.2.2.2.2,by change l≤w.length; rw [hn]; omega,rfl,?_,?_,?_,?_⟩⟩
  · rw [hB,hU]
  · rwa [hA]
  · rwa [hB]
  · rwa [hC]
  · rwa [hD]
  · rw [hF,hV]
  · rwa [hF]
  · rwa [hG]
  · rwa [hH]

theorem joined_correct (P : SevenDFA α) (w : Word α) :
    Joined P w ↔ MatchesWithin P.independent w 2 := by
  constructor
  · exact joined_sound P w
  · intro matched
    obtain ⟨a,u,c,d,v,g,tail,ha,hu,hc,hd,hv,hg,hh,rfl⟩:=(Witness.independent_iff P w).mp matched
    exact words_joined P a u c d v g tail ha hu hc hd hv hg hh

end REWB.ResidualActual.Independent
