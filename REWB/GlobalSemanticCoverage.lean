import REWB.GlobalCoverageP1
import REWB.ArrayText

/-! Derive the absolute endpoints used by geometric dispatch directly
    from source-language matches. The caller supplies no layout, run,
    period, or global coverage premise. The remaining query classes are
    still explicit residual obligations, not implemented fast matchers. -/
namespace REWB.GlobalSemanticCoverage
open REWB.Periodic REWB.P2Periodic
variable {α : Type} {σ : Nat}

theorem factor_slice (f : Nat→α) (n a b : Nat) (hab : a≤b) (hbn : b≤n) :
    factor f a b=Spec.slice (segment f 0 n) a b := by
  unfold Spec.slice factor
  rw [SmallPeriodP2.segment_drop f 0 n a (by omega)]
  simp only [Nat.zero_add]
  rw [SmallPeriodP2.segment_take f a (n-a) (b-a) (by omega)]

theorem factor_part (f : Nat→α) (n : Nat) (pre mid post : Word α)
    (hw : segment f 0 n=pre++mid++post) :
    factor f pre.length (pre++mid).length=mid := by
  have hn := congrArg List.length hw
  simp only [segment_length,List.length_append] at hn
  rw [factor_slice f n _ _ (by simp [List.length_append])
    (by simp only [List.length_append]; omega),hw]
  simp only [Spec.slice,List.length_append,List.append_assoc,List.drop_left]
  rw [show pre.length+mid.length-pre.length=mid.length by omega,List.take_left]

def p2Layout (a b u d vF g : Word α) : P2Periodic.Layout Nat :=
  let v := b++u++d++u++vF
  ⟨a.length,(a++b).length,(a++b++u).length,(a++b++u++d).length,
   (a++b++u++d++u).length,(a++v).length,(a++v++g).length,(a++v++g++v).length⟩

theorem p2_of_match (P : SevenDFA α) (f : Nat→α) (n : Nat)
    (hm : MatchesWithin P.nested2 (segment f 0 n) 2) :
    ∃ x,P2Periodic.Witness P f n [] [] x := by
  obtain ⟨a,b,u,d,vF,g,vH,ha,hb,hu,hd,hF,hG,hH,hw⟩ :=
    (REWB.Witness.nested2_iff P _).mp hm
  let v := b++u++d++u++vF
  let z := p2Layout a b u d vF g
  have hn := congrArg List.length hw
  simp only [segment_length,List.length_append] at hn
  have parts (pre mid post : Word α) (he : segment f 0 n=pre++mid++post) :=
    factor_part f n pre mid post he
  have hA : factor f 0 z.p=a := by
    simpa only [z,p2Layout,List.length_nil,List.nil_append] using
      parts [] a (v++g++v++vH) (by simpa only [v,List.nil_append,List.append_assoc] using hw)
  have hB : factor f z.p z.i=b := by
    simpa only [z,p2Layout] using parts a b (u++d++u++vF++g++v++vH)
      (by simpa only [v,List.append_assoc] using hw)
  have hU : factor f z.i z.a=u := by
    simpa only [z,p2Layout] using parts (a++b) u (d++u++vF++g++v++vH)
      (by simpa only [v,List.append_assoc] using hw)
  have hD : factor f z.a z.j=d := by
    simpa only [z,p2Layout] using parts (a++b++u) d (u++vF++g++v++vH)
      (by simpa only [v,List.append_assoc] using hw)
  have hU' : factor f z.j z.t=u := by
    simpa only [z,p2Layout] using parts (a++b++u++d) u (vF++g++v++vH)
      (by simpa only [v,List.append_assoc] using hw)
  have hF' : factor f z.t z.e=vF := by
    simpa only [z,p2Layout,List.length_append,Nat.add_assoc] using
      parts (a++b++u++d++u) vF (g++v++vH) (by simpa only [v,List.append_assoc] using hw)
  have hG' : factor f z.e z.k=g := by
    simpa only [z,p2Layout,v] using parts (a++v) g (v++vH)
      (by simpa only [v,List.append_assoc] using hw)
  have hV : factor f z.p z.e=v := by
    simpa only [z,p2Layout,v] using parts a v (g++v++vH)
      (by simpa only [v,List.append_assoc] using hw)
  have hV' : factor f z.k z.f=v := by
    simpa only [z,p2Layout,v] using parts (a++v++g) v vH
      (by simpa only [v,List.append_assoc] using hw)
  have hH' : factor f z.f n=vH := by
    have h := parts (a++v++g++v) vH [] (by simpa only [v,List.append_nil,List.append_assoc] using hw)
    have he : n=(a++v++g++v++vH).length := by
      simp only [v,List.length_append]
      omega
    simpa only [z,p2Layout,v,he] using h
  refine ⟨z,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [z,p2Layout,List.length_append]; omega
  · simp only [z,p2Layout,List.length_append]; omega
  · simp only [z,p2Layout,List.length_append]; omega
  · simp only [z,p2Layout,List.length_append]; omega
  · simp only [z,p2Layout,List.length_append]; omega
  · simp only [z,p2Layout,List.length_append]; omega
  · simp only [z,p2Layout,List.length_append]; omega
  · simp only [z,p2Layout,List.length_append]; omega
  · simpa only [List.nil_append,hA] using ha
  · simpa only [hB] using hb
  · simpa only [hU] using hu
  · simpa only [hD] using hd
  · simpa only [hF'] using hF
  · simpa only [hG'] using hG
  · simpa only [List.append_nil,hH'] using hH
  · rw [hU,hU']
  · rw [hV,hV']

def p1Layout (a u c d vF g : Word α) : P1Target.Layout Nat :=
  let pre := a++u++c
  let v := d++u++vF
  ⟨(pre++d).length,(pre++d++u).length,(pre++v).length,
   (pre++v++g).length,(pre++v++g++v).length⟩

theorem p1_of_match (P : SevenDFA α) (f : Nat→α) (n : Nat)
    (hm : MatchesWithin P.nested1 (segment f 0 n) 2) :
    Nonempty (GlobalCoverageP1.Witness P f n) := by
  obtain ⟨a,u,c,d,vF,g,vH,ha,hu,hc,hd,hF,hG,hH,hw⟩ :=
    (REWB.Witness.nested1_iff P _).mp hm
  let pre := a++u++c
  let v := d++u++vF
  let z := p1Layout a u c d vF g
  have hn := congrArg List.length hw
  simp only [segment_length,List.length_append] at hn
  have parts (left mid right : Word α) (he : segment f 0 n=left++mid++right) :=
    factor_part f n left mid right he
  have hA : segment f 0 a.length=a := by
    have hh := parts [] a (u++c++v++g++v++vH)
      (by simpa only [v,List.nil_append,List.append_assoc] using hw)
    simpa only [factor,List.length_nil,List.nil_append,Nat.sub_zero] using hh
  have hS : segment f a.length u.length=u := by
    have hh := parts a u (c++v++g++v++vH)
      (by simpa only [v,List.append_assoc] using hw)
    simpa only [factor,List.length_append,
      show a.length+u.length-a.length=u.length by omega] using hh
  have hC : factor f (a++u).length pre.length=c := by
    exact parts (a++u) c (v++g++v++vH) (by simpa only [v,List.append_assoc] using hw)
  have hD : factor f pre.length z.j=d := by
    simpa only [z,p1Layout,pre] using parts pre d (u++vF++g++v++vH)
      (by simpa only [v,pre,List.append_assoc] using hw)
  have hU : factor f z.j z.t=u := by
    simpa only [z,p1Layout,pre] using parts (pre++d) u (vF++g++v++vH)
      (by simpa only [v,pre,List.append_assoc] using hw)
  have hF' : factor f z.t z.e=vF := by
    simpa only [z,p1Layout,pre,List.length_append,Nat.add_assoc] using
      parts (pre++d++u) vF (g++v++vH) (by simpa only [v,pre,List.append_assoc] using hw)
  have hG' : factor f z.e z.k=g := by
    simpa only [z,p1Layout,pre,v] using parts (pre++v) g (v++vH)
      (by simpa only [v,pre,List.append_assoc] using hw)
  have hV : factor f pre.length z.e=v := by
    simpa only [z,p1Layout,pre,v] using parts pre v (g++v++vH)
      (by simpa only [v,pre,List.append_assoc] using hw)
  have hV' : factor f z.k z.f=v := by
    simpa only [z,p1Layout,pre,v] using parts (pre++v++g) v vH
      (by simpa only [v,pre,List.append_assoc] using hw)
  have hH' : factor f z.f n=vH := by
    have hh := parts (pre++v++g++v) vH []
      (by simpa only [v,pre,List.append_nil,List.append_assoc] using hw)
    have he : n=(pre++v++g++v++vH).length := by
      simp only [v,pre,List.length_append]
      omega
    simpa only [z,p1Layout,pre,v,he] using hh
  have hlen : z.t-z.j=u.length := by
    simp only [z,p1Layout,List.length_append]
    omega
  refine ⟨⟨pre.length,z,a.length,?_,?_,?_,?_,?_⟩⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp only [z,p1Layout,pre,List.length_append]; omega
    · simp only [z,p1Layout,pre,List.length_append]; omega
    · simp only [z,p1Layout,pre,List.length_append]; omega
    · simp only [z,p1Layout,pre,List.length_append]; omega
    · simp only [z,p1Layout,pre,List.length_append]; omega
    · simp only [z,p1Layout,pre,List.length_append]; omega
    · simpa only [hD] using hd
    · simpa only [hU] using hu
    · simpa only [hF'] using hF
    · simpa only [hG'] using hG
    · simpa only [List.append_nil,hH'] using hH
    · rw [hV,hV']
  · rw [hlen]
    simp only [pre,List.length_append]
    omega
  · rw [hlen,hS,hU]
  · rwa [hA]
  · rw [hlen]
    have hstart : a.length+u.length=(a++u).length := by simp
    rw [hstart,← factor_slice f n _ _
      (by simp only [pre,List.length_append]; omega)
      (by simp only [pre,List.length_append]; omega),hC]
    exact hc

/-- Global geometric coverage now follows from original matching
    semantics, without an independently supplied absolute witness. -/
theorem p2_cover [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (n L D Q : Nat) (hm : MatchesWithin P.nested2 (segment f 0 n) 2)
    (hL : 0<L) (hD : 0<D) (hQL : Q≤L) :
    (∃ x,P2Periodic.Witness P f n [] [] x ∧
      GlobalCoverageP2.Residual f n L D Q x.p x.e x.k) ∨
      (SmallPeriodP2.solve P f n Q).accepted=true := by
  obtain ⟨x,hx⟩ := p2_of_match P f n hm
  rcases GlobalCoverageP2.cover P f n L D Q x hx hL hD hQL with h | h
  · exact Or.inl ⟨x,hx,h⟩
  · exact Or.inr h

theorem p1_cover (P : SevenDFA (Fin σ)) (f : Nat→Fin σ)
    (n L D Q : Nat) (hm : MatchesWithin P.nested1 (segment f 0 n) 2)
    (hL : 0<L) (hD : 0<D) (hQL : Q≤L) :
    (∃ w : GlobalCoverageP1.Witness P f n,
      GlobalCoverageP2.Residual f n L D Q w.outerStart w.target.e w.target.k) ∨
      (CountedP1Cubic.solve P f n Q).answer=true := by
  obtain ⟨w⟩ := p1_of_match P f n hm
  rcases GlobalCoverageP1.cover P f n L D Q w hL hD hQL with h | h
  · exact Or.inl ⟨w,h⟩
  · exact Or.inr h

end REWB.GlobalSemanticCoverage
