import REWB.ShortOuterP2Events
import REWB.ShortOuterWords
import REWB.ResidualDispatchQueries

/-! Exact P2 semantics of the actual local offset joins.  The local word
has only the bounded width, so each outer start incurs one short join;
the global exact-key dictionary is shared by every such join. -/
namespace REWB.ShortOuter.P2
open REWB.Periodic REWB.P2Periodic REWB.TimedJoin
variable {σ : Nat}

def At (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p : Nat) : Prop :=
  ∃x : P2Periodic.Layout Nat,x.p=p ∧
    P2Periodic.Witness P (ArrayText.read text fallback) text.size [] [] x ∧ x.e-x.p<limit

theorem match_sound (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p : Nat) (hp : p≤text.size)
    (hA : prefixOK P (prepare P text fallback limit) p=true)
    (hm : Join.Match P.D (segment (ArrayText.read text fallback) p (min limit (text.size+1)))
      (sources P (prepare P text fallback limit) p).1
      (targets P (prepare P text fallback limit) p).1) : At P text fallback limit p := by
  obtain ⟨src,hsrc,tgt,htgt,hord,_,hkey,hD⟩:=hm
  obtain ⟨i,hi,a,ha,hia,hpa,hB,hC,he⟩:=(sources_mem P _ p src).mp hsrc
  subst src
  obtain ⟨j,hj,t,ht,hjt,hpt,hR,he⟩:=(targets_mem P _ p tgt).mp htgt
  subst tgt
  change a≤j at hord
  change i<min limit (text.size+1) at hi
  change a<min limit (text.size+1) at ha
  change j<min limit (text.size+1) at hj
  change t<min limit (text.size+1) at ht
  change p+a≤text.size at hpa
  change p+t≤text.size at hpt
  change Keys.get (Keys.build text fallback limit) (p+i) (a-i)=
    Keys.get (Keys.build text fallback limit) (p+j) (t-j) at hkey
  have heq:=(Keys.get_eq_general text fallback limit (p+i) (p+j) (a-i) (t-j)
    (by omega) (by omega) (by omega) (by omega)).mp hkey
  have hA':=(prefix_correct P text fallback limit p hp).mp hA
  have hB':=(prepare_b_correct P text fallback limit p i hp (by omega)).mp hB
  have hC':=(prepare_c_correct P text fallback limit (p+i) (a-i) (by omega) (by omega)).mp hC
  change P.D.accepts (Spec.slice (segment (ArrayText.read text fallback) p
    (min limit (text.size+1))) a j) at hD
  rw [Ready.slice_segment _ p _ a j hord (by omega)] at hD
  obtain ⟨ell,htell,hell,hpell,hF,k,hpk,hkn,heqOuter,hG,hH⟩:=
    (prepare_ready_correct P text fallback limit p t hp).mp hR
  let x : P2Periodic.Layout Nat:=⟨p,p+i,p+a,p+j,p+t,p+ell,k,k+ell⟩
  refine ⟨x,rfl,?_,by dsimp [x]; omega⟩
  refine ⟨by dsimp [x]; omega,by dsimp [x]; omega,by dsimp [x]; omega,
    by dsimp [x]; omega,by dsimp [x]; omega,hpk,by dsimp [x]; omega,hkn,
    ?_,?_,?_,?_,hF,hG,?_,?_,heqOuter⟩
  · simpa only [x,List.nil_append,factor,Nat.sub_zero] using hA'
  · simpa only [x,factor,Nat.add_sub_cancel_left] using hB'
  · simpa only [x,factor,show p+a-(p+i)=a-i by omega] using hC'
  · simpa only [x,factor,show p+j-(p+a)=j-a by omega] using hD
  · simpa only [x,List.append_nil] using hH
  · simpa only [x,factor,show p+a-(p+i)=a-i by omega,
      show p+t-(p+j)=t-j by omega] using heq

theorem match_complete (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit : Nat) (x : P2Periodic.Layout Nat)
    (hx : P2Periodic.Witness P (ArrayText.read text fallback) text.size [] [] x)
    (hshort : x.e-x.p<limit) :
    prefixOK P (prepare P text fallback limit) x.p=true ∧
    Join.Match P.D (segment (ArrayText.read text fallback) x.p (min limit (text.size+1)))
      (sources P (prepare P text fallback limit) x.p).1
      (targets P (prepare P text fallback limit) x.p).1 := by
  obtain ⟨hpi,hia,haj,hjt,hte,hek,hkf,hfn,hA,hB,hC,hD,hF,hG,hH,heq,heqOuter⟩:=hx
  simp only [List.nil_append,List.append_nil] at hA hH
  have hp : x.p≤text.size := by omega
  have hlength:=congrArg List.length heqOuter
  simp only [factor,segment_length] at hlength
  let i:=x.i-x.p
  let a:=x.a-x.p
  let j:=x.j-x.p
  let t:=x.t-x.p
  let ell:=x.e-x.p
  have hiabs : x.p+i=x.i := by dsimp [i]; omega
  have haabs : x.p+a=x.a := by dsimp [a]; omega
  have hjabs : x.p+j=x.j := by dsimp [j]; omega
  have htabs : x.p+t=x.t := by dsimp [t]; omega
  have heabs : x.p+ell=x.e := by dsimp [ell]; omega
  have hfg : x.k+ell=x.f := by dsimp [ell]; omega
  have hwi : i<min limit (text.size+1) := by dsimp [i]; omega
  have hwa : a<min limit (text.size+1) := by dsimp [a]; omega
  have hwj : j<min limit (text.size+1) := by dsimp [j]; omega
  have hwt : t<min limit (text.size+1) := by dsimp [t]; omega
  have hasub : a-i=x.a-x.i := by dsimp [a,i]; omega
  have htsub : t-j=x.t-x.j := by dsimp [t,j]; omega
  have hdsub : j-a=x.j-x.a := by dsimp [j,a]; omega
  let es:=Join.entry a (Keys.get (prepare P text fallback limit).band.keys (x.p+i) (a-i))
  let et:=Join.entry j (Keys.get (prepare P text fallback limit).band.keys (x.p+j) (t-j))
  have hsrc : es∈(sources P (prepare P text fallback limit) x.p).1 := by
    apply (sources_mem P _ x.p es).mpr
    refine ⟨i,hwi,a,hwa,by dsimp [i,a]; omega,?_,?_,?_,rfl⟩
    · change x.p+a≤text.size
      rw [haabs]
      omega
    · apply (prepare_b_correct P text fallback limit x.p i hp (by omega)).mpr
      exact hB
    · apply (prepare_c_correct P text fallback limit (x.p+i) (a-i)
        (by rw [hiabs]; omega) (by omega)).mpr
      simpa only [hiabs,hasub,factor] using hC
  have htgt : et∈(targets P (prepare P text fallback limit) x.p).1 := by
    apply (targets_mem P _ x.p et).mpr
    refine ⟨j,hwj,t,hwt,by dsimp [j,t]; omega,?_,?_,rfl⟩
    · change x.p+t≤text.size
      rw [htabs]
      omega
    · apply (prepare_ready_correct P text fallback limit x.p t hp).mpr
      refine ⟨ell,by dsimp [t,ell]; omega,hshort,by rw [heabs]; omega,?_,
        x.k,by rw [heabs]; exact hek,by rw [hfg]; exact hfn,?_,?_,?_⟩
      · simpa only [htabs,heabs] using hF
      · simpa only [heabs,hfg] using heqOuter
      · simpa only [heabs] using hG
      · simpa only [hfg] using hH
  refine ⟨(prefix_correct P text fallback limit x.p hp).mpr (by simpa [factor] using hA),
    es,hsrc,et,htgt,by change a≤j; dsimp [a,j]; omega,?_,?_,?_⟩
  · change j≤(segment (ArrayText.read text fallback) x.p (min limit (text.size+1))).length
    rw [segment_length]
    omega
  · change Keys.get (Keys.build text fallback limit) (x.p+i) (a-i)=
      Keys.get (Keys.build text fallback limit) (x.p+j) (t-j)
    apply (Keys.get_eq_general text fallback limit (x.p+i) (x.p+j) (a-i) (t-j)
      (by rw [hiabs]; omega) (by rw [hjabs]; omega) (by omega) (by omega)).mpr
    simpa only [hiabs,hjabs,hasub,htsub,factor] using heq
  · change P.D.accepts (Spec.slice (segment (ArrayText.read text fallback) x.p
      (min limit (text.size+1))) a j)
    rw [Ready.slice_segment _ x.p _ a j (by dsimp [a,j]; omega) (by omega)]
    simpa only [haabs,hdsub,factor] using hD

theorem match_iff (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p : Nat) (hp : p≤text.size) :
    (prefixOK P (prepare P text fallback limit) p=true ∧
      Join.Match P.D (segment (ArrayText.read text fallback) p (min limit (text.size+1)))
        (sources P (prepare P text fallback limit) p).1
        (targets P (prepare P text fallback limit) p).1) ↔ At P text fallback limit p := by
  constructor
  · rintro ⟨hA,hm⟩
    exact match_sound P text fallback limit p hp hA hm
  · rintro ⟨x,hxp,hx,hs⟩
    subst p
    exact match_complete P text fallback limit x hx hs

end REWB.ShortOuter.P2
