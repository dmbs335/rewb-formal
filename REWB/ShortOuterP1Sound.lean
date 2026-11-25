import REWB.ShortOuterP1Events
import REWB.ShortOuterWords
import REWB.ResidualDispatchQueries

/-! Exact P1 semantics of the actual short-outer event lists.  The earlier
inner source remains in absolute text coordinates and is never clipped
to the target's short outer window. -/
namespace REWB.ShortOuter.P1
open REWB.Periodic REWB.P2Periodic REWB.TimedJoin
variable {σ : Nat}

theorem match_sound (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit : Nat)
    (hm : Join.Match P.C text.toList (sources P (prepare P text fallback limit)).1
      (targets P (prepare P text fallback limit)).1) :
    ResidualDispatch.ShortP1 P (ArrayText.read text fallback) text.size limit := by
  obtain ⟨src,hsrc,tgt,htgt,hord,_,hkey,hC⟩:=hm
  obtain ⟨i,hi,len,hl,hil,hA,he⟩:=(sources_mem P _ src).mp hsrc
  subst src
  obtain ⟨p,hp,j,hj,t,ht,hjt,hpt,hD,hB,hR,he⟩:=(targets_mem P _ tgt).mp htgt
  subst tgt
  change i+len≤p at hord
  change Keys.get (Keys.build text fallback limit) i len=
    Keys.get (Keys.build text fallback limit) (p+j) (t-j) at hkey
  change i≤text.size at hi
  change p≤text.size at hp
  change len<min limit (text.size+1) at hl
  change j<min limit (text.size+1) at hj
  change t<min limit (text.size+1) at ht
  change p+t≤text.size at hpt
  have heq:=(Keys.get_eq_general text fallback limit i (p+j) len (t-j)
    hi (by omega) hl (by omega)).mp hkey
  have hlen : len=t-j := by
    have h:=congrArg List.length heq
    simpa only [segment_length] using h
  have ha:=(prefix_correct P text fallback limit i hi).mp hA
  have hd:=(prepare_d_correct P text fallback limit p j hp (by omega)).mp hD
  have hb:=(prepare_b_correct P text fallback limit (p+j) (t-j) (by omega) (by omega)).mp hB
  obtain ⟨ell,htell,hell,hpell,hF,k,hpk,hkn,heqOuter,hG,hH⟩:=
    (prepare_ready_correct P text fallback limit p t hp).mp hR
  let x : P1Target.Layout Nat:=⟨p+j,p+t,p+ell,k,k+ell⟩
  have hx : P1Target.Witness P (ArrayText.read text fallback) text.size p [] x := by
    refine ⟨by dsimp [x]; omega,by dsimp [x]; omega,by dsimp [x]; omega,hpk,
      by dsimp [x]; omega,hkn,?_,?_,hF,hG,?_,heqOuter⟩
    · simpa only [x,factor,Nat.add_sub_cancel_left] using hd
    · simpa only [x,factor,show p+t-(p+j)=t-j by omega] using hb
    · simpa only [x,List.append_nil] using hH
  let v : GlobalCoverageP1.Witness P (ArrayText.read text fallback) text.size:=
    ⟨p,x,i,hx,by dsimp [x]; omega,by
      simpa only [x,factor,show p+t-(p+j)=t-j by omega,hlen] using heq,ha,by
      simpa only [x,show p+t-(p+j)=len by omega,full_read,Join.entry,P1ShortSources.trueEntry] using hC⟩
  exact ⟨v,by dsimp [v,x]; omega⟩

theorem match_complete (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit : Nat) (hs : ResidualDispatch.ShortP1 P (ArrayText.read text fallback) text.size limit) :
    Join.Match P.C text.toList (sources P (prepare P text fallback limit)).1
      (targets P (prepare P text fallback limit)).1 := by
  obtain ⟨v,hshort⟩:=hs
  obtain ⟨hpj,hjt,hte,hek,hkf,hfn,hD,hB,hF,hG,hH,heqOuter⟩:=v.target_ok
  simp only [List.append_nil] at hH
  have hp : v.outerStart≤text.size := by omega
  have hi : v.earlierStart≤text.size := by have h:=v.earlier; omega
  have hlength:=congrArg List.length heqOuter
  simp only [factor,segment_length] at hlength
  let j:=v.target.j-v.outerStart
  let t:=v.target.t-v.outerStart
  let ell:=v.target.e-v.outerStart
  let len:=v.target.t-v.target.j
  have hjabs : v.outerStart+j=v.target.j := by dsimp [j]; omega
  have htabs : v.outerStart+t=v.target.t := by dsimp [t]; omega
  have heabs : v.outerStart+ell=v.target.e := by dsimp [ell]; omega
  have hfg : v.target.k+ell=v.target.f := by dsimp [ell]; omega
  have hinner : t-j=len := by dsimp [t,j,len]; omega
  have hwj : j<min limit (text.size+1) := by dsimp [j]; omega
  have hwt : t<min limit (text.size+1) := by dsimp [t]; omega
  have hwl : len<min limit (text.size+1) := by dsimp [len]; omega
  let es:=Join.entry (v.earlierStart+len)
    (Keys.get (prepare P text fallback limit).band.keys v.earlierStart len)
  let et:=Join.entry v.outerStart
    (Keys.get (prepare P text fallback limit).band.keys (v.outerStart+j) (t-j))
  have hsrc : es∈(sources P (prepare P text fallback limit)).1 := by
    apply (sources_mem P _ es).mpr
    refine ⟨v.earlierStart,hi,len,hwl,?_,?_,rfl⟩
    · have h:=v.earlier
      change v.earlierStart+len≤text.size
      dsimp [len]
      omega
    · exact (prefix_correct P text fallback limit v.earlierStart hi).mpr v.prefix_ok
  have htgt : et∈(targets P (prepare P text fallback limit)).1 := by
    apply (targets_mem P _ et).mpr
    refine ⟨v.outerStart,hp,j,hwj,t,hwt,?_,?_,?_,?_,?_,rfl⟩
    · dsimp [j,t]; omega
    · change v.outerStart+t≤text.size
      rw [htabs]
      omega
    · apply (prepare_d_correct P text fallback limit v.outerStart j hp (by omega)).mpr
      exact hD
    · apply (prepare_b_correct P text fallback limit (v.outerStart+j) (t-j)
        (by rw [hjabs]; omega) (by omega)).mpr
      simpa only [hjabs,hinner,len,factor] using hB
    · apply (prepare_ready_correct P text fallback limit v.outerStart t hp).mpr
      refine ⟨ell,by dsimp [t,ell]; omega,hshort,by rw [heabs]; omega,?_,
        v.target.k,by rw [heabs]; exact hek,by rw [hfg]; exact hfn,?_,?_,?_⟩
      · simpa only [htabs,heabs] using hF
      · simpa only [heabs,hfg] using heqOuter
      · simpa only [heabs] using hG
      · simpa only [hfg] using hH
  refine ⟨es,hsrc,et,htgt,v.earlier,by exact hp,?_,?_⟩
  · change Keys.get (Keys.build text fallback limit) v.earlierStart len=
      Keys.get (Keys.build text fallback limit) (v.outerStart+j) (t-j)
    apply (Keys.get_eq_general text fallback limit v.earlierStart (v.outerStart+j) len (t-j)
      hi (by rw [hjabs]; omega) hwl (by omega)).mpr
    simpa only [hjabs,hinner,len,factor] using v.equal_inner
  · simpa only [es,et,Join.entry,P1ShortSources.trueEntry,len,full_read] using v.gap_ok

theorem match_iff (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    Join.Match P.C text.toList (sources P (prepare P text fallback limit)).1
      (targets P (prepare P text fallback limit)).1 ↔
      ResidualDispatch.ShortP1 P (ArrayText.read text fallback) text.size limit :=
  ⟨match_sound P text fallback limit,match_complete P text fallback limit⟩

end REWB.ShortOuter.P1
