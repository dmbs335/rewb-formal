import REWB.MaskedAllStartCorrect

namespace REWB.MaskedAllStart.Regression
variable {σ : Nat}

theorem disabled_source (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (p : Nat) (hp : MaskedProgression.readMask source p=false) :
    MaskedProgression.readMask (solve B C E text fallback source target).bits p=false := by
  cases hb : MaskedProgression.readMask (solve B C E text fallback source target).bits p with
  | false=>rfl
  | true=>
    have hh:=(solve_correct B C E text fallback source target p).mp hb
    rw [hp] at hh
    cases hh.1

theorem empty_target (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source : Array Bool) (p : Nat) :
    MaskedProgression.readMask (solve B C E text fallback source #[]).bits p=false := by
  cases hb : MaskedProgression.readMask (solve B C E text fallback source #[]).bits p with
  | false=>rfl
  | true=>
    obtain ⟨_,a,j,t,_,_,_,_,ht,_⟩:=(solve_correct B C E text fallback source #[] p).mp hb
    simp only [MaskedProgression.readMask,Array.getElem?_empty,Option.getD_none] at ht
    cases ht

def odd : DFA (Fin 2):=⟨2,0,fun q _=>if q=0 then 1 else 0,fun q=>q==1⟩
def any : DFA (Fin 2):=⟨1,0,fun _ _=>0,fun _=>true⟩

theorem separated_one_letter :
    MaskedProgression.readMask (solve odd any any #[0,1,0] 0 #[true] #[false,false,true]).bits 0=true := by
  apply (solve_correct odd any any #[0,1,0] 0 #[true] #[false,false,true] 0).mpr
  refine ⟨rfl,1,2,3,by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl⟩

end REWB.MaskedAllStart.Regression
