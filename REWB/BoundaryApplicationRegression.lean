import REWB.BoundaryApplicationQuery

/-! Kernel regressions for the fully constructed fixed-end color index.
The suffix machine forgets its incoming state after one letter, making
empty and terminal interval handling observable. -/
namespace REWB.BoundaryApplication.Regression

def colors : DFA (Fin 2) := ⟨2,0,fun _ a=>a,fun _=>true⟩
def suffix : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩

theorem empty_mass :
    (Versions.root (FixedEnd.build colors suffix [] 0 0 (Nat.le_refl _)).versions).totalMass=2 :=
  FixedEnd.build_mass colors suffix [] 0 0 (Nat.le_refl _)

theorem root_query (w : Word (Fin 2)) (g : Nat) (hg : g≤w.length)
    (r : Nat) (hr : r≤w.length) :
    (FixedEnd.queryPath colors suffix w (FixedEnd.build colors suffix w 0 g hg) [] (fun _=>true) r).1=
      some true ↔ g≤r := by
  rw [FixedEnd.queryPath_correct colors suffix w 0 g hg (FixedEnd.trie w 0 g hg).tree []
    (subtree_nil w _) (fun _=>true) r hr]
  constructor
  · rintro ⟨a,ha,t,ht,htr,_,_⟩
    have hv:=FixedEnd.trie_valid w 0 g hg a ha
    simp only [ValidKey,originalKey] at hv
    rw [ht] at hv
    have hh:=hv.1
    omega
  · intro hgr
    let t : Fin (w.length+1):=⟨r,by omega⟩
    obtain ⟨a,ha,ht⟩:=FixedEnd.trie_target w 0 g hg t hgr
    refine ⟨a,ha,t,ht,Nat.le_refl _,rfl,?_⟩
    change suffix.accepts (Spec.slice w r r)
    simp only [Spec.slice,Nat.sub_self,List.take_zero,DFA.accepts,DFA.run,suffix]
    decide

theorem empty_query :
    (FixedEnd.queryPath colors suffix [] (FixedEnd.build colors suffix [] 0 0 (Nat.le_refl _))
      [] (fun _=>true) 0).1=some true :=
  (root_query [] 0 (Nat.le_refl _) 0 (Nat.le_refl _)).mpr (Nat.le_refl _)

theorem terminal_query (w : Word (Fin 2)) :
    (FixedEnd.queryPath colors suffix w (FixedEnd.build colors suffix w 0 w.length (Nat.le_refl _))
      [] (fun _=>true) w.length).1=some true :=
  (root_query w w.length (Nat.le_refl _) w.length (Nat.le_refl _)).mpr (Nat.le_refl _)

theorem before_terminal (w : Word (Fin 2)) (r : Nat) (hr : r<w.length) :
    ¬(FixedEnd.queryPath colors suffix w (FixedEnd.build colors suffix w 0 w.length (Nat.le_refl _))
      [] (fun _=>true) r).1=some true := by
  rw [root_query w w.length (Nat.le_refl _) r (Nat.le_of_lt hr)]
  omega

end REWB.BoundaryApplication.Regression
