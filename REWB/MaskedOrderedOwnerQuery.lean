import REWB.MaskedOrderedOwnerQualified

/-! A constant number of indexed operations validates a generated pair
against its owner's completed persistent snapshot. Only surviving
adjacencies reach the existing guarded LCE/LCS extension. -/
namespace REWB.MaskedOrdered.Owner
open REWB.RunGeometry (Bounds)
open REWB.MaskedRunDiscovery (Adjacent Complete discover)
variable {h σ : Nat}

def probe (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (e : Event) : Option Bounds×Nat :=
  match nodes[e.owner]? with
  | none => (none,2)
  | some rec =>
    let membership:=Tree.contains rec.state.tree cap e.edge.1
    let next:=Tree.succ rec.state.tree cap e.edge.1
    if membership.1 && decide (next.1=some e.edge.2) then
      let r:=discover forward backward n e.edge.1 e.edge.2 rec.depth
      (r.1,r.2+membership.2+next.2+8)
    else (none,membership.2+next.2+8)

theorem succ_of_adjacent (t : Tree h) (cap i j : Nat) (hg : t.Good) (hf : t.Fits 0)
    (hc : cap=2^h) (ha : Adjacent t.entries i j) : (Tree.succ t cap i).1=some j := by
  apply succ_unique t.entries i _ (some j) (Tree.succ_correct t cap i hg hf hc)
  refine ⟨ha.2.1,ha.2.2.1,?_⟩
  intro k hk hik
  by_cases hh : j≤k
  · exact hh
  · exact False.elim (ha.2.2.2 k hk hik (by omega))

theorem probe_accept (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (e : Event) (rec : Record h)
    (hr : nodes[e.owner]?=some rec) (hv : rec.state.Valid) (hc : cap=2^h)
    (ha : Adjacent rec.state.tree.entries e.edge.1 e.edge.2) :
    (probe forward backward n cap nodes e).1=
      (discover forward backward n e.edge.1 e.edge.2 rec.depth).1 := by
  have hm:=(Tree.contains_correct _ _ _ hv.2.1 hc).mpr ha.1
  have hs:=succ_of_adjacent rec.state.tree cap e.edge.1 e.edge.2 hv.1 hv.2.1 hc ha
  simp only [probe,hr,hm,hs,decide_true,Bool.true_and,if_true]

theorem probe_data (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (e : Event) (R : Bounds)
    (he : (probe forward backward n cap nodes e).1=some R) :
    ∃rec,nodes[e.owner]?=some rec ∧
      (Tree.contains rec.state.tree cap e.edge.1).1=true ∧
      (Tree.succ rec.state.tree cap e.edge.1).1=some e.edge.2 ∧
      (discover forward backward n e.edge.1 e.edge.2 rec.depth).1=some R := by
  cases hr : nodes[e.owner]? with
  | none => simp only [probe,hr] at he; cases he
  | some rec =>
    simp only [probe,hr] at he
    split at he
    next hh =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
      exact ⟨rec,rfl,hh.1,hh.2,he⟩
    next hh => cases he

theorem checked_adjacent (rec : Record h) (cap : Nat) (e : Event) (hv : rec.state.Valid)
    (hc : cap=2^h) (hm : (Tree.contains rec.state.tree cap e.edge.1).1=true)
    (hs : (Tree.succ rec.state.tree cap e.edge.1).1=some e.edge.2) :
    Adjacent rec.state.tree.entries e.edge.1 e.edge.2 := by
  have hi:=(Tree.contains_correct _ _ _ hv.2.1 hc).mp hm
  have hj:=Tree.succ_correct rec.state.tree cap e.edge.1 hv.1 hv.2.1 hc
  rw [hs] at hj
  refine ⟨hi,hj.1,hj.2.1,?_⟩
  intro k hk hik hkj
  have hh:=hj.2.2 k hk hik
  omega

theorem discover_some_guard (forward backward : RankIndex.Index) (n i j L : Nat) (R : Bounds)
    (he : (discover forward backward n i j L).1=some R) :
    i<j ∧ j+L≤n ∧ 2*(j-i)≤L := by
  simp only [discover] at he
  split at he
  next hh => exact hh
  next hh => cases he

theorem probe_sound (f : Nat→Fin σ) (n cap : Nat)
    (nodes : Array (Record h)) (e : Event) (R : Bounds) (hc : cap=2^h)
    (hcert : ∀rec,nodes[e.owner]?=some rec→rec.state.Valid ∧
      ∃base,Complete f n base rec.depth rec.state.tree.entries)
    (he : (probe (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) n cap nodes e).1=some R) :
    R.Valid f n ∧ R.period=e.edge.2-e.edge.1 ∧ 3*R.period≤R.hi-R.lo := by
  obtain ⟨rec,hr,hm,hs,hext⟩:=probe_data _ _ _ _ _ _ _ he
  obtain ⟨hv,base,hfull⟩:=hcert rec hr
  have ha:=checked_adjacent rec cap e hv hc hm hs
  have hg:=discover_some_guard _ _ _ _ _ _ R hext
  obtain ⟨S,hS,hvS,hper,_,_,hcub⟩:=
    MaskedRunDiscovery.complete_discovery f n base rec.depth rec.state.tree.entries
      e.edge.1 e.edge.2 hfull ha hg.2.2
  have hEq : S=R := Option.some.inj (hS.symm.trans hext)
  subst S
  exact ⟨hvS,hper,hcub⟩

def probeBudget (h n : Nat) : Nat := 11*h+26*(n.log2+1)+27

theorem probe_work (f : Nat→Fin σ) (n cap : Nat) (nodes : Array (Record h)) (e : Event) :
    (probe (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) n cap nodes e).2≤probeBudget h n := by
  cases hr : nodes[e.owner]? with
  | none => simp only [probe,hr,probeBudget]; omega
  | some rec =>
    have hm:=Tree.contains_work rec.state.tree cap e.edge.1
    have hs:=Tree.succ_work rec.state.tree cap e.edge.1
    have hd:=MaskedRunDiscovery.discover_work f n e.edge.1 e.edge.2 rec.depth
    simp only [probe,hr,probeBudget]
    split <;> dsimp only <;> omega

end REWB.MaskedOrdered.Owner
