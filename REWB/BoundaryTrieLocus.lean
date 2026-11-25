import REWB.BoundaryTrieBuild

/-! Complete prefix classes occur at the first node reaching a requested
depth. Equal-depth binary refinements need not be complete classes; the
strict ancestor test in `Locus` deliberately excludes them. -/
namespace REWB.BoundaryTrie.Tree
variable {n σ : Nat} {ρ : Type}

inductive Locus : Tree n ρ→Nat→Tree n ρ→Prop
  | here (t : Tree n ρ) {d} : d≤depth t→Locus t d t
  | left {stem e l r d u} : e<d→Locus l d u→Locus (.node stem e l r) d u
  | right {stem e l r d u} : e<d→Locus r d u→Locus (.node stem e l r) d u

theorem locus_first {t u : Tree n ρ} {d : Nat}
    (hd : d≤depth t) (hl : Locus t d u) : u=t := by
  cases hl with
  | here _ _ => rfl
  | left he _ => simp only [depth] at hd; omega
  | right he _ => simp only [depth] at hd; omega

theorem locus_good (f : Nat→Fin σ) {t u : Tree n ρ} {d : Nat}
    (hg : Good f t) (hl : Locus t d u) : Good f u := by
  induction hl with
  | here _ _ => exact hg
  | left _ _ ih => exact ih hg.1
  | right _ _ ih => exact ih hg.2.1

theorem locus_depth {t u : Tree n ρ} {d : Nat} (hl : Locus t d u) : d≤depth u := by
  induction hl with
  | here _ h => exact h
  | left _ _ ih => exact ih
  | right _ _ ih => exact ih

theorem locus_mem {t u : Tree n ρ} {d : Nat} (hl : Locus t d u)
    (a : Key n ρ) (ha : a∈leaves u) : a∈leaves t := by
  induction hl with
  | here _ _ => exact ha
  | left _ _ ih => exact List.mem_append_left _ (ih ha)
  | right _ _ ih => exact List.mem_append_right _ (ih ha)

/-- Every descriptor in the whole tree with the same d-symbol prefix
as a descriptor at the locus belongs to that locus, and conversely. -/
theorem locus_complete (f : Nat→Fin σ) {t u : Tree n ρ} {d : Nat}
    (hg : Good f t) (hl : Locus t d u) (a b : Key n ρ)
    (ha : a∈leaves u) (hb : b∈leaves t) :
    Key.Common f a b d ↔ b∈leaves u := by
  induction hl with
  | here t hd =>
    exact ⟨fun _=>hb,fun _=>Key.common_shorten f a b (depth t) _
      (depth_common f t hg a b ha hb) hd⟩
  | @left stem e l r d u he hl ih =>
    have hal:=locus_mem hl a ha
    rcases List.mem_append.mp hb with hbl | hbr
    · exact ih hg.1 ha hbl
    · have hcross:=hg.2.2.2.2.2.2 a hal b hbr
      constructor
      · intro hc
        have hh:=hcross.2 d hc
        omega
      · intro hbu
        have hc:=depth_common f u (locus_good f hg.1 hl) a b ha hbu
        have hd:=locus_depth hl
        have hh:=hcross.2 d (Key.common_shorten f a b (depth u) d hc hd)
        omega
  | @right stem e l r d u he hl ih =>
    have har:=locus_mem hl a ha
    rcases List.mem_append.mp hb with hbl | hbr
    · have hcross:=hg.2.2.2.2.2.2 b hbl a har
      constructor
      · intro hc
        have hh:=hcross.2 d ((Key.common_symmetric _ _ _ _).mp hc)
        omega
      · intro hbu
        have hc:=depth_common f u (locus_good f hg.2.1 hl) a b ha hbu
        have hd:=locus_depth hl
        have hh:=hcross.2 d ((Key.common_symmetric _ _ _ _).mp
          (Key.common_shorten f a b (depth u) d hc hd))
        omega
    · exact ih hg.2.1 ha hbr

/-- Follow an actual terminal path, stopping at the first node whose
depth reaches d. Nodes at equal depth below that node are not selected. -/
def locate.go (d : Nat) : List Bool→Tree n ρ→Option (Tree n ρ)
  | [],t => if d≤depth t then some t else none
  | b::tail,t =>
    if d≤depth t then some t
    else match t with
      | .node _ _ l r => go d tail (if b then r else l)
      | _ => none

def locate (d : Nat) (t : Tree n ρ) (path : List Bool) : Option (Tree n ρ) :=
  locate.go d path t

theorem locate_correct (f : Nat→Fin σ) (t : Tree n ρ) (path : List Bool)
    (a : Key n ρ) (d : Nat) (hg : Good f t)
    (hp : lookup t path=some a) (hd : d≤a.length) :
    ∃u,locate d t path=some u ∧ Locus t d u ∧ a∈leaves u := by
  induction path generalizing t with
  | nil =>
    cases t with
    | empty => cases hp
    | leaf b =>
      simp only [lookup,Option.some.injEq] at hp
      subst b
      exact ⟨.leaf a,by simp only [locate,locate.go,depth,hd,if_true],.here _ hd,
        by simp only [leaves,List.mem_singleton]⟩
    | node _ _ _ _ => cases hp
  | cons b path ih =>
    by_cases hdt : d≤depth t
    · exact ⟨t,by simp only [locate,locate.go,if_pos hdt],.here _ hdt,lookup_mem t (b::path) a hp⟩
    · cases t with
      | empty => cases hp
      | leaf _ => cases hp
      | node stem e l r =>
        have he : e<d := by change ¬d≤e at hdt; omega
        cases b with
        | false =>
          obtain ⟨u,hu,hl,ha⟩:=ih l hg.1 hp
          exact ⟨u,by simpa only [locate,locate.go,depth,if_neg (by omega : ¬d≤e),
            Bool.false_eq_true,if_false] using hu,
            .left he hl,ha⟩
        | true =>
          obtain ⟨u,hu,hl,ha⟩:=ih r hg.2.1 hp
          exact ⟨u,by simpa only [locate,locate.go,depth,if_neg (by omega : ¬d≤e),if_true] using hu,
            .right he hl,ha⟩

end REWB.BoundaryTrie.Tree

namespace REWB.BoundaryTrie.Build
variable {σ : Nat} {ρ : Type}

theorem run_locus_complete (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) (path : List Bool)
    (a b : Key text.size ρ) (d : Nat)
    (hp : (run text fallback descriptors).tree.lookup path=some a)
    (hd : d≤a.length) (hb : b∈descriptors) :
    ∃u,Tree.locate d (run text fallback descriptors).tree path=some u ∧
      Tree.Locus (run text fallback descriptors).tree d u ∧
      (Key.Common (ArrayText.read text fallback) a b d ↔ b∈u.leaves) := by
  have hg:=(run_correct text fallback descriptors).2.1
  obtain ⟨u,hu,hl,ha⟩:=Tree.locate_correct _ _ path a d hg hp hd
  have hb':= (run_correct text fallback descriptors).1.mem_iff.mpr hb
  exact ⟨u,hu,hl,Tree.locus_complete _ hg hl a b ha hb'⟩

end REWB.BoundaryTrie.Build
