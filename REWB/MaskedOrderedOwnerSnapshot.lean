import REWB.MaskedOrderedOwner

/-! Exact saved-node and fresh-generation provenance for the concrete
preorder traversal. Locations are proof witnesses for IDs already
allocated by the execution, not an executable traversal or supplied
index. -/
namespace REWB.MaskedOrdered.Owner
open REWB.BoundaryTrie (Key)
open REWB.MaskedRunDiscovery (positions Adjacent)
open REWB.MaskedEventBudget (edges)
variable {h n : Nat}

inductive Location : Trie n Nat→Option Parent→Nat→Trie n Nat→Option Parent→Nat→Prop
  | here (t parent base) : Location t parent base t parent base
  | left {stem d l r parent base u pu id} :
      Location l (some ⟨d,select parent d base⟩) (base+1) u pu id →
      Location (.node stem d l r) parent base u pu id
  | right {stem d l r parent base u pu id} :
      Location r (some ⟨d,select parent d base⟩) (base+1+slots l) u pu id →
      Location (.node stem d l r) parent base u pu id

theorem slots_pos (t : Trie n Nat) : 0<slots t := by
  cases t <;> simp [slots]

theorem location_bounds {t u : Trie n Nat} {parent pu : Option Parent} {base id : Nat}
    (hl : Location t parent base u pu id) : base≤id ∧ id<base+slots t := by
  induction hl with
  | here t parent base => have hh:=slots_pos t; omega
  | @left stem d l r parent base u pu id hh ih => simp only [slots]; omega
  | @right stem d l r parent base u pu id hh ih => simp only [slots]; omega

def Snapshot (t : Trie n Nat) (parent : Option Parent) (id : Nat) (r : Record h) : Prop :=
  r.depth=t.depth ∧ r.owner=select parent t.depth id ∧ r.children=childIds t id ∧
    r.state.Valid ∧ ∀p,p∈r.state.tree.entries↔p∈positions t

theorem visit_at (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (hc : cap=2^h) (hb : PositionsBounded h t) (u : Trie n Nat) (pu : Option Parent) (id : Nat)
    (hl : Location t parent s.nodes.size u pu id) :
    ∃r,(visit cap t parent s).2.nodes[id]?=some r ∧ Snapshot u pu id r := by
  induction t generalizing parent s u pu id with
  | empty =>
    cases hl
    refine ⟨_,visit_root _ _ _ _,rfl,rfl,rfl,visit_valid _ _ _ _ hc hb,?_⟩
    exact visit_mem _ _ _ _ hc hb
  | leaf a =>
    cases hl
    refine ⟨_,visit_root _ _ _ _,rfl,rfl,rfl,visit_valid _ _ _ _ hc hb,?_⟩
    exact visit_mem _ _ _ _ hc hb
  | node stem d l r il ir =>
    cases hl with
    | here =>
      refine ⟨_,visit_root _ _ _ _,rfl,rfl,rfl,visit_valid _ _ _ _ hc hb,?_⟩
      exact visit_mem _ _ _ _ hc hb
    | left hh =>
      let next:=some (Parent.mk d (select parent d s.nodes.size))
      let pushed : Store h:=⟨s.nodes.push ⟨d,select parent d s.nodes.size,none,State.empty h⟩,
        s.events,s.work+12⟩
      let a:=visit cap l next pushed
      obtain ⟨rec,hget,hs⟩:=il next pushed (positions_left _ _ _ _ hb) u pu id
        (by simpa only [pushed,Array.size_push] using hh)
      have hlo:=location_bounds hh
      have hbound : id<a.2.nodes.size:=(Array.getElem?_eq_some_iff.mp hget).1
      refine ⟨rec,?_,hs⟩
      simp only [visit]
      rw [Array.getElem?_setIfInBounds_ne (by omega : s.nodes.size≠id)]
      rw [visit_prefix _ _ _ _ id hbound]
      exact hget
    | right hh =>
      let next:=some (Parent.mk d (select parent d s.nodes.size))
      let pushed : Store h:=⟨s.nodes.push ⟨d,select parent d s.nodes.size,none,State.empty h⟩,
        s.events,s.work+12⟩
      let a:=visit cap l next pushed
      have hsize : a.2.nodes.size=s.nodes.size+1+slots l:=by
        simpa only [pushed,Array.size_push] using visit_size cap l next pushed
      have hh' : Location r next a.2.nodes.size u pu id := by rw [hsize]; exact hh
      obtain ⟨rec,hget,hs⟩:=ir next a.2 (positions_right _ _ _ _ hb) u pu id hh'
      have hlo:=location_bounds hh
      refine ⟨rec,?_,hs⟩
      simp only [visit]
      rw [Array.getElem?_setIfInBounds_ne (by omega : s.nodes.size≠id)]
      exact hget

theorem visit_adjacent (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (hc : cap=2^h) (hb : PositionsBounded h t) (i j : Nat) (ha : Adjacent (positions t) i j) :
    (i,j)∈edges (visit cap t parent s).1.tree.entries := by
  have hv:=visit_valid cap t parent s hc hb
  have hm:=visit_mem cap t parent s hc hb
  apply MaskedRunDiscovery.adjacent_edge _ i j (Tree.ordered _ _ hv.2.1)
  refine ⟨(hm i).mpr ha.1,(hm j).mpr ha.2.1,ha.2.2.1,?_⟩
  intro k hk hik hkj
  exact ha.2.2.2 k ((hm k).mp hk) hik hkj

/-- The pair is adjacent at completion of this binary split and neither
child already contains both ends. Its actual local merge therefore emits
a generation carrying this split's propagated complete-owner ID. -/
theorem visit_split_event (cap : Nat) (stem : Key n Nat) (d : Nat) (l r : Trie n Nat)
    (parent : Option Parent) (s : Store h) (hc : cap=2^h)
    (hb : PositionsBounded h (.node stem d l r)) (i j : Nat)
    (ha : Adjacent (positions (.node stem d l r)) i j)
    (hal : ¬(i∈positions l ∧ j∈positions l))
    (har : ¬(i∈positions r ∧ j∈positions r)) :
    (⟨select parent d s.nodes.size,(i,j)⟩ : Event)∈
      (visit cap (.node stem d l r) parent s).2.events.toList := by
  let next:=some (Parent.mk d (select parent d s.nodes.size))
  let pushed : Store h:=⟨s.nodes.push ⟨d,select parent d s.nodes.size,none,State.empty h⟩,
    s.events,s.work+12⟩
  let a:=visit cap l next pushed
  let b:=visit cap r next a.2
  have hl:=positions_left _ _ _ _ hb
  have hr:=positions_right _ _ _ _ hb
  have he:=visit_adjacent cap (.node stem d l r) parent s hc hb i j ha
  have he' : (i,j)∈(merge cap a.1 b.1 {}).2.fresh := by
    apply merge_new_edge cap a.1 b.1 {} (visit_valid _ _ _ _ hc hl)
      (visit_valid _ _ _ _ hc hr) hc (i,j) he
    · intro hedge
      have hm:=MaskedRunDiscovery.edge_members _ i j hedge
      exact hal ⟨(visit_mem cap l next pushed hc hl i).mp hm.1,
        (visit_mem cap l next pushed hc hl j).mp hm.2⟩
    · intro hedge
      have hm:=MaskedRunDiscovery.edge_members _ i j hedge
      exact har ⟨(visit_mem cap r next a.2 hc hr i).mp hm.1,
        (visit_mem cap r next a.2 hc hr j).mp hm.2⟩
  apply (emit_mem _ _ _ _).mpr
  exact Or.inr ⟨(i,j),he',rfl⟩

theorem visit_at_event (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (hc : cap=2^h) (hb : PositionsBounded h t)
    (stem : Key n Nat) (d : Nat) (l r : Trie n Nat) (pu : Option Parent) (id i j : Nat)
    (hl : Location t parent s.nodes.size (.node stem d l r) pu id)
    (ha : Adjacent (positions (.node stem d l r)) i j)
    (hal : ¬(i∈positions l ∧ j∈positions l))
    (har : ¬(i∈positions r ∧ j∈positions r)) :
    (⟨select pu d id,(i,j)⟩ : Event)∈(visit cap t parent s).2.events.toList := by
  induction t generalizing parent s with
  | empty => cases hl
  | leaf a => cases hl
  | node st depth a b ia ib =>
    cases hl with
    | here => exact visit_split_event _ _ _ _ _ _ _ hc hb i j ha hal har
    | left hh =>
      let next:=some (Parent.mk depth (select parent depth s.nodes.size))
      let pushed : Store h:=⟨s.nodes.push ⟨depth,select parent depth s.nodes.size,none,State.empty h⟩,
        s.events,s.work+12⟩
      have he:=ia next pushed (positions_left _ _ _ _ hb)
        (by simpa only [pushed,Array.size_push] using hh)
      apply (emit_mem _ _ _ _).mpr
      exact Or.inl (visit_events_mono _ _ _ _ _ he)
    | right hh =>
      let next:=some (Parent.mk depth (select parent depth s.nodes.size))
      let pushed : Store h:=⟨s.nodes.push ⟨depth,select parent depth s.nodes.size,none,State.empty h⟩,
        s.events,s.work+12⟩
      let left:=visit cap a next pushed
      have he:=ib next left.2 (positions_right _ _ _ _ hb) (by
        simpa only [left,visit_size,pushed,Array.size_push] using hh)
      apply (emit_mem _ _ _ _).mpr
      exact Or.inl he

end REWB.MaskedOrdered.Owner
