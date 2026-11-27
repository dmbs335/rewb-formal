import REWB.MaskedOrderedOwnerQualified

/-! Every emitted event records an actual visited split's propagated
owner. Resolving that owner in the final array yields a complete locus
and the exact saved occurrence set. -/
namespace REWB.MaskedOrdered.Owner
open REWB.MaskedRunDiscovery (positions Complete prepareSuffixes suffixKeys)
variable {h n σ : Nat}

def Origin (t : Trie n Nat) (parent : Option Parent) (base : Nat) (e : Event) : Prop :=
  ∃u pu id,Location t parent base u pu id ∧ e.owner=select pu u.depth id

theorem visit_event_origin (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (e : Event) (he : e∈(visit cap t parent s).2.events.toList) :
    e∈s.events.toList ∨ Origin t parent s.nodes.size e := by
  induction t generalizing parent s with
  | empty => exact Or.inl he
  | leaf a => exact Or.inl he
  | node stem d l r il ir =>
    let next:=some (Parent.mk d (select parent d s.nodes.size))
    let pushed : Store h:=⟨s.nodes.push ⟨d,select parent d s.nodes.size,none,State.empty h⟩,
      s.events,s.work+12⟩
    let a:=visit cap l next pushed
    let b:=visit cap r next a.2
    let step:=merge cap a.1 b.1 {}
    have hh : e∈(emit (select parent d s.nodes.size) step.2.fresh b.2.events).1.toList:=he
    rcases (emit_mem _ _ _ _).mp hh with hh|⟨edge,_,hh⟩
    · rcases ir next a.2 hh with hh|hh
      · rcases il next pushed hh with hh|hh
        · exact Or.inl hh
        · obtain ⟨u,pu,id,hl,ho⟩:=hh
          have hl' : Location l next (s.nodes.size+1) u pu id := by
            simpa only [pushed,Array.size_push] using hl
          exact Or.inr ⟨u,pu,id,.left hl',ho⟩
      · obtain ⟨u,pu,id,hl,ho⟩:=hh
        have hl' : Location r next (s.nodes.size+1+slots l) u pu id := by
          simpa only [a,visit_size,pushed,Array.size_push] using hl
        exact Or.inr ⟨u,pu,id,.right hl',ho⟩
    · subst e
      exact Or.inr ⟨.node stem d l r,parent,s.nodes.size,.here _ _ _,rfl⟩

theorem visit_event_owner (f : Nat→Fin σ) (cap : Nat) (t : Trie n Nat) (s : Store h)
    (hc : cap=2^h) (hb : PositionsBounded h t) (hg : t.Good f) (e : Event)
    (he : e∈(visit cap t none s).2.events.toList) (hnew : e∉s.events.toList) :
    ∃v pv rec,(visit cap t none s).2.nodes[e.owner]?=some rec ∧
      Snapshot v pv e.owner rec ∧ BoundaryTrie.Tree.Locus t rec.depth v ∧ rec.owner=e.owner := by
  have ho:=(visit_event_origin cap t none s e he).resolve_left hnew
  obtain ⟨u,pu,id,hl,hoe⟩:=ho
  obtain ⟨v,pv,hlv,hd,hself,hclass⟩:=location_owner f hg hl
  rw [←hoe] at hlv hself
  obtain ⟨rec,hget,hs⟩:=visit_at cap t none s hc hb v pv e.owner hlv
  refine ⟨v,pv,rec,hget,hs,?_,?_⟩
  · rw [hs.1,hd]
    exact hclass
  · exact hs.2.1.trans hself

theorem locus_nonempty (f : Nat→Fin σ) {t u : Trie n Nat} {H : Nat}
    (hl : BoundaryTrie.Tree.Locus t H u) (hg : t.Good f) (hn : t.leaves≠[]) : u.leaves≠[] := by
  induction hl with
  | here => exact hn
  | left _ _ ih => exact ih hg.1 hg.2.2.1
  | right _ _ ih => exact ih hg.2.1 hg.2.2.2.1

theorem suffix_event_certified (text : Array (Fin σ)) (fallback : Fin σ) (h cap work : Nat)
    (hc : cap=2^h) (hb : PositionsBounded h (prepareSuffixes text fallback).trie.tree)
    (e : Event)
    (he : e∈(visit cap (prepareSuffixes text fallback).trie.tree none
      ({work:=work} : Store h)).2.events.toList) :
    ∀rec,(visit cap (prepareSuffixes text fallback).trie.tree none
      ({work:=work} : Store h)).2.nodes[e.owner]?=some rec →
      rec.state.Valid ∧ ∃base,Complete (ArrayText.read text fallback) text.size base
        rec.depth rec.state.tree.entries := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have hg : t.Good (ArrayText.read text fallback):=
    (BoundaryTrie.Build.run_correct text fallback (suffixKeys text.size)).2.1
  obtain ⟨v,pv,rr,hget,hs,hl,_⟩:=visit_event_owner (ArrayText.read text fallback) cap t {work:=work}
    hc hb hg e he (by simp)
  intro rec hr
  have hEq : rr=rec:=Option.some.inj (hget.symm.trans hr)
  subst rr
  have hn : t.leaves≠[] := by
    intro hh
    have hp:=(MaskedRunTrieBridge.suffix_positions text fallback).length_eq
    change (positions t).length=(List.range (text.size+1)).length at hp
    simp only [positions,hh,List.map_nil,List.length_nil,List.length_range] at hp
    omega
  obtain ⟨a,ha⟩:=List.exists_mem_of_ne_nil v.leaves (locus_nonempty _ hl hg hn)
  have hfull:=MaskedRunDiscovery.prepareSuffixes_complete text fallback v rec.depth a hl ha
  refine ⟨hs.2.2.2.1,a.start,?_⟩
  intro p
  exact (hs.2.2.2.2 p).trans (hfull p)

end REWB.MaskedOrdered.Owner
