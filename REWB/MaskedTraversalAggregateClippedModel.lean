import REWB.MaskedTraversalAggregateClipReady

/-! Exact indexed model of the two temporary boundary replacements.
The selected values are the actual compiler outputs. This proof-only
list is never traversed by the runtime clipping or query implementation.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h : Nat}

theorem clipEntries_get (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (keys : List Nat) (old lo hi : Nat) (entries : List (Option (Mutable.Store.Entry C E))) (first : Nat) :
    (clipEntries env st keys old lo hi entries)[first]?=
      if first∈keys then (if first<entries.length then some (clippedEntry env st first old lo hi) else none)
      else entries[first]? := by
  induction keys generalizing entries with
  | nil=>simp only [clipEntries,List.foldl_nil,List.not_mem_nil,if_false]
  | cons p ps ih=>
    change (clipEntries env st ps old lo hi (entries.set p (clippedEntry env st p old lo hi)))[first]?=_
    rw [ih]
    simp only [List.length_set,List.mem_cons]
    by_cases hp : first∈ps
    · simp only [hp,if_true,or_true]
    · simp only [hp,if_false,or_false]
      by_cases he : p=first
      · subst p
        simp only [if_pos rfl,List.getElem?_set,if_true]
      · simp only [List.getElem?_set_ne he,Ne.symm he,if_false]

theorem clipEntries_current (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (keys : List Nat) (hk : ∀p,p∈keys→p∈partition.leaders.entries) :
    CurrentEntries env st partition capacity old (clipEntries env st keys old lo hi entries) := by
  intro first entry he
  rw [clipEntries_get] at he
  by_cases hp : first∈keys
  · obtain ⟨before,hbefore⟩:=complete first (hk first hp)
    have hb:=(List.getElem?_eq_some_iff.mp hbefore).1
    simp only [hp,if_true,hb,Option.some.injEq] at he
    obtain ⟨next,hn,_,hcurrent⟩:=clippedEntry_present env st partition capacity old first lo hi before
      (coherent first before hbefore)
    have heq : next=entry := Option.some.inj (hn.symm.trans he)
    subst entry
    exact hcurrent
  · simp only [hp,if_false] at he
    exact coherent.current first entry he

theorem clipEntries_linked (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat) (anchors : Array (Option Nat))
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (keys : List Nat) (hk : ∀p,p∈keys→p∈partition.leaders.entries) :
    LinkedEntries env st partition capacity old anchors (clipEntries env st keys old lo hi entries) := by
  intro first entry he
  rw [clipEntries_get] at he
  by_cases hp : first∈keys
  · obtain ⟨before,hbefore⟩:=complete first (hk first hp)
    have hb:=(List.getElem?_eq_some_iff.mp hbefore).1
    simp only [hp,if_true,hb,Option.some.injEq] at he
    obtain ⟨next,hn,hcfg,_⟩:=clippedEntry_present env st partition capacity old first lo hi before
      (coherent first before hbefore)
    have heq : next=entry := Option.some.inj (hn.symm.trans he)
    subst entry
    rw [hcfg]
    exact Linked.clipped env st partition capacity old first lo hi anchors before.config (linked first before hbefore)
  · simp only [hp,if_false] at he
    exact linked first entry he

theorem clipEntries_complete (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (keys : List Nat) : CompleteModel partition (clipEntries env st keys old lo hi entries) := by
  intro first hleader
  obtain ⟨before,hbefore⟩:=complete first hleader
  have hb:=(List.getElem?_eq_some_iff.mp hbefore).1
  by_cases hp : first∈keys
  · obtain ⟨next,hn,_,_⟩:=clippedEntry_present env st partition capacity old first lo hi before
      (coherent first before hbefore)
    exact ⟨next,by simp only [clipEntries_get,hp,if_true,hb,hn]⟩
  · exact ⟨before,by simpa only [clipEntries_get,hp,if_false] using hbefore⟩

theorem clipEntries_config (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (keys : List Nat) (hk : ∀p,p∈keys→p∈partition.leaders.entries)
    (first : Nat) (entry : Mutable.Store.Entry C E)
    (he : (clipEntries env st keys old lo hi entries)[first]?=some (some entry)) :
    ∃before,entries[first]?=some (some before) ∧
      entry.config=if first∈keys then Clip.config before.config old lo hi else before.config := by
  rw [clipEntries_get] at he
  by_cases hp : first∈keys
  · obtain ⟨before,hbefore⟩:=complete first (hk first hp)
    have hb:=(List.getElem?_eq_some_iff.mp hbefore).1
    simp only [hp,if_true,hb,Option.some.injEq] at he
    obtain ⟨next,hn,hcfg,_⟩:=clippedEntry_present env st partition capacity old first lo hi before
      (coherent first before hbefore)
    have heq : next=entry := Option.some.inj (hn.symm.trans he)
    subst entry
    exact ⟨before,hbefore,by simpa only [hp,if_true] using hcfg⟩
  · simp only [hp,if_false] at he
    exact ⟨entry,he,by simp only [hp,if_false]⟩

end REWB.MaskedTraversalAggregate.Cells
