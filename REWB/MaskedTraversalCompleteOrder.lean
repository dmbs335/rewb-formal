import REWB.MaskedTraversalAggregateRegionModel

/-! The chronological bank list is the proof model of actual indexed
slots. Its descriptor keys equal the maintained ordered leader tree;
there is no supplied sort, cluster list, or neighbor oracle. -/
namespace REWB.MaskedTraversalComplete
open REWB.MaskedCluster REWB.MaskedTraversalAggregate REWB.MaskedTraversalAggregate.Cells
variable {α : Type} {C E : DFA α} {h : Nat}

def firsts (parts : List Part) : List Nat := parts.map fun p=>p.config.descriptor.first

def entryKeys (entries : List (Option (Mutable.Store.Entry C E))) : List Nat :=
  entries.filterMap fun entry=>entry.map fun entry=>entry.config.descriptor.first

theorem parts_firsts (gate : Bool) (entries : List (Option (Mutable.Store.Entry C E))) :
    firsts (parts gate entries)=entryKeys entries := by
  induction entries with
  | nil=>rfl
  | cons value rest ih=>
    cases value with
    | none=>exact ih
    | some entry=>exact congrArg (List.cons entry.config.descriptor.first) ih

theorem regionParts_keys (entries : List (Option (Mutable.Store.Entry C E))) (lo hi : Nat) (hh : lo≤hi) :
    firsts (regionParts entries lo hi)=entryKeys entries := by
  have hs : entries.take lo++Spec.slice entries lo hi++entries.drop hi=entries := by
    have hx:=List.take_append_drop (hi-lo) (entries.drop lo)
    rw [List.drop_drop,show lo+(hi-lo)=hi by omega] at hx
    dsimp only [Spec.slice]
    rw [List.append_assoc,hx,List.take_append_drop]
  simp only [firsts,regionParts,List.map_append]
  change (firsts (parts false (entries.take lo))++firsts (parts true (Spec.slice entries lo hi)))++
    firsts (parts false (entries.drop hi))=_
  rw [parts_firsts,parts_firsts,parts_firsts]
  simp only [entryKeys,←List.filterMap_append,hs]

theorem entryKeys_mem (entries : List (Option (Mutable.Store.Entry C E))) (x : Nat) :
    x∈entryKeys entries ↔ ∃(i : Nat) (entry : Mutable.Store.Entry C E),entries[i]?=some (some entry) ∧ x=entry.config.descriptor.first := by
  constructor
  · intro hx
    obtain ⟨value,hvalue,hx⟩:=List.mem_filterMap.mp hx
    cases value with
    | none=>cases hx
    | some entry=>
      obtain ⟨i,hi⟩:=List.getElem?_of_mem hvalue
      exact ⟨i,entry,hi,(Option.some.inj hx).symm⟩
  · rintro ⟨i,entry,he,rfl⟩
    exact List.mem_filterMap.mpr ⟨some entry,List.mem_of_getElem? he,rfl⟩

theorem entryKeys_ordered (entries : List (Option (Mutable.Store.Entry C E))) (offset : Nat)
    (indexed : ∀(i : Nat) (entry : Mutable.Store.Entry C E),entries[i]?=some (some entry)→entry.config.descriptor.first=offset+i) :
    (entryKeys entries).Pairwise (·<·) := by
  induction entries generalizing offset with
  | nil=>exact List.Pairwise.nil
  | cons value rest ih=>
    have tail : ∀(i : Nat) (entry : Mutable.Store.Entry C E),rest[i]?=some (some entry)→entry.config.descriptor.first=(offset+1)+i := by
      intro i entry he
      have hh:=indexed (i+1) entry (by simpa only [List.getElem?_cons_succ] using he)
      omega
    have hr:=ih (offset+1) tail
    cases value with
    | none=>exact hr
    | some entry=>
      apply List.pairwise_cons.mpr
      refine ⟨?_,hr⟩
      intro x hx
      obtain ⟨i,e,he,hx⟩:=(entryKeys_mem rest x).mp hx
      have ha:=indexed 0 entry rfl
      have hb:=tail i e he
      change entry.config.descriptor.first<x
      omega

theorem regionParts_firsts (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (current : CurrentEntries env st partition capacity old entries) (complete : CompleteModel partition entries)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h) (hh : lo≤hi) :
    firsts (regionParts entries lo hi)=partition.leaders.entries := by
  rw [regionParts_keys entries lo hi hh]
  have hs : ∀(i : Nat) (entry : Mutable.Store.Entry C E),entries[i]?=some (some entry)→entry.config.descriptor.first=i := by
    intro i entry he
    exact (MaskedClusterDescriptor.describeLeader_sound partition capacity old i hv hc entry.config.descriptor
      (current i entry he).descriptor).1
  apply MaskedOrdered.strict_ext _ _
    (entryKeys_ordered entries 0 (by simpa only [Nat.zero_add] using hs))
    (MaskedOrdered.Tree.ordered partition.leaders 0 hv.leadFits)
  intro x
  rw [entryKeys_mem]
  constructor
  · rintro ⟨i,entry,he,rfl⟩
    exact (MaskedClusterDescriptor.describeLeader_sound partition capacity old i hv hc entry.config.descriptor
      (current i entry he).descriptor).2.firstLeader
  · intro hx
    obtain ⟨entry,he⟩:=complete x hx
    exact ⟨x,entry,he,(hs x entry he).symm⟩

theorem adjacent_specs (a b : Nat) (before after : List Nat)
    (hs : (before++a::b::after).Pairwise (·<·)) :
    MaskedOrdered.Tree.SuccSpec (before++a::b::after) a (some b) ∧
      MaskedOrdered.Tree.PredSpec (before++a::b::after) b (some a) := by
  obtain ⟨_,hrest,hcross⟩:=List.pairwise_append.mp hs
  obtain ⟨ha,hrest⟩:=List.pairwise_cons.mp hrest
  obtain ⟨hb,_⟩:=List.pairwise_cons.mp hrest
  have hab:=ha b List.mem_cons_self
  constructor
  · refine ⟨List.mem_append_right before (List.mem_cons_of_mem a List.mem_cons_self),hab,?_⟩
    intro x hx hax
    rcases List.mem_append.mp hx with hx|hx
    · have hh:=hcross x hx a List.mem_cons_self
      omega
    · rcases List.mem_cons.mp hx with he|hx
      · omega
      · rcases List.mem_cons.mp hx with he|hx
        · omega
        · exact Nat.le_of_lt (hb x hx)
  · refine ⟨List.mem_append_right before List.mem_cons_self,hab,?_⟩
    intro x hx hxb
    rcases List.mem_append.mp hx with hx|hx
    · exact Nat.le_of_lt (hcross x hx a List.mem_cons_self)
    · rcases List.mem_cons.mp hx with he|hx
      · omega
      · rcases List.mem_cons.mp hx with he|hx
        · omega
        · have hh:=hb x hx; omega

theorem last_spec (a : Nat) (before : List Nat) (hs : (before++[a]).Pairwise (·<·)) :
    MaskedOrdered.Tree.SuccSpec (before++[a]) a none := by
  have hcross:=(List.pairwise_append.mp hs).2.2
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact Nat.le_of_lt (hcross x hx a List.mem_cons_self)
  · have hh:=List.mem_singleton.mp hx; omega

end REWB.MaskedTraversalComplete
