import REWB.MaskedTraversalDriver

namespace REWB.MaskedTraversalDriver
open REWB.MaskedTraversalFrontier REWB.BoundaryTrie
open REWB.MaskedRunDiscovery (positions)
variable {h n σ : Nat}

theorem build_valid (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth) :
    (build (h:=h) capacity floor t).frontier.Valid floor := by
  induction t generalizing floor with
  | empty =>
    exact finish_valid _ _ _ _ _ _ (empty_valid h 0) hc hf
  | leaf a =>
    have hp : a.start<capacity := by have hb:=a.bounded; omega
    exact finish_valid _ _ _ _ _ _
      (insert_valid capacity a.length a.start (empty h) (empty_valid h _) hc hp) hc hf
  | node stem depth left right il ir =>
    have hd:=Tree.edge_depths f stem depth left right hg
    have hl:=il depth hg.1 hd.1
    have hr:=ir depth hg.2.1 hd.2
    exact finish_valid _ _ _ _ _ _
      (merge_valid capacity depth _ _ hl hr hc) hc hf

theorem build_mem (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth) (x : Nat) :
    x∈(build (h:=h) capacity floor t).frontier.state.occurrences.entries ↔ x∈positions t := by
  induction t generalizing floor with
  | empty =>
    simp only [build,finish_occurrences]
    rfl
  | leaf a =>
    have hp : a.start<capacity := by have hb:=a.bounded; omega
    simp only [build,finish_occurrences]
    rw [insert_mem capacity a.length a.start x (empty h) (empty_valid h _) hc hp]
    simp [empty,MaskedClusterLeaders.empty,MaskedOrdered.Tree.entries,positions,Tree.leaves]
  | node stem depth left right il ir =>
    have hd:=Tree.edge_depths f stem depth left right hg
    have hl:=build_valid capacity depth f left hg.1 hc hn hd.1
    have hr:=build_valid capacity depth f right hg.2.1 hc hn hd.2
    simp only [build,finish_occurrences]
    rw [merge_mem capacity depth _ _ hl hr hc x,il depth hg.1 hd.1,ir depth hg.2.1 hd.2]
    simp only [positions,Tree.leaves,List.map_append,List.mem_append]

theorem build_perm (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth)
    (hd : (positions t).Nodup) :
    (build (h:=h) capacity floor t).frontier.state.occurrences.entries.Perm (positions t) := by
  have hv:=build_valid capacity floor f t hg hc hn hf
  exact MaskedOrdered.nodup_perm _ _ (MaskedOrdered.Tree.nodup _ 0 hv.invariant.occFits) hd
    (build_mem capacity floor f t hg hc hn hf)

theorem build_count (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth)
    (hd : (positions t).Nodup) :
    (build (h:=h) capacity floor t).frontier.state.occurrences.count=t.leaves.length := by
  have hv:=build_valid capacity floor f t hg hc hn hf
  rw [MaskedOrdered.Tree.count_correct _ hv.invariant.occGood,
    (build_perm capacity floor f t hg hc hn hf hd).length_eq]
  simp only [positions,List.length_map]

/-- The child endpoints are already at the parent length before the
executable merge is invoked, including all child events at that endpoint. -/
theorem node_children_at_parent (capacity : Nat) (f : Nat→Fin σ)
    (stem : Key n Nat) (depth : Nat) (left right : Tree n Nat)
    (hg : (Tree.node stem depth left right).Good f) (hc : capacity=2^h) (hn : n<2^h) :
    (build (h:=h) capacity depth left).frontier.Valid depth ∧
    (build (h:=h) capacity depth right).frontier.Valid depth := by
  have hd:=Tree.edge_depths f stem depth left right hg
  exact ⟨build_valid capacity depth f left hg.1 hc hn hd.1,
    build_valid capacity depth f right hg.2.1 hc hn hd.2⟩

theorem run_valid (h : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hn : n<2^h) : (run h t).frontier.Valid 0 :=
  build_valid (MaskedOrdered.capacity h).1 0 f t hg (MaskedOrdered.capacity_value h) hn (Nat.zero_le _)

theorem run_mem (h : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hn : n<2^h) (x : Nat) :
    x∈(run h t).frontier.state.occurrences.entries ↔ x∈positions t :=
  build_mem (MaskedOrdered.capacity h).1 0 f t hg (MaskedOrdered.capacity_value h) hn (Nat.zero_le _) x

end REWB.MaskedTraversalDriver
