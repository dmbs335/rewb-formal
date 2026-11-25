import REWB.MaskedTraversalDriverCorrect

/-! Every band emitted by the actual driver is a complete suffix class
at every length that it contains.  In particular, partial equal-depth
binary refinements cannot supply a band or a primitive-square reset.
This is semantic completeness of the retained geometric query plans;
it does not assert that a masked answer callback has been implemented. -/
namespace REWB.MaskedTraversalDriver
open REWB.MaskedTraversalFrontier REWB.BoundaryTrie
open REWB.MaskedRunDiscovery
variable {h n σ : Nat}

def Plan.HasBand (b : MaskedTraversalEdge.Band h) : Plan h→Prop
  | .empty step => b∈step.lowered.edge.path.bands
  | .leaf _ _ step => b∈step.lowered.edge.path.bands
  | .node left right _ step => b∈step.lowered.edge.path.bands ∨ left.HasBand b ∨ right.HasBand b

theorem lower_band (capacity floor high : Nat) (s : Frontier h)
    (hv : s.Valid high) (hc : capacity=2^h) (b : MaskedTraversalEdge.Band h)
    (hb : b∈(lower capacity floor high s).edge.path.bands) :
    floor<b.lo ∧ b.lo≤b.hi ∧ b.hi≤high ∧ b.Valid capacity s.state.occurrences := by
  have hh : floor<high := by
    by_cases hh : floor<high
    · exact hh
    · simp only [lower,MaskedTraversalEdge.run,if_neg hh,List.not_mem_nil] at hb
  have hs:=MaskedTraversalEdge.run_valid capacity floor high s.state hh hv.invariant hv.future hc
  have hb':=hs.chain.bounds hb
  exact ⟨hb'.1,hb'.2.1,hb'.2.2,hs.bands b hb⟩

theorem lower_cover (capacity floor high L : Nat) (s : Frontier h)
    (hv : s.Valid high) (hc : capacity=2^h) (hl : floor<L) (hh : L≤high) :
    ∃b,b∈(lower capacity floor high s).edge.path.bands ∧ b.lo≤L ∧ L≤b.hi ∧
      b.snapshot.occurrences=s.state.occurrences := by
  have hs:=MaskedTraversalEdge.run_valid capacity floor high s.state (by omega)
    hv.invariant hv.future hc
  obtain ⟨b,hb,hlo,hhi⟩:=hs.chain.coverage.mpr ⟨hl,hh⟩
  exact ⟨b,hb,hlo,hhi,(hs.bands b hb).occurrences⟩

theorem build_cover (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth)
    (a : Key n Nat) (ha : a∈t.leaves) (L : Nat) (hl : floor<L) (hh : L≤a.length) :
    ∃b,(build (h:=h) capacity floor t).plan.HasBand b ∧ b.lo≤L ∧ L≤b.hi ∧
      a.start∈b.snapshot.occurrences.entries := by
  induction t generalizing floor with
  | empty => simp only [Tree.leaves,List.not_mem_nil] at ha
  | leaf x =>
    have he : a=x := by simpa only [Tree.leaves,List.mem_singleton] using ha
    subst x
    have hp : a.start<capacity := by have hb:=a.bounded; omega
    let leaf:=insert capacity a.length a.start (empty h)
    have hv:=insert_valid capacity a.length a.start (empty h) (empty_valid h _) hc hp
    obtain ⟨b,hb,hlo,hhi,hocc⟩:=lower_cover capacity floor a.length L leaf.frontier hv hc hl hh
    refine ⟨b,hb,hlo,hhi,?_⟩
    rw [hocc]
    exact (insert_mem capacity a.length a.start a.start (empty h) (empty_valid h _) hc hp).mpr (Or.inl rfl)
  | node stem depth left right il ir =>
    have hd:=Tree.edge_depths f stem depth left right hg
    let x:=build (h:=h) capacity depth left
    let y:=build (h:=h) capacity depth right
    let merged:=merge capacity depth x.frontier y.frontier
    have hx:=build_valid capacity depth f left hg.1 hc hn hd.1
    have hy:=build_valid capacity depth f right hg.2.1 hc hn hd.2
    by_cases hlocal : L≤depth
    · have hv:=merge_valid capacity depth x.frontier y.frontier hx hy hc
      obtain ⟨b,hb,hlo,hhi,hocc⟩:=lower_cover capacity floor depth L merged.frontier hv hc hl hlocal
      refine ⟨b,Or.inl hb,hlo,hhi,?_⟩
      rw [hocc]
      apply (merge_mem capacity depth x.frontier y.frontier hx hy hc a.start).mpr
      rcases List.mem_append.mp ha with hal|har
      · exact Or.inl ((build_mem capacity depth f left hg.1 hc hn hd.1 a.start).mpr
          (List.mem_map.mpr ⟨a,hal,rfl⟩))
      · exact Or.inr ((build_mem capacity depth f right hg.2.1 hc hn hd.2 a.start).mpr
          (List.mem_map.mpr ⟨a,har,rfl⟩))
    · rcases List.mem_append.mp ha with hal|har
      · obtain ⟨b,hb,hlo,hhi,hmem⟩:=il depth hg.1 hd.1 hal (by omega)
        exact ⟨b,Or.inr (Or.inl hb),hlo,hhi,hmem⟩
      · obtain ⟨b,hb,hlo,hhi,hmem⟩:=ir depth hg.2.1 hd.2 har (by omega)
        exact ⟨b,Or.inr (Or.inr hb),hlo,hhi,hmem⟩

theorem build_band_locus (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth)
    (b : MaskedTraversalEdge.Band h) (hb : (build capacity floor t).plan.HasBand b) :
    floor<b.lo ∧ b.Valid capacity b.snapshot.occurrences ∧
    ∀L,b.lo≤L → L≤b.hi → ∃u,Tree.Locus t L u ∧
      ∀x,x∈b.snapshot.occurrences.entries ↔ x∈positions u := by
  induction t generalizing floor with
  | empty =>
    have hv:=empty_valid h 0
    have hs:=lower_band capacity floor 0 (empty h) hv hc b hb
    omega
  | leaf a =>
    have hp : a.start<capacity := by have hh:=a.bounded; omega
    let leaf:=insert capacity a.length a.start (empty h)
    have hv:=insert_valid capacity a.length a.start (empty h) (empty_valid h _) hc hp
    have hs:=lower_band capacity floor a.length leaf.frontier hv hc b hb
    refine ⟨hs.1,⟨hs.2.1,rfl,hs.2.2.2.invariant,hs.2.2.2.future,hs.2.2.2.clean,hs.2.2.2.crossing⟩,?_⟩
    intro L hL hH
    refine ⟨.leaf a,.here _ (by change L≤a.length; omega),?_⟩
    intro x
    rw [hs.2.2.2.occurrences]
    change x∈(insert capacity a.length a.start (empty h)).frontier.state.occurrences.entries ↔ _
    rw [insert_mem capacity a.length a.start x (empty h) (empty_valid h _) hc hp]
    simp [empty,MaskedClusterLeaders.empty,MaskedOrdered.Tree.entries,positions,Tree.leaves]
  | node stem depth left right il ir =>
    have hd:=Tree.edge_depths f stem depth left right hg
    let a:=build (h:=h) capacity depth left
    let c:=build (h:=h) capacity depth right
    let merged:=merge capacity depth a.frontier c.frontier
    have hva:=build_valid capacity depth f left hg.1 hc hn hd.1
    have hvc:=build_valid capacity depth f right hg.2.1 hc hn hd.2
    have hvm:=merge_valid capacity depth a.frontier c.frontier hva hvc hc
    change b∈(lower capacity floor depth merged.frontier).edge.path.bands ∨
      a.plan.HasBand b ∨ c.plan.HasBand b at hb
    rcases hb with hb|hb|hb
    · have hs:=lower_band capacity floor depth merged.frontier hvm hc b hb
      refine ⟨hs.1,⟨hs.2.1,rfl,hs.2.2.2.invariant,hs.2.2.2.future,hs.2.2.2.clean,hs.2.2.2.crossing⟩,?_⟩
      intro L hL hH
      refine ⟨.node stem depth left right,.here _ (by change L≤depth; omega),?_⟩
      intro x
      rw [hs.2.2.2.occurrences]
      change x∈(merge capacity depth a.frontier c.frontier).frontier.state.occurrences.entries ↔ _
      rw [merge_mem capacity depth a.frontier c.frontier hva hvc hc x,
        build_mem capacity depth f left hg.1 hc hn hd.1 x,
        build_mem capacity depth f right hg.2.1 hc hn hd.2 x]
      simp only [positions,Tree.leaves,List.map_append,List.mem_append]
    · have hs:=il depth hg.1 hd.1 hb
      refine ⟨by change floor≤depth at hf; omega,hs.2.1,?_⟩
      intro L hL hH
      obtain ⟨u,hu,hm⟩:=hs.2.2 L hL hH
      exact ⟨u,.left (by omega) hu,hm⟩
    · have hs:=ir depth hg.2.1 hd.2 hb
      refine ⟨by change floor≤depth at hf; omega,hs.2.1,?_⟩
      intro L hL hH
      obtain ⟨u,hu,hm⟩:=hs.2.2 L hL hH
      exact ⟨u,.right (by omega) hu,hm⟩

theorem suffix_band_complete (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) (b : MaskedTraversalEdge.Band h)
    (hb : (run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b)
    (L base : Nat) (hL : b.lo≤L) (hH : L≤b.hi) (hbase : base∈b.snapshot.occurrences.entries) :
    Complete (ArrayText.read text fallback) text.size base L b.snapshot.occurrences.entries := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have hg : t.Good (ArrayText.read text fallback) :=
    (Build.run_correct text fallback (suffixKeys text.size)).2.1
  have hs:=build_band_locus (MaskedOrdered.capacity h).1 0 _ t hg
    (MaskedOrdered.capacity_value h) hn (Nat.zero_le _) b hb
  obtain ⟨u,hu,hm⟩:=hs.2.2 L hL hH
  obtain ⟨a,ha,he⟩:=List.mem_map.mp ((hm base).mp hbase)
  have hf:=prepareSuffixes_complete text fallback u L a hu ha
  intro x
  have heq:= (hm x).trans (hf x)
  simpa only [he] using heq

/-- Every real nonempty copy length occurs in an emitted band containing
its actual start.  Length zero is intentionally outside these edge plans. -/
theorem suffix_cover (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) (p : Fin (text.size+1)) (L : Nat) (hl : 0<L) (hh : L≤text.size-p.val) :
    ∃b,(run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b ∧
      b.lo≤L ∧ L≤b.hi ∧ p.val∈b.snapshot.occurrences.entries := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have hs:=Build.run_correct text fallback (suffixKeys text.size)
  have hg : t.Good (ArrayText.read text fallback) := hs.2.1
  have ha : suffixKey text.size p∈t.leaves := hs.1.mem_iff.mpr (suffixKey_mem text.size p)
  exact build_cover (MaskedOrdered.capacity h).1 0 _ t hg (MaskedOrdered.capacity_value h)
    hn (Nat.zero_le _) (suffixKey text.size p) ha L hl hh

/-- Actual partial refinements perform neither a band query nor an
initial due-record drain.  Their dirty-bank work must wait for the first
strict edge, whose complete-class theorem is above. -/
theorem equal_depth_edge (capacity length : Nat) (s : Frontier h) :
    (lower capacity length length s).edge.initial=none ∧
      (lower capacity length length s).edge.path.bands=[] := by
  simp only [lower,MaskedTraversalEdge.run_equal]
  trivial

end REWB.MaskedTraversalDriver
