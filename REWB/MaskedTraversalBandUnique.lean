import REWB.MaskedTraversalDriverCoverage
import REWB.MaskedLocalAnchor
import REWB.RunBudget

/-! A source and a positive length occur in at most one emitted band.
The flattened list below is a proof view of the retained tree plan; no
production operation builds it. Pairwise disjointness also proves that
locally distinct density charges stay distinct over the whole execution,
once each charge is attributed to its actual source/length band. -/
namespace REWB.MaskedTraversalDriver
open REWB.MaskedTraversalFrontier REWB.BoundaryTrie
open REWB.MaskedRunDiscovery
variable {h n σ : Nat}

def BandCovers (b : MaskedTraversalEdge.Band h) (source length : Nat) : Prop :=
  b.lo≤length ∧ length≤b.hi ∧ source∈b.snapshot.occurrences.entries

def DisjointBands (a b : MaskedTraversalEdge.Band h) : Prop :=
  ∀source length,BandCovers a source length→BandCovers b source length→False

def Plan.bandView : Plan h→List (MaskedTraversalEdge.Band h)
  | .empty step => step.lowered.edge.path.bands
  | .leaf _ _ step => step.lowered.edge.path.bands
  | .node left right _ step => left.bandView++right.bandView++step.lowered.edge.path.bands

theorem mem_bandView (b : MaskedTraversalEdge.Band h) (p : Plan h) :
    b∈p.bandView ↔ p.HasBand b := by
  induction p <;> simp_all only [Plan.bandView,Plan.HasBand,List.mem_append,or_assoc,or_comm,or_left_comm]

theorem chain_disjoint {floor high : Nat} {bs : List (MaskedTraversalEdge.Band h)}
    (hc : MaskedTraversalEdge.Chain floor high bs) : bs.Pairwise DisjointBands := by
  induction hc with
  | nil => exact List.Pairwise.nil
  | @cons cut high b bs hhi hlo hl hh tail ih =>
    apply List.Pairwise.cons
    · intro a ha source length hb ha'
      have hbound:=tail.bounds ha
      have hlow:=hb.1
      have hhigh:=ha'.2.1
      omega
    · exact ih

theorem lower_disjoint (capacity floor high : Nat) (s : Frontier h)
    (hv : s.Valid high) (hc : capacity=2^h) :
    (lower capacity floor high s).edge.path.bands.Pairwise DisjointBands := by
  by_cases hh : floor<high
  · exact chain_disjoint (MaskedTraversalEdge.run_valid capacity floor high s.state hh hv.invariant hv.future hc).chain
  · simp only [lower,MaskedTraversalEdge.run,if_neg hh]
    exact List.Pairwise.nil

theorem band_position (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth)
    (b : MaskedTraversalEdge.Band h) (hb : (build capacity floor t).plan.HasBand b)
    (source length : Nat) (hit : BandCovers b source length) :
    source∈positions t ∧ floor<length := by
  have hs:=build_band_locus capacity floor f t hg hc hn hf b hb
  obtain ⟨u,hu,hm⟩:=hs.2.2 length hit.1 hit.2.1
  obtain ⟨a,ha,he⟩:=List.mem_map.mp ((hm source).mp hit.2.2)
  exact ⟨List.mem_map.mpr ⟨a,Tree.locus_mem hu a ha,he⟩,by have hh:=hs.1; have hl:=hit.1; omega⟩

theorem build_disjoint (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth)
    (hdistinct : (positions t).Nodup) :
    (build (h:=h) capacity floor t).plan.bandView.Pairwise DisjointBands := by
  induction t generalizing floor with
  | empty => exact lower_disjoint capacity floor 0 (empty h) (empty_valid h 0) hc
  | leaf a =>
    have hp : a.start<capacity := by have hh:=a.bounded; omega
    exact lower_disjoint capacity floor a.length _
      (insert_valid capacity a.length a.start (empty h) (empty_valid h _) hc hp) hc
  | node stem depth left right il ir =>
    have hd:=Tree.edge_depths f stem depth left right hg
    have hnds : (positions left++positions right).Nodup := by
      simpa only [positions,Tree.leaves,List.map_append] using hdistinct
    have hparts:=List.pairwise_append.mp hnds
    let x:=build (h:=h) capacity depth left
    let y:=build (h:=h) capacity depth right
    let merged:=merge capacity depth x.frontier y.frontier
    have hx:=build_valid capacity depth f left hg.1 hc hn hd.1
    have hy:=build_valid capacity depth f right hg.2.1 hc hn hd.2
    have hm:=merge_valid capacity depth x.frontier y.frontier hx hy hc
    have hl:=il depth hg.1 hd.1 hparts.1
    have hr:=ir depth hg.2.1 hd.2 hparts.2.1
    change (x.plan.bandView++y.plan.bandView++(lower capacity floor depth merged.frontier).edge.path.bands).Pairwise DisjointBands
    apply List.pairwise_append.mpr
    refine ⟨?_,lower_disjoint capacity floor depth merged.frontier hm hc,?_⟩
    · apply List.pairwise_append.mpr
      refine ⟨hl,hr,?_⟩
      intro a ha b hb source length hita hitb
      have hpa:=(band_position capacity depth f left hg.1 hc hn hd.1 a
        ((mem_bandView a x.plan).mp ha) source length hita).1
      have hpb:=(band_position capacity depth f right hg.2.1 hc hn hd.2 b
        ((mem_bandView b y.plan).mp hb) source length hitb).1
      exact hparts.2.2 source hpa source hpb rfl
    · intro a ha b hb source length hita hitb
      have hs:=lower_band capacity floor depth merged.frontier hm hc b hb
      have hh:=hitb.2.1
      have hbnd:=hs.2.2.1
      rcases List.mem_append.mp ha with ha|ha
      · have hL:=(band_position capacity depth f left hg.1 hc hn hd.1 a
          ((mem_bandView a x.plan).mp ha) source length hita).2
        omega
      · have hL:=(band_position capacity depth f right hg.2.1 hc hn hd.2 a
          ((mem_bandView a y.plan).mp ha) source length hita).2
        omega

theorem suffix_disjoint (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) :
    (run h (prepareSuffixes text fallback).trie.tree).plan.bandView.Pairwise DisjointBands :=
  build_disjoint (MaskedOrdered.capacity h).1 0 _ _
    (Build.run_correct text fallback (suffixKeys text.size)).2.1 (MaskedOrdered.capacity_value h)
    hn (Nat.zero_le _) (MaskedRunTrieBridge.suffix_positions_nodup text fallback)

theorem pairwise_unique (bs : List (MaskedTraversalEdge.Band h))
    (hd : bs.Pairwise DisjointBands) (a b : MaskedTraversalEdge.Band h)
    (ha : a∈bs) (hb : b∈bs) (source length : Nat)
    (hita : BandCovers a source length) (hitb : BandCovers b source length) : a=b := by
  induction bs with
  | nil => simp at ha
  | cons c cs ih =>
    have hh:=List.pairwise_cons.mp hd
    rcases List.mem_cons.mp ha with hac|ha
    · rcases List.mem_cons.mp hb with hbc|hb
      · exact hac.trans hbc.symm
      · exact False.elim (hh.1 b hb source length (hac ▸ hita) hitb)
    · rcases List.mem_cons.mp hb with hbc|hb
      · exact False.elim (hh.1 a ha source length (hbc ▸ hitb) hita)
      · exact ih hh.2 ha hb

theorem suffix_unique (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) (a b : MaskedTraversalEdge.Band h)
    (ha : (run h (prepareSuffixes text fallback).trie.tree).plan.HasBand a)
    (hb : (run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b)
    (source length : Nat) (hita : BandCovers a source length) (hitb : BandCovers b source length) : a=b :=
  pairwise_unique _ (suffix_disjoint text fallback h hn) a b
    ((mem_bandView _ _).mpr ha) ((mem_bandView _ _).mpr hb) source length hita hitb

/-- Global distinctness follows from local emitters and the actual band
partition. The application must prove its emitted density key really
belongs to that band; global duplicate-freedom is not an input. -/
theorem charges_nodup (bs : List (MaskedTraversalEdge.Band h))
    (hd : bs.Pairwise DisjointBands) (emit : MaskedTraversalEdge.Band h→List (Nat×Nat))
    (localDistinct : ∀b,b∈bs→(emit b).Nodup)
    (hits : ∀b,b∈bs→∀key,key∈emit b→BandCovers b key.1 (2*key.2)) :
    (bs.flatMap emit).Nodup := by
  induction bs with
  | nil => exact List.Pairwise.nil
  | cons b bs ih =>
    have hp:=List.pairwise_cons.mp hd
    have ht:=ih hp.2 (fun c hc=>localDistinct c (List.mem_cons_of_mem b hc))
      (fun c hc=>hits c (List.mem_cons_of_mem b hc))
    change (emit b++bs.flatMap emit).Nodup
    apply List.pairwise_append.mpr
    refine ⟨localDistinct b List.mem_cons_self,ht,?_⟩
    intro k hk j hj he
    subst j
    obtain ⟨c,hc,hk'⟩:=List.mem_flatMap.mp hj
    exact hp.1 c hc k.1 (2*k.2) (hits b List.mem_cons_self k hk)
      (hits c (List.mem_cons_of_mem b hc) k hk')

theorem suffix_charges_nodup (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) (emit : MaskedTraversalEdge.Band h→List (Nat×Nat))
    (localDistinct : ∀b,(run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b→(emit b).Nodup)
    (hits : ∀b,(run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b→
      ∀key,key∈emit b→BandCovers b key.1 (2*key.2)) :
    ((run h (prepareSuffixes text fallback).trie.tree).plan.bandView.flatMap emit).Nodup :=
  charges_nodup _ (suffix_disjoint text fallback h hn) emit
    (fun b hb=>localDistinct b ((mem_bandView b _).mp hb))
    (fun b hb=>hits b ((mem_bandView b _).mp hb))

/-- A density key uses a genuine full-class adjacency at its own doubled
period. This is a local geometric certificate, not a uniqueness premise. -/
def DensityAt (b : MaskedTraversalEdge.Band h) (key : Nat×Nat) : Prop :=
  BandCovers b key.1 (2*key.2) ∧
    ∃i j,Adjacent b.snapshot.occurrences.entries i j ∧ j-i=key.2

theorem density_square (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) (b : MaskedTraversalEdge.Band h)
    (hb : (run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b)
    (key : Nat×Nat) (hd : DensityAt b key) :
    RunGeometry.PrimitiveSquare (ArrayText.read text fallback) text.size key.1 key.2 := by
  obtain ⟨hit,i,j,ha,hq⟩:=hd
  have full:=suffix_band_complete text fallback h hn b hb (2*key.2) key.1 hit.1 hit.2.1 hit.2.2
  have hs:=MaskedLocalAnchor.reset_square (ArrayText.read text fallback) text.size
    key.1 (2*key.2) b.snapshot.occurrences.entries full i j key.1 ha
    (by omega) hit.2.2
  simpa only [hq] using hs

/-- The actual band partition and genuine threshold adjacency suffice
for the global square budget. Actual event-to-band attribution and local
one-shot emission still belong to the repair scheduler. -/
theorem suffix_charges_budget (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) (emit : MaskedTraversalEdge.Band h→List (Nat×Nat))
    (localDistinct : ∀b,(run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b→(emit b).Nodup)
    (hits : ∀b,(run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b→
      ∀key,key∈emit b→DensityAt b key) :
    ((run h (prepareSuffixes text fallback).trie.tree).plan.bandView.flatMap emit).length≤
      2*text.size*(text.size.log2+1) := by
  apply RunBudget.primitive_budget (ArrayText.read text fallback) text.size (text.size.log2+1)
  · exact suffix_charges_nodup text fallback h hn emit localDistinct
      (fun b hb key hk=>(hits b hb key hk).1)
  · intro key hk
    obtain ⟨b,hb,hkey⟩:=List.mem_flatMap.mp hk
    have hs:=density_square text fallback h hn b ((mem_bandView _ _).mp hb) key
      (hits b ((mem_bandView _ _).mp hb) key hkey)
    refine ⟨hs,?_⟩
    have bound:=hs.1
    have sizeBound:=Nat.lt_log2_self (n:=text.size)
    omega

theorem suffix_exactly_once (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) (p : Fin (text.size+1)) (L : Nat)
    (positive : 0<L) (bounded : L≤text.size-p.val) :
    ∃b,((run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b ∧ BandCovers b p.val L) ∧
      ∀c,((run h (prepareSuffixes text fallback).trie.tree).plan.HasBand c ∧ BandCovers c p.val L)→c=b := by
  obtain ⟨b,hb,hlo,hhi,hp⟩:=suffix_cover text fallback h hn p L positive bounded
  refine ⟨b,⟨hb,hlo,hhi,hp⟩,?_⟩
  intro c hc
  exact suffix_unique text fallback h hn c b hc.1 hb p.val L hc.2 ⟨hlo,hhi,hp⟩

end REWB.MaskedTraversalDriver
