import REWB.MaskedSuffixClassLookup

/-! One actual suffix preparation and one retained small-to-large
occurrence execution supply all later class queries. A query reads a
direct terminal slot, follows cached parent jumps, and reads one saved
node record. Neither text nor occurrence lists are visited by the query. -/
namespace REWB.MaskedSuffixClass
open REWB.BoundaryTrie REWB.BoundaryApplication REWB.MaskedRunDiscovery
variable {n h σ : Nat}

def height (n : Nat) : Nat := (n+1).log2+1
def levels (n : Nat) : Nat := StartLocate.levelsFor (2*(n+1))

theorem height_capacity (n : Nat) : n<2^(height n) := by
  have hh:=Nat.lt_log2_self (n:=n+1)
  unfold height
  omega

structure Index (n h : Nat) where
  suffix : SuffixIndex n
  owner : MaskedOrdered.Owner.Store h
  addresses : StartLocate.Store Nat (n+1)
  levels : Nat
  work : Nat

/-- This entrypoint can reuse a suffix preparation already retained by
another index. The concrete `prepare` below constructs it exactly once. -/
def fromSuffixes (h : Nat) (suffix : SuffixIndex n) : Index n h :=
  let saved:=MaskedOrdered.Owner.run h suffix.trie.tree
  let marked:=annotate suffix.trie.tree 0
  let rowWidth:=levels n
  let addresses:=StartLocate.build rowWidth marked.tree
  ⟨suffix,saved.2,addresses,rowWidth,
    suffix.work+saved.2.work+marked.work+addresses.work+rowWidth+8⟩

def prepare (text : Array (Fin σ)) (fallback : Fin σ) : Index text.size (height text.size) :=
  let out:=fromSuffixes (height text.size) (prepareSuffixes text fallback)
  {out with work:=out.work+height text.size+2}

structure Class (h : Nat) where
  node : Nat
  record : MaskedOrdered.Owner.Record h

structure Answer (h : Nat) where
  value : Option (Class h)
  work : Nat

def query (idx : Index n h) (p : Fin (n+1)) (H : Nat) : Answer h :=
  let hit:=StartLocate.query idx.levels idx.addresses p H
  match hit.value with
  | none => ⟨none,hit.work+1⟩
  | some c =>
    ⟨(idx.owner.nodes[c.cell.payload]?).map (fun r=>⟨c.cell.payload,r⟩),hit.work+3⟩

theorem query_work (idx : Index n h) (p : Fin (n+1)) (H : Nat) :
    (query idx p H).work≤6*idx.levels+9 := by
  have hh:=StartLocate.query_work idx.levels idx.addresses p H
  unfold query
  dsimp only
  split <;> dsimp only <;> omega

theorem prepare_suffix (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).suffix=prepareSuffixes text fallback := rfl

theorem prepare_forward (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).suffix.trie.prepared.ranks=
      LCEIndex.prepare (ArrayText.read text fallback) text.size :=
  prepareSuffixes_forward text fallback

theorem prepare_backward (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).suffix.backward=
      LCEIndex.prepareReverse (ArrayText.read text fallback) text.size :=
  prepareSuffixes_backward text fallback

theorem fromSuffixes_locus (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hcap : text.size<2^h) (p : Fin (text.size+1)) (H : Nat) (hH : H≤text.size-p.val) :
    ∃out u pu,(query (fromSuffixes h (prepareSuffixes text fallback)) p H).value=some out ∧
      Tree.Locus (prepareSuffixes text fallback).trie.tree H u ∧
      MaskedOrdered.Owner.Location (prepareSuffixes text fallback).trie.tree none 0 u pu out.node ∧
      MaskedOrdered.Owner.Snapshot u pu out.node out.record ∧
      ∃a,a∈u.leaves ∧ a.start=p.val := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have hg : t.Good (ArrayText.read text fallback) :=
    (BoundaryTrie.Build.run_correct text fallback (suffixKeys text.size)).2.1
  have hn : (annotate t 0).tree.nodes≤2*(text.size+1) := by
    rw [annotate_nodes]
    exact (MaskedRunOwnerCost.suffix_shape text fallback).1
  obtain ⟨hit,v,hh,hc,_,hp,_⟩:=StartLocate.bounded_query_located (2*(text.size+1))
    (annotate t 0).tree (annotate_good _ t 0 hg) hn p (suffix_target text fallback p)
    H (suffix_targetDepth text fallback p H hH)
  obtain ⟨u,pu,hl,hid,_,ha⟩:=cut_locus t 0 none p H v hc
  obtain ⟨rec,hr,hs⟩:=retained_at text fallback h hcap u pu v.payload hid
  refine ⟨⟨v.payload,rec⟩,u,pu,?_,hl,hid,hs,ha⟩
  dsimp only [t] at hh
  change (query (fromSuffixes h (prepareSuffixes text fallback)) p H).value=_
  simp only [query,fromSuffixes,levels,hh,hp,hr,Option.map_some]
  rfl

theorem query_locus (text : Array (Fin σ)) (fallback : Fin σ)
    (p : Fin (text.size+1)) (H : Nat) (hH : H≤text.size-p.val) :
    ∃out u pu,(query (prepare text fallback) p H).value=some out ∧
      Tree.Locus (prepareSuffixes text fallback).trie.tree H u ∧
      MaskedOrdered.Owner.Location (prepareSuffixes text fallback).trie.tree none 0 u pu out.node ∧
      MaskedOrdered.Owner.Snapshot u pu out.node out.record ∧
      ∃a,a∈u.leaves ∧ a.start=p.val :=
  fromSuffixes_locus text fallback (height text.size) (height_capacity text.size) p H hH

/-- Completeness is a consequence of the actual lookup and built suffix
trie, with no supplied occurrence-set or node-boundary oracle. -/
theorem query_complete (text : Array (Fin σ)) (fallback : Fin σ)
    (p : Fin (text.size+1)) (H : Nat) (hH : H≤text.size-p.val) :
    ∃out,(query (prepare text fallback) p H).value=some out ∧ out.record.state.Valid ∧
      Complete (ArrayText.read text fallback) text.size p.val H out.record.state.tree.entries := by
  obtain ⟨out,u,pu,ho,hl,_,hs,ha⟩:=query_locus text fallback p H hH
  exact ⟨out,ho,snapshot_complete text fallback u pu out.node _ H p out.record hl hs ha⟩

theorem query_sound (text : Array (Fin σ)) (fallback : Fin σ)
    (p : Fin (text.size+1)) (H : Nat) (hH : H≤text.size-p.val)
    (out : Class (height text.size)) (ho : (query (prepare text fallback) p H).value=some out) :
    out.record.state.Valid ∧
      Complete (ArrayText.read text fallback) text.size p.val H out.record.state.tree.entries := by
  obtain ⟨v,hv,hs⟩:=query_complete text fallback p H hH
  have he : v=out := Option.some.inj (hv.symm.trans ho)
  exact he ▸ hs

theorem prepare_query_work (text : Array (Fin σ)) (fallback : Fin σ)
    (p : Fin (text.size+1)) (H : Nat) :
    (query (prepare text fallback) p H).work≤6*((2*(text.size+1)).log2+1)+9 :=
  query_work _ p H

theorem query_invalid (text : Array (Fin σ)) (fallback : Fin σ)
    (p : Fin (text.size+1)) (H : Nat) (hH : text.size-p.val<H) :
    (query (prepare text fallback) p H).value=none := by
  have hh:=suffix_cut_invalid text fallback (levels text.size) p H hH
  simp only [query,prepare,fromSuffixes,hh]

theorem query_exists_iff (text : Array (Fin σ)) (fallback : Fin σ)
    (p : Fin (text.size+1)) (H : Nat) :
    (∃out,(query (prepare text fallback) p H).value=some out) ↔ H≤text.size-p.val := by
  constructor
  · rintro ⟨out,ho⟩
    by_cases hh : H≤text.size-p.val
    · exact hh
    · rw [query_invalid text fallback p H (by omega)] at ho
      cases ho
  · intro hh
    obtain ⟨out,ho,_⟩:=query_complete text fallback p H hh
    exact ⟨out,ho⟩

end REWB.MaskedSuffixClass
