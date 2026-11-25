import REWB.MaskedDensityCharge

/-! Primitive-square charging on the actual constructed suffix trie.
Distinct canonical reset records inject into position/period pairs, so
the three-squares budget applies. The remaining scheduler obligation is
to attach each emitted repair to this first-threshold ID, certify the
full-class adjacency, and emit each (ID,start,period) record at most once.
No dynamic event-generation or repair-time theorem is claimed here. -/
namespace REWB.MaskedDensityCharge
open REWB.BoundaryTrie
open REWB.MaskedRunDiscovery
open REWB.MaskedOrdered.Owner
open REWB.RunGeometry
variable {σ : Nat}

def Certified (text : Array (Fin σ)) (fallback : Fin σ) (c : Charge) : Prop :=
  At (prepareSuffixes text fallback).trie.tree c ∧
    PrimitiveSquare (ArrayText.read text fallback) text.size c.start c.period

theorem keys_nodup {n : Nat} (t : Tree n Nat) (hn : (positions t).Nodup)
    (cs : List Charge) (hc : cs.Nodup) (ha : ∀c,c∈cs→At t c) : (cs.map Charge.key).Nodup := by
  induction cs with
  | nil => exact List.nodup_nil
  | cons c cs ih =>
    have hnd:=List.nodup_cons.mp hc
    have hhere:=ha c List.mem_cons_self
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih hnd.2 (fun a hm=>ha a (List.mem_cons_of_mem _ hm))⟩
    intro hm
    obtain ⟨a,ham,hkey⟩:=List.mem_map.mp hm
    have he:=at_injective t hn a c (ha a (List.mem_cons_of_mem _ ham)) hhere hkey
    exact hnd.1 (he ▸ ham)

/-- The primitive certificate is obtained from a real complete class
of the constructed suffix trie. Only genuine, surviving adjacency is
used; temporary partial-merge adjacency is insufficient. -/
theorem certify_completed_reset (text : Array (Fin σ)) (fallback : Fin σ)
    (v : Tree text.size Nat) (a : Key text.size Nat) (L i j p id : Nat)
    (hl : Tree.Locus (prepareSuffixes text fallback).trie.tree L v) (ha : a∈v.leaves)
    (hadj : Adjacent (positions v) i j) (hdense : 2*(j-i)≤L) (hp : p∈positions v)
    (hat : At (prepareSuffixes text fallback).trie.tree ⟨id,p,j-i⟩) :
    Certified text fallback ⟨id,p,j-i⟩ := by
  refine ⟨hat,?_⟩
  exact MaskedLocalAnchor.reset_square (ArrayText.read text fallback) text.size a.start L (positions v)
    (prepareSuffixes_complete text fallback v L a hl ha) i j p hadj hdense hp

/-- At the density threshold itself, both the canonical location and
the primitive square follow directly from one actual locus adjacency. -/
theorem certify_threshold (text : Array (Fin σ)) (fallback : Fin σ)
    (u : Tree text.size Nat) (parent : Option Parent) (id i j p : Nat)
    (hl : Location (prepareSuffixes text fallback).trie.tree none 0 u parent id)
    (hc : Tree.Locus (prepareSuffixes text fallback).trie.tree (2*(j-i)) u)
    (hp : p∈positions u) (hadj : Adjacent (positions u) i j) :
    Certified text fallback ⟨id,p,j-i⟩ := by
  obtain ⟨a,ha,_⟩:=List.mem_map.mp hp
  exact certify_completed_reset text fallback u a (2*(j-i)) i j p id hc ha hadj
    (Nat.le_refl _) hp ⟨u,parent,hl,hc,hp⟩

/-- Every primitive square has one canonical actual preorder charge
ID. This is structural existence, not an enumeration of repair events. -/
theorem canonical_exists (text : Array (Fin σ)) (fallback : Fin σ) (p q : Nat)
    (hs : PrimitiveSquare (ArrayText.read text fallback) text.size p q) :
    ∃id,Certified text fallback ⟨id,p,q⟩ ∧
      ∀other,Certified text fallback ⟨other,p,q⟩→other=id := by
  let i : Fin (text.size+1):=⟨p,by have hh:=hs.1; omega⟩
  let a:=suffixKey text.size i
  obtain ⟨path,hpath⟩:=(Build.run_paths text fallback (suffixKeys text.size) a).mpr (suffixKey_mem text.size i)
  have hlen : 2*q≤a.length := by change 2*q≤text.size-p; have hh:=hs.1; omega
  obtain ⟨u,_,hcut,ha⟩:=Tree.locate_correct (ArrayText.read text fallback)
    (prepareSuffixes text fallback).trie.tree path a (2*q)
    (Build.run_correct text fallback (suffixKeys text.size)).2.1 hpath hlen
  obtain ⟨parent,id,hl,_⟩:=locus_location hcut none 0 (by intro p hp; cases hp)
  have hp : p∈positions u := List.mem_map.mpr ⟨a,ha,rfl⟩
  have hc : Certified text fallback ⟨id,p,q⟩ := ⟨⟨u,parent,hl,hcut,hp⟩,hs⟩
  refine ⟨id,hc,?_⟩
  intro other ho
  have he:=at_injective _ (MaskedRunTrieBridge.suffix_positions_nodup text fallback)
    ⟨other,p,q⟩ ⟨id,p,q⟩ ho.1 hc.1 rfl
  exact congrArg Charge.node he

/-- A canonical charge resolves to an actual saved owner record. The
parent-depth inequality makes that record its own complete-class owner. -/
theorem actual_record (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat) (hcap : text.size<2^h)
    (c : Charge) (hc : At (prepareSuffixes text fallback).trie.tree c) :
    ∃r,(run h (prepareSuffixes text fallback).trie.tree).2.nodes[c.node]?=some r ∧
      r.owner=c.node ∧ 2*c.period≤r.depth ∧ c.start∈r.state.tree.entries := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have hb : PositionsBounded h t := by
    intro p hp
    have hh:=List.mem_range.mp ((MaskedRunTrieBridge.suffix_positions text fallback).mem_iff.mp hp)
    omega
  obtain ⟨u,parent,hl,_,hp,hbelow,hdepth⟩:=at_parent t
    (MaskedRunTrieBridge.suffix_positions_nodup text fallback) c hc
  let initial : Store h:={work:=(REWB.MaskedOrdered.capacity h).2}
  obtain ⟨r,hr,hs⟩:=visit_at (REWB.MaskedOrdered.capacity h).1 t none initial
    (REWB.MaskedOrdered.capacity_value h) hb u parent c.node hl
  have howner : select parent u.depth c.node=c.node := by
    cases parent with
    | none => rfl
    | some par =>
      have hh:=hbelow par rfl
      exact select_strict par u.depth c.node (by omega)
  refine ⟨r,hr,hs.2.1.trans howner,?_,(hs.2.2.2.2 c.start).mpr hp⟩
  rw [hs.1]
  exact hdepth

/-- Actual suffix-trie uniqueness converts record distinctness into
position/period distinctness, closing the structural reset-charge bound. -/
theorem certified_budget (text : Array (Fin σ)) (fallback : Fin σ) (cs : List Charge)
    (hd : cs.Nodup) (hc : ∀c,c∈cs→Certified text fallback c) :
    cs.length≤2*text.size*(text.size.log2+1) := by
  have hkeys:=keys_nodup (prepareSuffixes text fallback).trie.tree
    (MaskedRunTrieBridge.suffix_positions_nodup text fallback) cs hd (fun c hm=>(hc c hm).1)
  have hbudget:=RunBudget.primitive_budget (ArrayText.read text fallback) text.size (text.size.log2+1)
    (cs.map Charge.key) hkeys (by
      intro key hkey
      obtain ⟨c,hm,he⟩:=List.mem_map.mp hkey
      subst key
      have hs:=(hc c hm).2
      refine ⟨hs,?_⟩
      have hb:=hs.1
      have hn:=Nat.lt_log2_self (n:=text.size)
      change c.period<2^(text.size.log2+1)
      omega)
  simpa only [List.length_map] using hbudget

end REWB.MaskedDensityCharge
