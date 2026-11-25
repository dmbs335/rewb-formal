import REWB.MaskedOrderedOwnerQuery

/-! Cubic-run coverage of actual owner-tagged generations. The generated
suffix trie supplies the LCA split, and the concrete preorder execution
supplies the fresh event. No equality of two differently ordered event
logs is assumed. Owner qualification and batch validation are separate. -/
namespace REWB.MaskedRunOwnerCoverage
open REWB.BoundaryTrie REWB.MaskedRunDiscovery REWB.Periodic REWB.RunGeometry
open REWB.MaskedOrdered.Owner
variable {n h σ : Nat}

theorem location_subtree {u t : Trie n Nat} (hs : MaskedRunTrieBridge.Subtree u t)
    (parent : Option Parent) (base : Nat) :
    ∃pu id,Location t parent base u pu id := by
  induction hs generalizing parent base with
  | refl => exact ⟨parent,base,.here _ _ _⟩
  | @left stem d l r hh ih =>
    obtain ⟨pu,id,hl⟩:=ih (some ⟨d,select parent d base⟩) (base+1)
    exact ⟨pu,id,.left hl⟩
  | @right stem d l r hh ih =>
    obtain ⟨pu,id,hl⟩:=ih (some ⟨d,select parent d base⟩) (base+1+slots l)
    exact ⟨pu,id,.right hl⟩

theorem node_occurs (f : Nat→Fin σ) (t : Trie n Nat) (a : Key n Nat)
    (hg : t.Good f) (ha : a∈t.leaves) :
    ∀k,k∈positions t→Occurs f n a.start t.depth k := by
  intro k hk
  obtain ⟨b,hb,he⟩:=List.mem_map.mp hk
  have hh:=BoundaryTrie.Tree.depth_common f t hg a b ha hb
  have hbound:=b.bounded
  refine ⟨by have hd:=hh.2.1; omega,?_⟩
  simpa only [he] using hh.2.2.symm

theorem primitive_adjacent_subclass (f : Nat→Fin σ) (n i q H : Nat) (xs : List Nat)
    (hmin : PrimitiveSquare f n i q) (hH : 2*q≤H)
    (hwords : ∀k,k∈xs→Occurs f n i H k) (hi : i∈xs) (hj : i+q∈xs) :
    Adjacent xs i (i+q) := by
  have hq:=hmin.2.1
  refine ⟨hi,hj,by omega,?_⟩
  intro k hk hik hkj
  have hcopy:=(segment_eq_points f i k H).mp (hwords k hk).2.symm
  have hp : Period (shift f i) (2*q) (k-i) := by
    intro a ha
    change f (i+a)=f (i+(a+(k-i)))
    rw [show i+(a+(k-i))=k+a by omega]
    exact hcopy a (by omega)
  have hh:=hmin.2.2.2 (k-i) (by omega) hp
  omega

theorem split_separate (l r : Trie n Nat) (i j : Nat)
    (hn : (positions l++positions r).Nodup)
    (hc : (i∈positions l ∧ j∈positions r) ∨ (i∈positions r ∧ j∈positions l)) :
    ¬(i∈positions l ∧ j∈positions l) ∧ ¬(i∈positions r ∧ j∈positions r) := by
  have hd : ∀p,p∈positions l→p∈positions r→False := by
    intro p hl hr
    exact (List.pairwise_append.mp hn).2.2 p hl p hr rfl
  rcases hc with hc|hc
  · exact ⟨fun hh=>hd j hh.2 hc.2,fun hh=>hd i hc.1 hh.1⟩
  · exact ⟨fun hh=>hd i hh.1 hc.1,fun hh=>hd j hc.2 hh.2⟩

theorem suffix_bounded (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) : PositionsBounded h (prepareSuffixes text fallback).trie.tree := by
  intro p hp
  have hh:=(MaskedRunTrieBridge.suffix_positions text fallback).mem_iff.mp hp
  have hb:=List.mem_range.mp hh
  omega

/-- The exact first coexistence emits a real event in the fast execution.
Its owner is the ID propagated by that execution at the actual LCA depth.
The separate local discovery result is already the original cubic run. -/
theorem cubic_event (text : Array (Fin σ)) (fallback : Fin σ) (R : Bounds)
    (hv : R.Valid (ArrayText.read text fallback) text.size)
    (hcubic : 3*R.period≤R.hi-R.lo) (h : Nat) (hcap : text.size<2^h) :
    ∃(H : Nat) (u : Trie text.size Nat) (pu : Option Parent) (id : Nat),
      Location (prepareSuffixes text fallback).trie.tree none 0 u pu id ∧
      u.depth=H ∧ 2*R.period≤H ∧
      R.lo∈positions u ∧ R.lo+R.period∈positions u ∧
      (⟨select pu H id,(R.lo,R.lo+R.period)⟩ : MaskedOrdered.Owner.Event)∈
        (run h (prepareSuffixes text fallback).trie.tree).2.events.toList ∧
      ((prepareSuffixes text fallback).discover R.lo (R.lo+R.period) H).1=some R := by
  let f:=ArrayText.read text fallback
  let t:=(prepareSuffixes text fallback).trie.tree
  have ht : t.Good f := (Build.run_correct text fallback (suffixKeys text.size)).2.1
  have hp:=hv.2.2.2.1.1
  have hlo:=hv.1
  obtain ⟨H,owner,a,b,pa,pb,hpa,hpb,ha,hb,hlca,_,_,_,hH,_,hdisc⟩:=
    MaskedRunCoverage.actual_suffix_coverage text fallback R hv hcubic
  have hne : a.start≠b.start := by rw [ha,hb]; omega
  obtain ⟨stem,l,r,hsub,hcross⟩:=MaskedRunTrieBridge.lca_split t a b H hlca hne
  let u : Trie text.size Nat:=.node stem H l r
  have hgood : u.Good f := MaskedRunTrieBridge.subtree_good f hsub ht
  have hna : a∈u.leaves := by
    rcases hcross with hh|hh
    · exact List.mem_append_left _ hh.1
    · exact List.mem_append_right _ hh.1
  have hnb : b∈u.leaves := by
    rcases hcross with hh|hh
    · exact List.mem_append_right _ hh.2
    · exact List.mem_append_left _ hh.2
  have hi : R.lo∈positions u := List.mem_map.mpr ⟨a,hna,ha⟩
  have hj : R.lo+R.period∈positions u := List.mem_map.mpr ⟨b,hnb,hb⟩
  have hwords : ∀k,k∈positions u→Occurs f text.size R.lo H k := by
    have hh:=node_occurs f u a hgood hna
    simpa only [ha,u,BoundaryTrie.Tree.depth] using hh
  have hsq : R.SquareStart R.lo := ⟨Nat.le_refl _,by omega⟩
  have hadj:=primitive_adjacent_subclass f text.size R.lo R.period H (positions u)
    (square_start_sound f text.size R hv R.lo hsq) hH hwords hi hj
  have hnd : (positions l++positions r).Nodup := by
    have hh:=(MaskedRunTrieBridge.subtree_positions hsub).nodup
      (MaskedRunTrieBridge.suffix_positions_nodup text fallback)
    simpa only [positions,BoundaryTrie.Tree.leaves,List.map_append] using hh
  have hsep:=split_separate l r R.lo (R.lo+R.period) hnd (by
    rcases hcross with hh|hh
    · exact Or.inl ⟨List.mem_map.mpr ⟨a,hh.1,ha⟩,List.mem_map.mpr ⟨b,hh.2,hb⟩⟩
    · exact Or.inr ⟨List.mem_map.mpr ⟨a,hh.1,ha⟩,List.mem_map.mpr ⟨b,hh.2,hb⟩⟩)
  obtain ⟨pu,id,hl⟩:=location_subtree hsub none 0
  have hbounded:=suffix_bounded text fallback h hcap
  have he:=visit_at_event (h:=h) (MaskedOrdered.capacity h).1 t none
    {work:=(MaskedOrdered.capacity h).2} (MaskedOrdered.capacity_value h) hbounded
    stem H l r pu id R.lo (R.lo+R.period) hl hadj hsep.1 hsep.2
  exact ⟨H,u,pu,id,hl,rfl,hH,hi,hj,he,hdisc⟩

/-- The event's propagated owner ID resolves to the actual completed
occurrence snapshot, where its pair is still truly adjacent. -/
theorem cubic_owner_record (text : Array (Fin σ)) (fallback : Fin σ) (R : Bounds)
    (hv : R.Valid (ArrayText.read text fallback) text.size)
    (hcubic : 3*R.period≤R.hi-R.lo) (h : Nat) (hcap : text.size<2^h) :
    ∃(owner : Nat) (rec : Record h),
      (⟨owner,(R.lo,R.lo+R.period)⟩ : MaskedOrdered.Owner.Event)∈
        (run h (prepareSuffixes text fallback).trie.tree).2.events.toList ∧
      (run h (prepareSuffixes text fallback).trie.tree).2.nodes[owner]?=some rec ∧
      rec.state.Valid ∧ Adjacent rec.state.tree.entries R.lo (R.lo+R.period) ∧
      ((prepareSuffixes text fallback).discover R.lo (R.lo+R.period) rec.depth).1=some R := by
  let f:=ArrayText.read text fallback
  let t:=(prepareSuffixes text fallback).trie.tree
  have ht : t.Good f := (Build.run_correct text fallback (suffixKeys text.size)).2.1
  obtain ⟨H,u,pu,id,hl,hdepth,hH,hi,hj,he,hdisc⟩:=cubic_event text fallback R hv hcubic h hcap
  obtain ⟨v,pv,hlv,hdv,_,hlocus,hmv⟩:=location_owner_mem f ht hl
  rw [hdepth] at hlv hdv hlocus
  have hmemv : ∀k,k∈positions u→k∈positions v := by
    intro k hk
    obtain ⟨a,ha,he⟩:=List.mem_map.mp hk
    exact List.mem_map.mpr ⟨a,hmv a ha,he⟩
  have hiv:=hmemv R.lo hi
  have hjv:=hmemv (R.lo+R.period) hj
  obtain ⟨a,ha,has⟩:=List.mem_map.mp hiv
  have hfull : Complete f text.size R.lo H (positions v) := by
    have hh:=prepareSuffixes_complete text fallback v H a hlocus ha
    simpa only [has] using hh
  have hsq : R.SquareStart R.lo := ⟨Nat.le_refl _,by have hlo:=hv.1; omega⟩
  have hadj:=MaskedRunCoverage.primitive_adjacent f text.size R.lo R.period H (positions v)
    (square_start_sound f text.size R hv R.lo hsq) hH hfull hiv hjv
  obtain ⟨rec,hget,hs⟩:=visit_at (h:=h) (MaskedOrdered.capacity h).1 t none
    {work:=(MaskedOrdered.capacity h).2} (MaskedOrdered.capacity_value h)
    (suffix_bounded text fallback h hcap) v pv (select pu H id) hlv
  have hrdepth : rec.depth=H := hs.1.trans hdv
  have hrmem:=hs.2.2.2.2
  refine ⟨select pu H id,rec,he,hget,hs.2.2.2.1,?_,?_⟩
  · exact ⟨(hrmem _).mpr hadj.1,(hrmem _).mpr hadj.2.1,hadj.2.2.1,
      fun k hk hik hkj=>hadj.2.2.2 k ((hrmem k).mp hk) hik hkj⟩
  · rwa [hrdepth]

/-- Every cubic run is returned by an actual surviving-generation
validator call on the array of completed owner snapshots. -/
theorem cubic_probe (text : Array (Fin σ)) (fallback : Fin σ) (R : Bounds)
    (hv : R.Valid (ArrayText.read text fallback) text.size)
    (hcubic : 3*R.period≤R.hi-R.lo) (h : Nat) (hcap : text.size<2^h) :
    ∃e,e∈(run h (prepareSuffixes text fallback).trie.tree).2.events.toList ∧
      (probe (prepareSuffixes text fallback).trie.prepared.ranks
        (prepareSuffixes text fallback).backward text.size (MaskedOrdered.capacity h).1
        (run h (prepareSuffixes text fallback).trie.tree).2.nodes e).1=some R := by
  obtain ⟨owner,rec,he,hr,hvalid,ha,hd⟩:=cubic_owner_record text fallback R hv hcubic h hcap
  let e : MaskedOrdered.Owner.Event:=⟨owner,(R.lo,R.lo+R.period)⟩
  refine ⟨e,he,?_⟩
  rw [probe_accept _ _ _ _ _ e rec hr hvalid (MaskedOrdered.capacity_value h) ha]
  exact hd

end REWB.MaskedRunOwnerCoverage
