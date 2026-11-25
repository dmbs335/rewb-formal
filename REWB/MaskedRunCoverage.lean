import REWB.MaskedRunDiscoveryLocus

/-! Every cubic run is recovered by true-gap discovery at an actual
complete suffix-trie class. The pair is the run's first two q-spaced
copies; its LCA depth selects the complete owner of any zero-depth
binary refinements. This is coverage for the generated trie and local
discovery call, not yet an enumeration schedule or its aggregate cost. -/
namespace REWB.MaskedRunCoverage
open REWB.Periodic REWB.RunGeometry REWB.MaskedRunDiscovery REWB.BoundaryTrie
variable {α : Type} {σ : Nat}

/-- The first two q-spaced copies of a cubic run share a 2q prefix. -/
theorem cubic_pair (f : Nat→α) (n : Nat) (R : Bounds)
    (hv : R.Valid f n) (hc : 3*R.period≤R.hi-R.lo) :
    R.lo+R.period+2*R.period≤n ∧
      segment f R.lo (2*R.period)=segment f (R.lo+R.period) (2*R.period) := by
  have hloRun:=hv.1
  have hn:=hv.2.1
  have hp:=run_on f n R.lo R.hi R.period hv
  refine ⟨by omega,(segment_eq_points f R.lo (R.lo+R.period) (2*R.period)).mpr ?_⟩
  intro a ha
  have hh:=hp (R.lo+a) (by omega) (by omega)
  simpa only [show R.lo+a+R.period=R.lo+R.period+a by omega] using hh

/-- No complete longer-prefix class can insert a start strictly between
the two q-spaced copies of a minimum-period-q square. -/
theorem primitive_adjacent (f : Nat→α) (n i q H : Nat) (xs : List Nat)
    (hmin : PrimitiveSquare f n i q) (hH : 2*q≤H)
    (hfull : Complete f n i H xs) (hi : i∈xs) (hj : i+q∈xs) :
    Adjacent xs i (i+q) := by
  have hq:=hmin.2.1
  refine ⟨hi,hj,by omega,?_⟩
  intro k hk hik hkj
  have hcopy:=(segment_eq_points f i k H).mp ((hfull k).mp hk).2.symm
  have hP : Period (shift f i) (2*q) (k-i) := by
    intro a ha
    change f (i+a)=f (i+(a+(k-i)))
    rw [show i+(a+(k-i))=k+a by omega]
    exact hcopy a (by omega)
  have hh:=hmin.2.2.2 (k-i) (by omega) hP
  omega

theorem recover_run (f : Nat→Fin σ) (n : Nat) (R : Bounds)
    (hv : R.Valid f n) (hc : 3*R.period≤R.hi-R.lo) (H : Nat)
    (xs : List Nat) (hH : 2*R.period≤H)
    (hfull : Complete f n R.lo H xs)
    (hi : R.lo∈xs) (hj : R.lo+R.period∈xs) :
    (discover (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n)
      n R.lo (R.lo+R.period) H).1=some R := by
  have hloRun:=hv.1
  have hsquare : R.SquareStart R.lo := ⟨Nat.le_refl _,by omega⟩
  have hmin:=square_start_sound f n R hv R.lo hsquare
  have ha:=primitive_adjacent f n R.lo R.period H xs hmin hH hfull hi hj
  obtain ⟨S,hs,hvS,hperiod,hlo,hhi,_⟩:=complete_discovery f n R.lo H xs R.lo
    (R.lo+R.period) hfull ha (by omega)
  have hp : R.period=S.period := by omega
  have hS : S.SquareStart R.lo := ⟨hlo,by omega⟩
  have he:=square_start_unique f n R S hv hvS R.lo hp hsquare hS
  rwa [←he] at hs

/-- A locus selected at depth H and containing keys with exact LCP H
has depth exactly H. Its root is the complete owner, rather than a
possibly partial equal-depth binary descendant. -/
theorem exact_locus_depth (f : Nat→Fin σ) {n : Nat} (t u : Tree n Nat)
    (H : Nat) (a b : Key n Nat) (hg : t.Good f)
    (hl : Tree.Locus t H u) (ha : a∈u.leaves) (hb : b∈u.leaves)
    (he : Key.Exact f a b H) : u.depth=H := by
  have hlow:=Tree.locus_depth hl
  have hhigh:=he.2 u.depth (Tree.depth_common f u (Tree.locus_good f hg hl) a b ha hb)
  omega

/-- Actual generated paths, their LCA, the complete class owner, true
consecutiveness and the indexed extension together recover any cubic
run. No all-run list or supplied tree is an input to this result. -/
theorem actual_suffix_coverage (text : Array (Fin σ)) (fallback : Fin σ)
    (R : Bounds) (hv : R.Valid (ArrayText.read text fallback) text.size)
    (hc : 3*R.period≤R.hi-R.lo) :
    ∃ (H : Nat) (u : Tree text.size Nat) (a b : Key text.size Nat) (pa pb : List Bool),
      (prepareSuffixes text fallback).trie.tree.lookup pa=some a ∧
      (prepareSuffixes text fallback).trie.tree.lookup pb=some b ∧
      a.start=R.lo ∧ b.start=R.lo+R.period ∧
      Tree.LCA (prepareSuffixes text fallback).trie.tree a b H ∧
      Tree.locate H (prepareSuffixes text fallback).trie.tree pa=some u ∧
      Tree.Locus (prepareSuffixes text fallback).trie.tree H u ∧
      u.depth=H ∧ 2*R.period≤H ∧
      Adjacent (positions u) R.lo (R.lo+R.period) ∧
      ((prepareSuffixes text fallback).discover R.lo (R.lo+R.period) H).1=some R := by
  let f:=ArrayText.read text fallback
  let t:=(prepareSuffixes text fallback).trie.tree
  have hpair:=cubic_pair f text.size R hv hc
  have hloRun:=hv.1
  have hn:=hv.2.1
  let i : Fin (text.size+1):=⟨R.lo,by omega⟩
  let j : Fin (text.size+1):=⟨R.lo+R.period,by omega⟩
  let a:=suffixKey text.size i
  let b:=suffixKey text.size j
  have hg : t.Good f := (Build.run_correct text fallback (suffixKeys text.size)).2.1
  obtain ⟨pa,hpa⟩:=(Build.run_paths text fallback (suffixKeys text.size) a).mpr
    (suffixKey_mem text.size i)
  obtain ⟨pb,hpb⟩:=(Build.run_paths text fallback (suffixKeys text.size) b).mpr
    (suffixKey_mem text.size j)
  have hpa' : t.lookup pa=some a := hpa
  have hpb' : t.lookup pb=some b := hpb
  obtain ⟨H,hlca,hexact⟩:=Tree.path_commonPrefix f t a b pa pb hg hpa' hpb'
  have hcommon : Key.Common f a b (2*R.period) := by
    refine ⟨?_,?_,hpair.2⟩
    · change 2*R.period≤text.size-R.lo
      omega
    · change 2*R.period≤text.size-(R.lo+R.period)
      omega
  have hH:=hexact.2 (2*R.period) hcommon
  obtain ⟨u,hu,hl,ha⟩:=Tree.locate_correct f t pa a H hg hpa' hexact.1.1
  have hb : b∈u.leaves :=
    (Tree.locus_complete f hg hl a b ha (Tree.lookup_mem t pb b hpb')).mp hexact.1
  have hfull : Complete f text.size R.lo H (positions u) :=
    prepareSuffixes_complete text fallback u H a hl ha
  have hi : R.lo∈positions u := List.mem_map.mpr ⟨a,ha,rfl⟩
  have hj : R.lo+R.period∈positions u := List.mem_map.mpr ⟨b,hb,rfl⟩
  have hsq : R.SquareStart R.lo := ⟨Nat.le_refl _,by omega⟩
  have hadj:=primitive_adjacent f text.size R.lo R.period H (positions u)
    (square_start_sound f text.size R hv R.lo hsq) hH hfull hi hj
  have hrecover:=recover_run f text.size R hv hc H (positions u) hH hfull hi hj
  refine ⟨H,u,a,b,pa,pb,hpa',hpb',rfl,rfl,hlca,hu,hl,
    exact_locus_depth f t u H a b hg hl ha hb hexact,hH,hadj,?_⟩
  simpa only [SuffixIndex.discover,prepareSuffixes_forward,prepareSuffixes_backward] using hrecover

end REWB.MaskedRunCoverage
