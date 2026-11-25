import REWB.MaskedRunCatalogGeometry
import REWB.MaskedSuffixClassIndex

/-! Two shared indexed extensions recover a dense component's run, then
one exact-key lookup supplies its original batch ID and immutable target
counts. Completeness is required only for the proof of least period;
no class traversal or period/divisor search occurs during execution. -/
namespace REWB.MaskedRunCatalog
open REWB.RunGeometry REWB.Periodic REWB.MaskedRunDiscovery
variable {σ n h : Nat}

def discover (idx : Index) (forward backward : RankIndex.Index) (i j L : Nat) : Option Found×Nat :=
  let run:=MaskedRunDiscovery.discover forward backward idx.length i j L
  match run.1 with
  | none => (none,run.2+1)
  | some R =>
      let found:=lookup idx R
      (found.1,run.2+found.2+2)

theorem discover_some (idx : Index) (forward backward : RankIndex.Index) (i j L : Nat) (R : Bounds)
    (he : (MaskedRunDiscovery.discover forward backward idx.length i j L).1=some R) :
    (discover idx forward backward i j L).1=(lookup idx R).1 := by
  simp only [discover,he]

theorem discover_work (f : Nat→Fin σ) (n : Nat) (idx : Index) (hn : idx.length=n) (i j L : Nat) :
    (discover idx (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) i j L).2≤
      26*(n.log2+1)+26*idx.width+31 := by
  have hr:=MaskedRunDiscovery.discover_work f n i j L
  simp only [discover,hn]
  cases he : (MaskedRunDiscovery.discover (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) n i j L).1 with
  | none => simp only [he]; omega
  | some R =>
    have hh:=lookup_work idx R
    simp only [he]
    omega

/-- Uses the exact forward/backward arrays already retained by a suffix
class index; neither rank array is prepared by this call. -/
def discoverShared (idx : Index) (classes : MaskedSuffixClass.Index n h) (i j L : Nat) : Option Found×Nat :=
  discover idx classes.suffix.trie.prepared.ranks classes.suffix.backward i j L

theorem discover_complete (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K base L : Nat) (xs : List Nat) (i j : Nat)
    (hc : Complete (ArrayText.read text fallback) text.size base L xs)
    (ha : Adjacent xs i j) (hd : 2*(j-i)≤L) :
    ∃R id,(discover (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K))
      (LCEIndex.prepare (ArrayText.read text fallback) text.size)
      (LCEIndex.prepareReverse (ArrayText.read text fallback) text.size) i j L).1=some ⟨id,entry target K R⟩ ∧
      (MaskedMutableProgression.Batch.prepare text fallback source K).runs[id]?=some R ∧
      R.Valid (ArrayText.read text fallback) text.size ∧ R.period=j-i ∧ R.lo≤i ∧ j+L≤R.hi ∧
      3*R.period≤R.hi-R.lo := by
  obtain ⟨R,he,hv,hq,hlo,hhi,hcubic⟩:=complete_discovery (ArrayText.read text fallback) text.size base L xs i j hc ha hd
  obtain ⟨id,hid⟩:=(ofBatch_exists text fallback source target K R).mpr ⟨hv,hcubic⟩
  have hrun:=(ofBatch_lookup text fallback source target K R id _).mp hid |>.1
  refine ⟨R,id,?_,hrun,hv,hq,hlo,hhi,hcubic⟩
  rw [discover_some _ _ _ i j L R he]
  exact hid

theorem shared_complete (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K base L : Nat) (xs : List Nat) (i j : Nat)
    (hc : Complete (ArrayText.read text fallback) text.size base L xs)
    (ha : Adjacent xs i j) (hd : 2*(j-i)≤L) :
    ∃R id,(discoverShared (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K))
      (MaskedSuffixClass.prepare text fallback) i j L).1=some ⟨id,entry target K R⟩ ∧
      (MaskedMutableProgression.Batch.prepare text fallback source K).runs[id]?=some R ∧
      R.Valid (ArrayText.read text fallback) text.size ∧ R.period=j-i ∧ R.lo≤i ∧ j+L≤R.hi ∧
      3*R.period≤R.hi-R.lo := by
  simp only [discoverShared,MaskedSuffixClass.prepare_forward,MaskedSuffixClass.prepare_backward]
  exact discover_complete text fallback source target K base L xs i j hc ha hd

def descriptor (idx : Index) (forward backward : RankIndex.Index)
    (d : MaskedClusterDescriptor.Descriptor) (L : Nat) : Option Found×Nat :=
  if 0<d.repetitions then
    let found:=discover idx forward backward d.first (d.first+d.period) L
    (found.1,found.2+3)
  else (none,2)

def descriptorShared (idx : Index) (classes : MaskedSuffixClass.Index n h)
    (d : MaskedClusterDescriptor.Descriptor) (L : Nat) : Option Found×Nat :=
  descriptor idx classes.suffix.trie.prepared.ranks classes.suffix.backward d L

theorem descriptor_work (f : Nat→Fin σ) (n : Nat) (idx : Index) (hn : idx.length=n)
    (d : MaskedClusterDescriptor.Descriptor) (L : Nat) :
    (descriptor idx (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) d L).2≤
      26*(n.log2+1)+26*idx.width+34 := by
  have hh:=discover_work f n idx hn d.first (d.first+d.period) L
  simp only [descriptor]
  split <;> dsimp only <;> omega

/-- The actual queried dense descriptor resolves to a catalog entry
whose run contains the whole component and its current-length copies. -/
theorem descriptor_complete (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (s : MaskedClusterLeaders.State h) (capacity L first base : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hcap : capacity=2^h)
    (d : MaskedClusterDescriptor.Descriptor)
    (hd : (MaskedClusterDescriptor.describeLeader s capacity first).1=some d)
    (hc : Complete (ArrayText.read text fallback) text.size base L s.occurrences.entries)
    (hL : 0<L) (hm : 0<d.repetitions) :
    ∃R id,(descriptorShared (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K))
      (MaskedSuffixClass.prepare text fallback) d L).1=some ⟨id,entry target K R⟩ ∧
      (MaskedMutableProgression.Batch.prepare text fallback source K).runs[id]?=some R ∧
      R.Valid (ArrayText.read text fallback) text.size ∧ R.period=d.period ∧
      R.lo≤d.first ∧ d.last+L≤R.hi := by
  have hs:=(MaskedClusterDescriptor.describeLeader_sound s capacity L first hi hcap d hd).2
  have hg:=hs.geometry s capacity L hi hcap d (ArrayText.read text fallback) text.size base hc hL
  have hp:=hg.period_pos
  have hend:=hg.endpoint
  have hprod:=Nat.mul_pos hm hp
  have hlt : d.first<d.last := by omega
  obtain ⟨u,hu,hadj,_⟩:=hs.first_successor s capacity L hi hcap d hlt
  have hq : d.period=u-d.first := by
    rw [hs.period_eq s capacity d]
    simp only [hlt,if_true,hu,Option.getD_some]
  have hue : u=d.first+d.period := by have hh:=hadj.2.2.1; omega
  rw [hue] at hadj
  have hdense:=hg.dense hm |>.1
  obtain ⟨R,id,he,hid,hv,hrq,hrlo,hrhi,_⟩:=
    shared_complete text fallback source target K base L s.occurrences.entries
      d.first (d.first+d.period) hc hadj (by simpa only [Nat.add_sub_cancel_left] using hdense)
  simp only [Nat.add_sub_cancel_left] at hrq
  have hperiod : OnPeriod (ArrayText.read text fallback) d.first (d.last+L) R.period := by
    rw [hrq]
    exact descriptor_period _ _ _ _ _ d hc hg hm
  have hlast:=((hc d.last).mp hs.lastMember).1
  have hcontains:=run_contains_right _ _ R d.first (d.last+L) hv hrlo
    (by rw [hrq]; omega) hperiod hlast
  refine ⟨R,id,?_,hid,hv,hrq,hrlo,hcontains⟩
  simp only [descriptorShared,descriptor,if_pos hm]
  exact he

theorem descriptorShared_work (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (d : MaskedClusterDescriptor.Descriptor) (L : Nat) :
    (descriptorShared (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K))
      (MaskedSuffixClass.prepare text fallback) d L).2≤52*width text.size+34 := by
  simp only [descriptorShared,MaskedSuffixClass.prepare_forward,MaskedSuffixClass.prepare_backward]
  have hh:=descriptor_work (ArrayText.read text fallback) text.size
    (ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K)) rfl d L
  have hd : text.size.log2+1≤width text.size := MaskedRunEnumerationCost.depth_le text.size
  change _≤26*(text.size.log2+1)+26*width text.size+34 at hh
  omega

end REWB.MaskedRunCatalog
