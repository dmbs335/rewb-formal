import REWB.MaskedTraversalNeighborAnchors

/-! A retained anchor is an actual populated array slot plus a certificate
for this cluster's canonical AP grid. `copies` is proof-only: no runtime
loop enumerates it to build or refresh a bank. Using the cluster's own
first as the H-word base allows other clusters to join a shorter complete
class without assuming that they share this longer H-prefix.
-/
namespace REWB.MaskedTraversalRetained
open REWB.MaskedClusterDescriptor REWB.MaskedRunDiscovery REWB.MaskedTraversalBankReady REWB.MaskedTraversalRepair
variable {α : Type} {h : Nat}

def copies (d : Descriptor) : List Nat :=
  (List.range (d.repetitions+1)).map (fun k=>d.first+k*d.period)

theorem copies_mem (d : Descriptor) (p : Nat) :
    p∈copies d↔∃k,k≤d.repetitions ∧ p=d.first+k*d.period := by
  simp only [copies,List.mem_map,List.mem_range,Nat.lt_succ_iff]
  constructor <;> rintro ⟨k,hk,he⟩ <;> exact ⟨k,hk,he.symm⟩

def Own (f : Nat→α) (n L : Nat) (anchors : Array (Option Nat)) (first : Nat) (d : Descriptor) : Prop :=
  ∃H,(anchors[first]?).join=some H ∧
    MaskedLocalAnchor.Certificate f n d.first L (copies d) d.last (d.nextAt n) d.previous d.following H

def Away (partition : MaskedClusterLeaders.State h) (capacity : Nat) (f : Nat→α) (n L : Nat)
    (anchors : Array (Option Nat)) (keys : List Nat) : Prop :=
  ∀first,first∉keys→∀d,(describeLeader partition capacity first).1=some d→Own f n L anchors first d

theorem Own.bounds {f : Nat→α} {n L first : Nat} {anchors : Array (Option Nat)} {d : Descriptor}
    (ho : Own f n L anchors first d) :
    d.last+readAnchor anchors first L≤n ∧
      ∀p,d.following=some p→d.last+readAnchor anchors first L≤p := by
  obtain ⟨H,hH,cert⟩:=ho
  simp only [readAnchor,hH,Option.getD_some]
  exact ⟨cert.lastBound,cert.followingSafe⟩

theorem Away.bounds {partition : MaskedClusterLeaders.State h} {capacity n L : Nat}
    {f : Nat→α} {anchors : Array (Option Nat)} {keys : List Nat}
    (ha : Away partition capacity f n L anchors keys) :
    AnchorBoundsAway partition capacity n L anchors keys := by
  intro first hn d hd
  exact (ha first hn d hd).bounds

theorem anchorsLoop_slot (L : Nat) (ps : List Nat) (anchors : Array (Option Nat)) (work p : Nat) :
    (anchorsLoop L ps anchors work).1[p]?=
      if p∈ps then (if p<anchors.size then some (some L) else none) else anchors[p]? := by
  induction ps generalizing anchors work with
  | nil => simp [anchorsLoop]
  | cons q ps ih =>
    rw [anchorsLoop,ih]
    simp only [resetAnchor,Array.size_setIfInBounds]
    by_cases hp : p∈ps
    · simp only [hp,if_true,List.mem_cons,or_true]
    · simp only [hp,if_false,List.mem_cons,or_false]
      by_cases he : q=p
      · subst q
        simp only [if_pos rfl,if_true,Array.getElem?_setIfInBounds_self]
      · simp only [Array.getElem?_setIfInBounds_ne he,Ne.symm he,if_false]

theorem reset_own (partition : MaskedClusterLeaders.State h) (capacity n base L first : Nat)
    (f : Nat→α) (anchors : Array (Option Nat)) (keys : List Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (d : Descriptor) (hd : (describeLeader partition capacity first).1=some d)
    (hfull : Complete f n base L partition.occurrences.entries) (hL : 0<L)
    (hp : first∈keys) (hb : first<anchors.size) :
    Own f n L (anchorsLoop L keys anchors 0).1 first d := by
  have hs:=(describeLeader_sound partition capacity L first hi hc d hd).2
  have hg:=describeLeader_geometry partition capacity L first hi hc d hd f n base hfull hL
  refine ⟨L,?_,?_⟩
  · rw [anchorsLoop_slot,if_pos hp,if_pos hb]
    rfl
  · refine ⟨Nat.le_refl _,?_,hg.anchor.lastBound,Iff.rfl,hg.anchor.previousSafe,hg.anchor.followingSafe⟩
    intro p hp
    obtain ⟨k,hk,he⟩:=(copies_mem d p).mp hp
    have hm : p∈partition.occurrences.entries := ((hg.members p).mpr ⟨k,hk,he⟩).1
    have ho:=(hfull p).mp hm
    have hf:=(hfull d.first).mp hs.firstMember
    exact ⟨ho.1,ho.2.trans hf.2.symm⟩

theorem reset_all (partition : MaskedClusterLeaders.State h) (capacity n base L : Nat)
    (f : Nat→α) (anchors : Array (Option Nat)) (keys : List Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : Complete f n base L partition.occurrences.entries) (hL : 0<L) (hn : n<anchors.size)
    (ha : Away partition capacity f n L anchors keys) :
    Away partition capacity f n L (anchorsLoop L keys anchors 0).1 [] := by
  intro first _ d hd
  by_cases hp : first∈keys
  · have hs:=describeLeader_sound partition capacity L first hi hc d hd
    have hm:=((hfull d.first).mp hs.2.firstMember).1
    have hb : first<anchors.size := by rw [←hs.1]; omega
    exact reset_own partition capacity n base L first f anchors keys hi hc d hd hfull hL hp hb
  · obtain ⟨H,hH,cert⟩:=ha first hp d hd
    refine ⟨H,?_,cert⟩
    rw [anchorsLoop_slot,if_neg hp]
    exact hH

theorem transport_same (before after : MaskedClusterLeaders.State h) (capacity : Nat)
    (f : Nat→α) (n L : Nat) (anchors : Array (Option Nat)) (oldKeys newKeys : List Nat)
    (hgrow : ∀p,p∈oldKeys→p∈newKeys)
    (hdesc : ∀p,p∉newKeys→(describeLeader after capacity p).1=(describeLeader before capacity p).1)
    (ha : Away before capacity f n L anchors oldKeys) : Away after capacity f n L anchors newKeys := by
  intro first hn d hd
  have hold : first∉oldKeys := by intro hm; exact hn (hgrow first hm)
  exact ha first hold d ((hdesc first hn).symm.trans hd)

end REWB.MaskedTraversalRetained
