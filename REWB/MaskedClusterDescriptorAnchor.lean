import REWB.MaskedClusterDescriptorSound
import REWB.MaskedClusterDescriptorProgression

/-! Geometry derived from the actual descriptor query. The maintained
leader invariant suffices for neighbor and ownership facts. Exact APs
and reset certificates additionally require the full unmasked occurrence
class; they are never asserted for an intermediate merge subset.
All lists and certificates in this module occur only in propositions.
The executable query remains the constant number of ordered-tree paths
defined in `MaskedClusterDescriptor`. -/
namespace REWB.MaskedClusterDescriptor
open REWB.MaskedOrdered REWB.MaskedRunDiscovery REWB.MaskedLocalAnchor REWB.Periodic
variable {h : Nat} {α : Type}

theorem Sound.period_eq (s : MaskedClusterLeaders.State h) (capacity : Nat) (d : Descriptor)
    (hd : Sound s capacity d) :
    d.period = if d.first<d.last then
      (Tree.succ s.occurrences capacity d.first).1.getD d.first-d.first else 1 :=
  congrArg Descriptor.period hd.materialized

theorem Sound.repetitions_eq (s : MaskedClusterLeaders.State h) (capacity : Nat) (d : Descriptor)
    (hd : Sound s capacity d) : d.repetitions=(d.last-d.first)/d.period := by
  have hh:=congrArg Descriptor.repetitions hd.materialized
  rw [hd.period_eq s capacity d]
  exact hh

theorem Sound.previous_eq (s : MaskedClusterLeaders.State h) (capacity : Nat) (d : Descriptor)
    (hd : Sound s capacity d) :
    d.previous=if d.first<d.last then (Tree.pred s.occurrences capacity d.last).1 else none :=
  congrArg Descriptor.previous hd.materialized

theorem Sound.following_eq (s : MaskedClusterLeaders.State h) (capacity : Nat) (d : Descriptor)
    (hd : Sound s capacity d) :
    d.following=match d.next with
      | none => none
      | some p => (Tree.succ s.occurrences capacity p).1 := by
  have hh:=congrArg Descriptor.following hd.materialized
  cases he : d.next <;> simpa only [finish,he] using hh

theorem Sound.no_internal_leader (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (d : Descriptor) (hd : Sound s capacity d)
    (x : Nat) (_hx : x∈s.occurrences.entries) (hf : d.first<x) (hl : x≤d.last) :
    ¬MaskedClusterLeaders.Leader s.occurrences.entries L x := by
  intro hleader
  have hx':= (hi.represented x).mpr hleader
  have hn:=hd.nextSpec
  have ht:=hd.lastSpec
  cases he : d.next with
  | none =>
    rw [he] at hn
    have hh:=hn x hx'
    omega
  | some next =>
    rw [he] at hn ht
    have hh:=hn.2.2 x hx' hf
    have hb:=ht.2.1
    omega

theorem Sound.first_successor (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (hlt : d.first<d.last) :
    ∃u,(Tree.succ s.occurrences capacity d.first).1=some u ∧
      Adjacent s.occurrences.entries d.first u ∧ u≤d.last := by
  have hs:=Tree.succ_correct s.occurrences capacity d.first hi.occGood hi.occFits hc
  cases he : (Tree.succ s.occurrences capacity d.first).1 with
  | none =>
    rw [he] at hs
    have hh:=hs d.last hd.lastMember
    omega
  | some u =>
    rw [he] at hs
    refine ⟨u,rfl,⟨hd.firstMember,hs.1,hs.2.1,?_⟩,hs.2.2 d.last hd.lastMember hlt⟩
    intro x hx hfx hxu
    have hh:=hs.2.2 x hx hfx
    omega

theorem Sound.previous_adjacency (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (p : Nat) (hp : d.previous=some p) :
    Adjacent s.occurrences.entries p d.last ∧ 2*(d.last-p)≤L ∧ d.first≤p := by
  have he:=hd.previous_eq s capacity d
  by_cases hlt : d.first<d.last
  · simp only [hlt,if_true] at he
    have hs:=Tree.pred_correct s.occurrences capacity d.last hi.occGood hi.occFits hc
    rw [he.symm.trans hp] at hs
    have ha : Adjacent s.occurrences.entries p d.last := by
      refine ⟨hs.1,hd.lastMember,hs.2.1,?_⟩
      intro x hx hpx hxl
      have hh:=hs.2.2 x hx hxl
      omega
    exact ⟨ha,nonleader_dense _ L p d.last ha
      (hd.no_internal_leader s capacity L hi d d.last hd.lastMember hlt (Nat.le_refl _)),
      hs.2.2 d.first hd.firstMember hlt⟩
  · simp only [hlt,if_false] at he
    rw [he] at hp
    cases hp

theorem Sound.next_adjacency (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (d : Descriptor) (hd : Sound s capacity d)
    (next : Nat) (he : d.next=some next) :
    Adjacent s.occurrences.entries d.last next ∧ L<2*(next-d.last) := by
  have hn:=hd.nextSpec
  have hl:=hd.lastSpec
  rw [he] at hn hl
  have hleader:=(hi.represented next).mp hn.1
  refine ⟨⟨hd.lastMember,hleader.1,hl.2.1,?_⟩,hleader.2 d.last hd.lastMember hl.2.1⟩
  intro x hx hlx hxn
  have hh:=hl.2.2 x hx hxn
  omega

theorem Sound.following_adjacency (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (next : Nat) (hn : d.next=some next)
    (p : Nat) (hp : d.following=some p) : Adjacent s.occurrences.entries next p := by
  have he:=hd.following_eq s capacity d
  simp only [hn] at he
  have hs:=Tree.succ_correct s.occurrences capacity next hi.occGood hi.occFits hc
  rw [he.symm.trans hp] at hs
  have ha:=hd.next_adjacency s capacity L hi d next hn
  refine ⟨ha.1.2.1,hs.1,hs.2.1,?_⟩
  intro x hx hnx hxp
  have hh:=hs.2.2 x hx hnx
  omega

theorem Sound.anchor (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (f : Nat→α) (n base : Nat)
    (hfull : Complete f n base L s.occurrences.entries) (copies : List Nat)
    (hsub : ∀k,k∈copies→k∈s.occurrences.entries) :
    Certificate f n base L copies d.last (d.nextAt n) d.previous d.following L := by
  cases he : d.next with
  | none =>
    have hf : d.following=none := by
      have hh:=hd.following_eq s capacity d
      simpa only [he] using hh
    simp only [Descriptor.nextAt,he,Option.getD_none,hf]
    exact reset_terminal f n base L s.occurrences.entries copies hfull hsub d.last hd.lastMember
      d.previous (fun p hp=>(hd.previous_adjacency s capacity L hi hc d p hp).1.1)
  | some next =>
    have ha:=hd.next_adjacency s capacity L hi d next he
    simp only [Descriptor.nextAt,he,Option.getD_some]
    exact reset f n base L s.occurrences.entries copies hfull hsub d.last next d.previous d.following
      ha.1 ha.2 (fun p hp=>
        let hh:=hd.previous_adjacency s capacity L hi hc d p hp
        ⟨hh.1,hh.2.1⟩)
      (fun p hp=>hd.following_adjacency s capacity L hi hc d next he p hp)

theorem Sound.next_bounds (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (d : Descriptor) (hd : Sound s capacity d)
    (f : Nat→α) (n base : Nat) (hfull : Complete f n base L s.occurrences.entries)
    (hL : 0<L) : d.last<d.nextAt n ∧ d.nextAt n≤n := by
  cases he : d.next with
  | none =>
    have hl:=((hfull d.last).mp hd.lastMember).1
    simp only [Descriptor.nextAt,he,Option.getD_none]
    omega
  | some next =>
    have ha:=hd.next_adjacency s capacity L hi d next he
    have hn:=((hfull next).mp ha.1.2.1).1
    simp only [Descriptor.nextAt,he,Option.getD_some]
    exact ⟨ha.1.2.2.1,by omega⟩

theorem Sound.point (s : MaskedClusterLeaders.State h) (capacity : Nat)
    (d : Descriptor) (hd : Sound s capacity d) (he : d.first=d.last) :
    d.period=1 ∧ d.repetitions=0 ∧ d.previous=none := by
  have hlt : ¬d.first<d.last := by omega
  have hq:=hd.period_eq s capacity d
  have hm:=hd.repetitions_eq s capacity d
  have hp:=hd.previous_eq s capacity d
  simp only [hlt,if_false] at hq hp
  rw [he,Nat.sub_self,Nat.zero_div] at hm
  exact ⟨hq,hm,hp⟩

theorem Sound.dense (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (f : Nat→α) (n base : Nat)
    (hfull : Complete f n base L s.occurrences.entries) (hlt : d.first<d.last) :
    0<d.period ∧ 0<d.repetitions ∧ 2*d.period≤L ∧
    d.last=d.first+d.repetitions*d.period ∧ LeastPeriod (shift f d.first) L d.period ∧
    ∀x,(x∈s.occurrences.entries ∧ d.first≤x ∧ x≤d.last ↔
      ∃k,k≤d.repetitions ∧ x=d.first+k*d.period) := by
  obtain ⟨u,hu,ha,hul⟩:=hd.first_successor s capacity L hi hc d hlt
  have hq : d.period=u-d.first := by
    rw [hd.period_eq s capacity d]
    simp only [hlt,if_true,hu,Option.getD_some]
  have hm:=hd.repetitions_eq s capacity d
  have hg:=component_progression f n base L s.occurrences.entries hfull d.first d.last u
    hd.firstMember hd.lastMember hlt ha hul
    (fun x hx hf hl=>hd.no_internal_leader s capacity L hi d x hx hf hl)
  simpa only [←hq,←hm] using hg

/-- The measured descriptor is exactly the closed AP of its complete
component, including the singleton period-one convention. -/
theorem Sound.progression (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (f : Nat→α) (n base : Nat)
    (hfull : Complete f n base L s.occurrences.entries) :
    0<d.period ∧ d.last=d.first+d.repetitions*d.period ∧
    ∀x,(x∈s.occurrences.entries ∧ d.first≤x ∧ x≤d.last ↔
      ∃k,k≤d.repetitions ∧ x=d.first+k*d.period) := by
  by_cases hlt : d.first<d.last
  · have hg:=hd.dense s capacity L hi hc d f n base hfull hlt
    exact ⟨hg.1,hg.2.2.2.1,hg.2.2.2.2.2⟩
  · have he : d.first=d.last := Nat.le_antisymm hd.first_le_last (by omega)
    obtain ⟨hq,hm,_⟩:=hd.point s capacity d he
    refine ⟨by omega,by simp only [hm,Nat.zero_mul,Nat.add_zero]; exact he.symm,?_⟩
    intro x
    constructor
    · rintro ⟨_,hf,hl⟩
      refine ⟨0,by omega,?_⟩
      simp only [Nat.zero_mul,Nat.add_zero]
      omega
    · rintro ⟨k,hk,hx⟩
      have hk0 : k=0 := by omega
      have hx' : x=d.first := by simpa only [hk0,Nat.zero_mul,Nat.add_zero] using hx
      rw [hx']
      exact ⟨hd.firstMember,Nat.le_refl _,hd.first_le_last⟩

theorem Sound.ap_mem (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (f : Nat→α) (n base : Nat)
    (hfull : Complete f n base L s.occurrences.entries) (k : Nat) (hk : k≤d.repetitions) :
    d.first+k*d.period∈s.occurrences.entries :=
  ((hd.progression s capacity L hi hc d f n base hfull).2.2 _ |>.mpr ⟨k,hk,rfl⟩).1

theorem describeLeader_progression (s : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : (describeLeader s capacity first).1=some d)
    (f : Nat→α) (n base : Nat) (hfull : Complete f n base L s.occurrences.entries) :
    0<d.period ∧ d.last=d.first+d.repetitions*d.period ∧
    ∀x,(x∈s.occurrences.entries ∧ d.first≤x ∧ x≤d.last ↔
      ∃k,k≤d.repetitions ∧ x=d.first+k*d.period) :=
  (describeLeader_sound s capacity L first hi hc d hd).2.progression
    s capacity L hi hc d f n base hfull

theorem Sound.dense_previous (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (f : Nat→α) (n base : Nat)
    (hfull : Complete f n base L s.occurrences.entries) (hlt : d.first<d.last) :
    d.previous=some (d.first+(d.repetitions-1)*d.period) := by
  obtain ⟨u,hu,ha,hul⟩:=hd.first_successor s capacity L hi hc d hlt
  have hq : d.period=u-d.first := by
    rw [hd.period_eq s capacity d]
    simp only [hlt,if_true,hu,Option.getD_some]
  have hg:=hd.dense s capacity L hi hc d f n base hfull hlt
  have hm:=hg.2.1
  have hend:=hg.2.2.2.1
  have hs:=Tree.pred_correct s.occurrences capacity d.last hi.occGood hi.occFits hc
  cases he : (Tree.pred s.occurrences capacity d.last).1 with
  | none =>
    rw [he] at hs
    have hh:=hs d.first hd.firstMember
    omega
  | some p =>
    have hp : d.previous=some p := by
      rw [hd.previous_eq s capacity d]
      simp only [hlt,if_true,he]
    have hb:=hd.previous_adjacency s capacity L hi hc d p hp
    have hgap:=component_gap f n base L s.occurrences.entries hfull d.first d.last u ha hul
      (fun x hx hf hl=>hd.no_internal_leader s capacity L hi d x hx hf hl)
      p d.last hb.1 hb.2.2 (Nat.le_refl _)
    rw [←hq] at hgap
    have hsplit : d.repetitions*d.period=(d.repetitions-1)*d.period+d.period := by
      calc
        d.repetitions*d.period=((d.repetitions-1)+1)*d.period := by
          congr 1
          omega
        _=(d.repetitions-1)*d.period+d.period := by rw [Nat.add_mul,Nat.one_mul]
    have hpl:=hb.1.2.2.1
    have hcoord : p=d.first+(d.repetitions-1)*d.period := by omega
    rw [hp,hcoord]

/-- All geometry consumed by the point/dense compiler, obtained from
the actual queried descriptor. The occurrence list is a proof argument;
no component membership list is materialized by the query. -/
structure Geometry (f : Nat→α) (n base L : Nat) (xs : List Nat) (d : Descriptor) : Prop where
  period_pos : 0<d.period
  endpoint : d.last=d.first+d.repetitions*d.period
  members : ∀x,(x∈xs ∧ d.first≤x ∧ x≤d.last ↔
    ∃k,k≤d.repetitions ∧ x=d.first+k*d.period)
  point : d.repetitions=0→d.first=d.last ∧ d.period=1 ∧ d.previous=none
  dense : 0<d.repetitions→2*d.period≤L ∧ LeastPeriod (shift f d.first) L d.period ∧
    d.previous=some (d.first+(d.repetitions-1)*d.period)
  next_strict : d.last<d.nextAt n
  next_bound : d.nextAt n≤n
  anchor : Certificate f n base L xs d.last (d.nextAt n) d.previous d.following L

theorem Sound.geometry (s : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : Sound s capacity d) (f : Nat→α) (n base : Nat)
    (hfull : Complete f n base L s.occurrences.entries) (hL : 0<L) :
    Geometry f n base L s.occurrences.entries d := by
  have hg:=hd.progression s capacity L hi hc d f n base hfull
  have hn:=hd.next_bounds s capacity L hi d f n base hfull hL
  refine ⟨hg.1,hg.2.1,hg.2.2,?_,?_,hn.1,hn.2,
    hd.anchor s capacity L hi hc d f n base hfull s.occurrences.entries (fun _ hk=>hk)⟩
  · intro hm
    have he : d.first=d.last := by simpa only [hm,Nat.zero_mul,Nat.add_zero] using hg.2.1.symm
    have hp:=hd.point s capacity d he
    exact ⟨he,hp.1,hp.2.2⟩
  · intro hm
    have hprod:=Nat.mul_pos hm hg.1
    have hlt : d.first<d.last := by have hh:=hg.2.1; omega
    have hh:=hd.dense s capacity L hi hc d f n base hfull hlt
    exact ⟨hh.2.2.1,hh.2.2.2.2.1,hd.dense_previous s capacity L hi hc d f n base hfull hlt⟩

theorem describeLeader_geometry (s : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : (describeLeader s capacity first).1=some d)
    (f : Nat→α) (n base : Nat) (hfull : Complete f n base L s.occurrences.entries) (hL : 0<L) :
    Geometry f n base L s.occurrences.entries d :=
  (describeLeader_sound s capacity L first hi hc d hd).2.geometry
    s capacity L hi hc d f n base hfull hL

theorem describe_geometry (s : MaskedClusterLeaders.State h) (capacity L p : Nat)
    (hi : MaskedClusterLeaders.Invariant L s) (hc : capacity=2^h)
    (d : Descriptor) (hd : (describe s capacity p).1=some d)
    (f : Nat→α) (n base : Nat) (hfull : Complete f n base L s.occurrences.entries) (hL : 0<L) :
    Geometry f n base L s.occurrences.entries d :=
  (describe_sound s capacity L p hi hc d hd).1.geometry
    s capacity L hi hc d f n base hfull hL

end REWB.MaskedClusterDescriptor
