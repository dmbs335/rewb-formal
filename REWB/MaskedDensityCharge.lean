import REWB.MaskedOrderedOwnerQualified
import REWB.MaskedLocalAnchor
import REWB.RunBudget

/-! Structural uniqueness for density-reset charges. IDs are the actual
preorder addresses used by `MaskedOrdered.Owner.visit`. A charge must
belong to the first threshold locus at depth `2*q`; equal-depth binary
refinements below that locus are excluded. This module does not assert
that a dynamic repair scheduler has emitted or deduplicated the charges. -/
namespace REWB.MaskedDensityCharge
open REWB.BoundaryTrie
open REWB.MaskedRunDiscovery
open REWB.MaskedOrdered.Owner
variable {n σ : Nat}

theorem locus_position {t u : Tree n Nat} {depth : Nat} (hl : Tree.Locus t depth u)
    (p : Nat) (hp : p∈positions u) : p∈positions t := by
  obtain ⟨a,ha,he⟩:=List.mem_map.mp hp
  exact List.mem_map.mpr ⟨a,Tree.locus_mem hl a ha,he⟩

theorem location_position {t u : Tree n Nat} {parent pu : Option Parent} {base id : Nat}
    (hl : Location t parent base u pu id) (p : Nat) (hp : p∈positions u) : p∈positions t := by
  obtain ⟨a,ha,he⟩:=List.mem_map.mp hp
  exact List.mem_map.mpr ⟨a,location_mem hl a ha,he⟩

theorem positions_split (stem : Key n Nat) (depth : Nat) (l r : Tree n Nat)
    (hn : (positions (.node stem depth l r)).Nodup) :
    (positions l).Nodup ∧ (positions r).Nodup ∧
      ∀p,p∈positions l→p∈positions r→False := by
  have hh : (positions l++positions r).Nodup := by
    simpa only [positions,Tree.leaves,List.map_append] using hn
  have hd:=List.pairwise_append.mp hh
  exact ⟨hd.1,hd.2.1,fun p hl hr=>hd.2.2 p hl p hr rfl⟩

/-- Two first-threshold classes containing the same actual suffix
position are the same subtree. Duplicate binary refinements cannot
satisfy the first-threshold relation at their parent's depth. -/
theorem locus_unique {t u v : Tree n Nat} {depth p : Nat}
    (hn : (positions t).Nodup) (hu : Tree.Locus t depth u) (hv : Tree.Locus t depth v)
    (hpu : p∈positions u) (hpv : p∈positions v) : u=v := by
  induction hu generalizing v with
  | here t hd => exact (Tree.locus_first hd hv).symm
  | @left stem d l r depth u hd hu ih =>
    have hs:=positions_split stem d l r hn
    cases hv with
    | here _ hdepth => change depth≤d at hdepth; omega
    | left _ hv => exact ih hs.1 hv hpu hpv
    | right _ hv => exact False.elim (hs.2.2 p (locus_position hu p hpu) (locus_position hv p hpv))
  | @right stem d l r depth u hd hu ih =>
    have hs:=positions_split stem d l r hn
    cases hv with
    | here _ hdepth => change depth≤d at hdepth; omega
    | left _ hv => exact False.elim (hs.2.2 p (locus_position hv p hpv) (locus_position hu p hpu))
    | right _ hv => exact ih hs.2.1 hv hpu hpv

theorem location_span {t u : Tree n Nat} {parent pu : Option Parent} {base id : Nat}
    (hl : Location t parent base u pu id) : base≤id ∧ id+slots u≤base+slots t := by
  induction hl with
  | here t parent base => exact ⟨Nat.le_refl _,Nat.le_refl _⟩
  | @left stem d l r parent base u pu id hh ih => simp only [slots]; omega
  | @right stem d l r parent base u pu id hh ih => simp only [slots]; omega

/-- Actual preorder IDs uniquely determine both the subtree and the
propagated parent metadata, without an external node-ID map. -/
theorem location_id {t u v : Tree n Nat} {parent pu pv : Option Parent} {base id : Nat}
    (hu : Location t parent base u pu id) (hv : Location t parent base v pv id) : u=v ∧ pu=pv := by
  induction hu with
  | here t parent base =>
    cases hv with
    | here => exact ⟨rfl,rfl⟩
    | left hh => have hb:=(location_bounds hh).1; omega
    | right hh => have hb:=(location_bounds hh).1; omega
  | @left stem d l r parent base u pu id hu ih =>
    cases hv with
    | here => have hb:=(location_bounds hu).1; omega
    | left hv => exact ih hv
    | right hv =>
      have hlu:=(location_bounds hu).2
      have hrv:=(location_bounds hv).1
      omega
  | @right stem d l r parent base u pu id hu ih =>
    cases hv with
    | here => have hb:=(location_bounds hu).1; omega
    | left hv =>
      have hru:=(location_bounds hu).1
      have hlv:=(location_bounds hv).2
      omega
    | right hv => exact ih hv

theorem location_unique {t u : Tree n Nat} {parent pu pv : Option Parent} {base i j p : Nat}
    (hn : (positions t).Nodup) (hu : Location t parent base u pu i) (hv : Location t parent base u pv j)
    (hp : p∈positions u) : i=j := by
  induction hu generalizing pv j with
  | here t parent base =>
    have hh:=location_span hv
    omega
  | @left stem d l r parent base u pu i hu ih =>
    have hs:=positions_split stem d l r hn
    cases hv with
    | here =>
      have hspan:=location_span hu
      have hpos:=slots_pos r
      simp only [slots] at hspan
      omega
    | left hv => exact ih hs.1 hv hp
    | right hv => exact False.elim (hs.2.2 p (location_position hu p hp) (location_position hv p hp))
  | @right stem d l r parent base u pu i hu ih =>
    have hs:=positions_split stem d l r hn
    cases hv with
    | here =>
      have hspan:=location_span hu
      have hpos:=slots_pos l
      simp only [slots] at hspan
      omega
    | left hv => exact False.elim (hs.2.2 p (location_position hv p hp) (location_position hu p hp))
    | right hv => exact ih hs.2.1 hv hp

theorem locus_id_unique {t u v : Tree n Nat} {parent pu pv : Option Parent} {base i j depth p : Nat}
    (hn : (positions t).Nodup) (hu : Location t parent base u pu i) (hv : Location t parent base v pv j)
    (hlu : Tree.Locus t depth u) (hlv : Tree.Locus t depth v)
    (hpu : p∈positions u) (hpv : p∈positions v) : i=j := by
  have he:=locus_unique hn hlu hlv hpu hpv
  subst v
  exact location_unique hn hu hv hpu

def Below (parent : Option Parent) (depth : Nat) : Prop :=
  ∀p,parent=some p→p.depth<depth

theorem locus_location {t u : Tree n Nat} {depth : Nat} (hl : Tree.Locus t depth u)
    (parent : Option Parent) (base : Nat) (hb : Below parent depth) :
    ∃pu id,Location t parent base u pu id ∧ Below pu depth := by
  induction hl generalizing parent base with
  | here t hd => exact ⟨parent,base,.here _ _ _,hb⟩
  | @left stem d l r depth u hd hl ih =>
    have hb' : Below (some ⟨d,select parent d base⟩) depth := by
      intro p hp; cases hp; exact hd
    obtain ⟨pu,id,hi,hp⟩:=ih (some ⟨d,select parent d base⟩) (base+1) hb'
    exact ⟨pu,id,.left hi,hp⟩
  | @right stem d l r depth u hd hl ih =>
    have hb' : Below (some ⟨d,select parent d base⟩) depth := by
      intro p hp; cases hp; exact hd
    obtain ⟨pu,id,hi,hp⟩:=ih (some ⟨d,select parent d base⟩) (base+1+slots l) hb'
    exact ⟨pu,id,.right hi,hp⟩

/-- The parent bound follows from first-threshold qualification at the
actual occurrence. It excludes lower refinements even when depths tie. -/
theorem locus_parent {t u : Tree n Nat} {pu : Option Parent} {base id depth p : Nat}
    (hn : (positions t).Nodup) (hl : Location t none base u pu id)
    (hc : Tree.Locus t depth u) (hp : p∈positions u) : Below pu depth ∧ depth≤u.depth := by
  obtain ⟨pv,j,hv,hbelow⟩:=locus_location hc none base (by intro p hp; cases hp)
  have hij:=location_unique hn hl hv hp
  subst j
  have hparent:=(location_id hl hv).2
  exact ⟨hparent ▸ hbelow,Tree.locus_depth hc⟩

structure Charge where
  node : Nat
  start : Nat
  period : Nat
  deriving Repr,DecidableEq

def Charge.key (c : Charge) : RunBudget.Key := (c.start,c.period)

def At (t : Tree n Nat) (c : Charge) : Prop :=
  ∃u parent,Location t none 0 u parent c.node ∧ Tree.Locus t (2*c.period) u ∧ c.start∈positions u

theorem at_injective (t : Tree n Nat) (hn : (positions t).Nodup) (a b : Charge)
    (ha : At t a) (hb : At t b) (hkey : a.key=b.key) : a=b := by
  have hs : a.start=b.start := congrArg Prod.fst hkey
  have hq : a.period=b.period := congrArg Prod.snd hkey
  obtain ⟨u,pu,hlu,hcu,hau⟩:=ha
  obtain ⟨v,pv,hlv,hcv,hbv⟩:=hb
  have hnode : a.node=b.node := by
    apply locus_id_unique hn hlu hlv hcu
    · simpa only [hq] using hcv
    · exact hau
    · rwa [hs]
  cases a
  cases b
  simp only [Charge.mk.injEq]
  exact ⟨hnode,hs,hq⟩

theorem at_parent (t : Tree n Nat) (hn : (positions t).Nodup) (c : Charge) (hc : At t c) :
    ∃u parent,Location t none 0 u parent c.node ∧ Tree.Locus t (2*c.period) u ∧
      c.start∈positions u ∧ Below parent (2*c.period) ∧ 2*c.period≤u.depth := by
  obtain ⟨u,parent,hl,hcut,hmem⟩:=hc
  have hb:=locus_parent hn hl hcut hmem
  exact ⟨u,parent,hl,hcut,hmem,hb.1,hb.2⟩

end REWB.MaskedDensityCharge
