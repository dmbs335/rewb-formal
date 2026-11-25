import REWB.BoundaryBorderWindow

/-! Exact geometry of the occurrence components returned by the
constant-query window extractor. Completeness is needed to identify the
least period from true adjacency. It is supplied by the retained suffix
class wrapper, not reconstructed by scanning occurrences. -/
namespace REWB.BoundaryBorder.Window
open REWB.Periodic REWB.RunGeometry REWB.MaskedRunDiscovery REWB.MaskedOrdered REWB.LCEIndex
variable {α : Type} {σ h : Nat}

theorem rounded_spec (first cap q : Nat) (hf : first≤cap) (hq : 0<q) :
    first≤rounded first cap q ∧ rounded first cap q≤cap ∧
    cap<rounded first cap q+q ∧ (rounded first cap q-first)%q=0 := by
  have hr:=Nat.mod_add_div (cap-first) q
  have hm:=Nat.mod_lt (cap-first) hq
  rw [Nat.mul_comm q ((cap-first)/q)] at hr
  refine ⟨by unfold rounded; omega,by unfold rounded; omega,
    by unfold rounded; omega,?_⟩
  simp only [rounded,Nat.add_sub_cancel_left,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod]

theorem prefix_least (f : Nat→α) (n first L q extent : Nat)
    (hp : PeriodPrefix f n first q extent) (hm : LeastPeriod (shift f first) L q)
    (hL : L≤extent) : LeastPeriod (shift f first) extent q := by
  refine ⟨hm.1,hp.periodic,?_⟩
  intro r hr hR
  exact hm.2.2 r hr (restrict hR hL)

/-- A least-period prefix contains exactly one phase of this occurrence
class. Both directions concern every physical position, not just already
enumerated progression members. -/
theorem prefix_grid (f : Nat→α) (n base L first q extent : Nat) (xs : List Nat)
    (hfull : Complete f n base L xs) (hf : first∈xs)
    (hp : PeriodPrefix f n first q extent) (hm : LeastPeriod (shift f first) L q)
    (hL : L≤extent) (hqL : q≤L) (p : Nat) (hfp : first≤p) (hpr : p+L≤first+extent) :
    p∈xs ↔ (p-first)%q=0 := by
  have hmin:=prefix_least f n first L q extent hp hm hL
  constructor
  · intro hmem
    have heq:=((hfull first).mp hf).2.trans ((hfull p).mp hmem).2.symm
    have he : ∀i,i<L→shift f first (0+i)=shift f first (p-first+i) := by
      intro i hi
      have hh:=(segment_eq_points f first p L).mp heq i hi
      simpa only [shift,Nat.zero_add,show first+(p-first+i)=p+i by omega] using hh
    have hd:=equal_long_factor_same_phase hmin (Nat.zero_le (p-first))
      (show p-first+L≤extent by omega) hqL he
    simpa only [Nat.sub_zero] using Nat.mod_eq_zero_of_dvd hd
  · intro hmod
    apply (hfull p).mpr
    refine ⟨by have hb:=hp.bounded; omega,?_⟩
    apply Eq.trans ?_ ((hfull first).mp hf).2
    apply (segment_eq_points f p first L).mpr
    intro i hi
    have hpi:=period_residue hp.periodic (p-first+i) (by omega)
    have hfi:=period_residue hp.periodic i (by omega)
    have he : (p-first+i)%q=i%q := by
      simp only [Nat.add_mod,hmod,Nat.zero_add,Nat.mod_mod]
    change f (first+(p-first+i))=f (first+((p-first+i)%q)) at hpi
    change f (first+i)=f (first+i%q) at hfi
    rw [show first+(p-first+i)=p+i by omega,he] at hpi
    exact hpi.trans hfi.symm

theorem dense_extent (f : Nat→α) (n base L first u extent : Nat) (xs : List Nat)
    (hfull : Complete f n base L xs) (ha : Adjacent xs first u) (hd : 2*(u-first)≤L)
    (hp : PeriodPrefix f n first (u-first) extent) :
    LeastPeriod (shift f first) L (u-first) ∧ L+(u-first)≤extent := by
  have hfu:=ha.2.2.1
  have hc:=complete_consecutive f n base L xs first u hfull ha
  have hm:=dense_least (shift f first) L (u-first) (by omega) hd hc
  have hu:=((hfull u).mp ha.2.1).1
  exact ⟨hm,hp.longest (L+(u-first)) (by omega) (overlap_period _ _ _ hc.1)⟩

/-- A dense adjacency after the rounded endpoint would extend the same
periodic prefix, contradicting either its measured maximality or the
window cutoff. -/
theorem dense_exit (f : Nat→α) (n base L first u extent hi : Nat) (xs : List Nat)
    (hfull : Complete f n base L xs) (ha : Adjacent xs first u) (hd : 2*(u-first)≤L)
    (hp : PeriodPrefix f n first (u-first) extent) (hhi : first≤hi)
    (x : Nat) (hx : Adjacent xs (rounded first (min hi (first+extent-L)) (u-first)) x)
    (hxh : x≤hi) :
    L<2*(x-rounded first (min hi (first+extent-L)) (u-first)) := by
  have hfu:=ha.2.2.1
  have hg:=dense_extent f n base L first u extent xs hfull ha hd hp
  have hsize:=hg.2
  have hcap : first≤min hi (first+extent-L) := Nat.le_min.mpr ⟨hhi,by omega⟩
  have hr:=rounded_spec first (min hi (first+extent-L)) (u-first) hcap (by omega)
  have hlast : rounded first (min hi (first+extent-L)) (u-first)+L≤first+extent := by
    have hb:=Nat.le_trans hr.2.1 (Nat.min_le_right hi (first+extent-L))
    omega
  by_cases hsmall : 2*(x-rounded first (min hi (first+extent-L)) (u-first))≤L
  · have hm:=MaskedLocalAnchor.complete_least f n base L xs hfull first u
      (rounded first (min hi (first+extent-L)) (u-first)) ha hd hx.1
    have hgap:=dense_consecutive_gap (by have hh:=hx.2.2.1; omega) hsmall
      (complete_consecutive f n base L xs _ x hfull hx) hm
    have hmove:=prefix_move f n first (u-first) extent
      (rounded first (min hi (first+extent-L)) (u-first)) hp (by omega) hr.1 (by omega)
    have hc:=complete_consecutive f n base L xs _ x hfull hx
    rw [hgap] at hc
    have hxb:=((hfull x).mp hx.2.1).1
    have hlong:=hmove.longest (L+(u-first)) (by omega) (overlap_period _ _ _ hc.1)
    have hxcap : x≤min hi (first+extent-L) := Nat.le_min.mpr ⟨hxh,by omega⟩
    have hlt:=hr.2.2.1
    have hxl:=hx.2.2.1
    omega
  · omega

structure Valid (f : Nat→Fin σ) (n L hi : Nat) (xs : List Nat) (b : Band) : Prop where
  first_mem : b.first∈xs
  last_mem : b.last∈xs
  ordered : b.first≤b.last
  upper : b.last≤hi
  positive : 0<b.step
  step_le : b.step≤L
  members : ∀p,b.Holds p ↔ p∈xs ∧ b.first≤p ∧ p≤b.last
  after : ∀p,p∈xs→b.last<p→p≤hi→L<2*(p-b.last)
  span : b.last+b.step≤b.first+(extend (prepare f n) n b.first b.step).extent

theorem point_valid (f : Nat→Fin σ) (n L hi first : Nat) (xs : List Nat)
    (hL : 0<L) (hf : first∈xs) (hhi : first≤hi)
    (ha : ∀p,p∈xs→first<p→p≤hi→L<2*(p-first)) :
    Valid f n L hi xs ⟨first,first,1⟩ := by
  refine ⟨hf,hf,Nat.le_refl _,hhi,by change 0<1; decide,by change 1≤L; omega,?_,ha,?_⟩
  · intro p
    change (first≤p ∧ p≤first ∧ first≤p ∧ (p-first)%1=0) ↔ p∈xs ∧ first≤p ∧ p≤first
    constructor
    · rintro ⟨hfp,hpf,_,_⟩
      have he : p=first := by omega
      exact ⟨he.symm ▸ hf,hfp,hpf⟩
    · rintro ⟨_,hfp,hpf⟩
      exact ⟨hfp,hpf,hfp,Nat.mod_one _⟩
  · change first+1≤first+(1+_)
    omega

theorem dense_valid (f : Nat→Fin σ) (n base L first u hi : Nat) (t : Tree h) (capacity : Nat)
    (hg : Tree.Good t) (ht : Tree.Fits t 0) (hc : capacity=2^h)
    (hfull : Complete f n base L t.entries) (ha : Adjacent t.entries first u)
    (hd : 2*(u-first)≤L) (hhi : first≤hi) :
    Valid f n L hi t.entries
      ⟨first,rounded first (min hi (first+(extend (prepare f n) n first (u-first)).extent-L)) (u-first),u-first⟩ := by
  let extent:=(extend (prepare f n) n first (u-first)).extent
  let last:=rounded first (min hi (first+extent-L)) (u-first)
  have hfu:=ha.2.2.1
  have hfb:=((hfull first).mp ha.1).1
  have hp:=extend_correct f n first (u-first) (by omega)
  have hgeom:=dense_extent f n base L first u extent t.entries hfull ha hd hp
  have hsize:=hgeom.2
  have hcap : first≤min hi (first+extent-L) := Nat.le_min.mpr ⟨hhi,by omega⟩
  have hr:=rounded_spec first (min hi (first+extent-L)) (u-first) hcap (by omega)
  have hlast : last+L≤first+extent := by
    have hb:=Nat.le_trans hr.2.1 (Nat.min_le_right hi (first+extent-L))
    change rounded first (min hi (first+extent-L)) (u-first)+L≤first+extent
    omega
  have hm:=prefix_grid f n base L first (u-first) extent t.entries hfull ha.1 hp hgeom.1
    (by omega) (by omega)
  have hlmem : last∈t.entries := (hm last hr.1 hlast).mpr hr.2.2.2
  change Valid f n L hi t.entries ⟨first,last,u-first⟩
  refine ⟨ha.1,hlmem,hr.1,Nat.le_trans hr.2.1 (Nat.min_le_left _ _),
    by change 0<u-first; omega,by change u-first≤L; omega,?_,?_,?_⟩
  · intro p
    change (first≤p ∧ p≤last ∧ first≤p ∧ (p-first)%(u-first)=0) ↔
      p∈t.entries ∧ first≤p ∧ p≤last
    constructor
    · rintro ⟨hfp,hpl,_,hmod⟩
      exact ⟨(hm p hfp (by omega)).mpr hmod,hfp,hpl⟩
    · rintro ⟨hmem,hfp,hpl⟩
      exact ⟨hfp,hpl,hfp,(hm p hfp (by omega)).mp hmem⟩
  · intro p hmem hlp hphi
    change last<p at hlp
    change L<2*(p-last)
    have hs:=Tree.succ_correct t capacity last hg ht hc
    cases he : (Tree.succ t capacity last).1 with
    | none =>
      rw [he] at hs
      have hh:=hs p hmem
      omega
    | some x =>
      rw [he] at hs
      have hxp:=hs.2.2 p hmem hlp
      have hax : Adjacent t.entries last x := by
        refine ⟨hlmem,hs.1,hs.2.1,?_⟩
        intro y hy hly hyx
        have hh:=hs.2.2 y hy hly
        omega
      have hx:=dense_exit f n base L first u extent hi t.entries hfull ha hd hp hhi
        x hax (by omega)
      change L<2*(x-last) at hx
      omega
  · change last+(u-first)≤first+extent
    omega

theorem component_correct (f : Nat→Fin σ) (n base L hi first : Nat) (t : Tree h) (capacity : Nat)
    (hg : Tree.Good t) (ht : Tree.Fits t 0) (hc : capacity=2^h)
    (hfull : Complete f n base L t.entries) (hL : 0<L) (hf : first∈t.entries) (hhi : first≤hi) :
    (component (prepare f n) t capacity n L hi first).1.first=first ∧
      Valid f n L hi t.entries (component (prepare f n) t capacity n L hi first).1 := by
  have hs:=Tree.succ_correct t capacity first hg ht hc
  cases he : (Tree.succ t capacity first).1 with
  | none =>
    rw [he] at hs
    simp only [component,he]
    refine ⟨True.intro,point_valid f n L hi first t.entries hL hf hhi ?_⟩
    intro p hp hfp _
    have hh:=hs p hp
    omega
  | some u =>
    rw [he] at hs
    have ha : Adjacent t.entries first u := by
      refine ⟨hf,hs.1,hs.2.1,?_⟩
      intro x hx hfx hxu
      have hh:=hs.2.2 x hx hfx
      omega
    by_cases hd : first<u ∧ u≤hi ∧ 2*(u-first)≤L
    · simp only [component,he,if_pos hd]
      exact ⟨True.intro,dense_valid f n base L first u hi t capacity hg ht hc hfull ha hd.2.2 hhi⟩
    · simp only [component,he,if_neg hd]
      refine ⟨True.intro,point_valid f n L hi first t.entries hL hf hhi ?_⟩
      intro p hp hfp hphi
      have hup:=hs.2.2 p hp hfp
      have hnot : ¬2*(u-first)≤L := fun hh=>hd ⟨hs.2.1,by omega,hh⟩
      omega

theorem interval_none_forbids (t : Tree h) (capacity lo hi : Nat)
    (hg : Tree.Good t) (ht : Tree.Fits t 0) (hc : capacity=2^h)
    (hn : (Tree.interval t capacity lo hi).1=none) (p : Nat) :
    ¬(p∈t.entries ∧ lo≤p ∧ p≤hi) := by
  intro hp
  obtain ⟨x,hx⟩:=(Tree.interval_exists t capacity lo hi hg ht hc).mpr ⟨p,hp⟩
  rw [hn] at hx
  cases hx

theorem extract_valid (f : Nat→Fin σ) (n base L lo hi : Nat) (t : Tree h) (capacity : Nat)
    (hg : Tree.Good t) (ht : Tree.Fits t 0) (hc : capacity=2^h)
    (hfull : Complete f n base L t.entries) (hL : 0<L) (b : Band)
    (hb : (extract (prepare f n) t capacity n L lo hi).first=some b ∨
      (extract (prepare f n) t capacity n L lo hi).second=some b) :
    Valid f n L hi t.entries b ∧ lo≤b.first := by
  cases he : (Tree.interval t capacity lo hi).1 with
  | none =>
    simp only [extract,he,reduceCtorEq] at hb
    rcases hb with hh|hh <;> cases hh
  | some first =>
    have hf:=Tree.interval_some t capacity lo hi first hg ht hc he
    have hl:=component_correct f n base L hi first t capacity hg ht hc hfull hL hf.1 hf.2.2.1
    cases hn : (Tree.interval t capacity ((component (prepare f n) t capacity n L hi first).1.last+1) hi).1 with
    | none =>
      simp only [extract,he,hn,Option.some.injEq,reduceCtorEq,or_false] at hb
      rw [←hb]
      exact ⟨hl.2,by rw [hl.1]; exact hf.2.1⟩
    | some next =>
      have hnext:=Tree.interval_some t capacity _ hi next hg ht hc hn
      have hr:=component_correct f n base L hi next t capacity hg ht hc hfull hL hnext.1 hnext.2.2.1
      simp only [extract,he,hn,Option.some.injEq] at hb
      rcases hb with hb|hb
      · rw [←hb]
        exact ⟨hl.2,by rw [hl.1]; exact hf.2.1⟩
      · rw [←hb]
        refine ⟨hr.2,?_⟩
        rw [hr.1]
        have ho:=hl.2.ordered
        have heq:=hl.1
        have hflo:=hf.2.1
        have hnl:=hnext.2.1
        omega

/-- At most two measured components cover the entire short window.
The return value is exact at every physical position, including gaps
between adjacent AP members and empty/reversed windows. -/
theorem extract_correct (f : Nat→Fin σ) (n base L lo hi : Nat) (t : Tree h) (capacity : Nat)
    (hg : Tree.Good t) (ht : Tree.Fits t 0) (hc : capacity=2^h)
    (hfull : Complete f n base L t.entries) (hwidth : hi-lo<L) (p : Nat) :
    (extract (prepare f n) t capacity n L lo hi).Holds p ↔ p∈t.entries ∧ lo≤p ∧ p≤hi := by
  have hL : 0<L := by omega
  constructor
  · rintro (⟨b,hb,hp⟩|⟨b,hb,hp⟩)
    · obtain ⟨hv,hlo⟩:=extract_valid f n base L lo hi t capacity hg ht hc hfull hL b (Or.inl hb)
      have hh:=(hv.members p).mp hp
      exact ⟨hh.1,Nat.le_trans hlo hh.2.1,Nat.le_trans hh.2.2 hv.upper⟩
    · obtain ⟨hv,hlo⟩:=extract_valid f n base L lo hi t capacity hg ht hc hfull hL b (Or.inr hb)
      have hh:=(hv.members p).mp hp
      exact ⟨hh.1,Nat.le_trans hlo hh.2.1,Nat.le_trans hh.2.2 hv.upper⟩
  · rintro ⟨hp,hlo,hhi⟩
    cases he : (Tree.interval t capacity lo hi).1 with
    | none => exact False.elim (interval_none_forbids t capacity lo hi hg ht hc he p ⟨hp,hlo,hhi⟩)
    | some first =>
      have hf:=Tree.interval_some t capacity lo hi first hg ht hc he
      have hl:=component_correct f n base L hi first t capacity hg ht hc hfull hL hf.1 hf.2.2.1
      have hfirst : (component (prepare f n) t capacity n L hi first).1.first≤p := by
        rw [hl.1]
        exact hf.2.2.2 p hp hlo
      cases hn : (Tree.interval t capacity ((component (prepare f n) t capacity n L hi first).1.last+1) hi).1 with
      | none =>
        have hlast : p≤(component (prepare f n) t capacity n L hi first).1.last := by
          by_cases hh : p≤(component (prepare f n) t capacity n L hi first).1.last
          · exact hh
          · exact False.elim (interval_none_forbids t capacity _ hi hg ht hc hn p ⟨hp,by omega,hhi⟩)
        exact Or.inl ⟨_,by simp only [extract,he,hn],(hl.2.members p).mpr ⟨hp,hfirst,hlast⟩⟩
      | some next =>
        have hnext:=Tree.interval_some t capacity _ hi next hg ht hc hn
        have hr:=component_correct f n base L hi next t capacity hg ht hc hfull hL hnext.1 hnext.2.2.1
        by_cases hleft : p≤(component (prepare f n) t capacity n L hi first).1.last
        · exact Or.inl ⟨_,by simp only [extract,he,hn],(hl.2.members p).mpr ⟨hp,hfirst,hleft⟩⟩
        · have hsecond : (component (prepare f n) t capacity n L hi next).1.first≤p := by
            rw [hr.1]
            exact hnext.2.2.2 p hp (by omega)
          by_cases hright : p≤(component (prepare f n) t capacity n L hi next).1.last
          · exact Or.inr ⟨_,by simp only [extract,he,hn],(hr.2.members p).mpr ⟨hp,hsecond,hright⟩⟩
          · have hgap1:=hl.2.after next hnext.1 (by have hh:=hnext.2.1; omega) hnext.2.2.1
            have hgap2:=hr.2.after p hp (by omega) hhi
            have horder1:=hl.2.ordered
            have horder2:=hr.2.ordered
            have hfirstEq:=hl.1
            have hnextEq:=hr.1
            have hfirstLo:=hf.2.1
            omega

end REWB.BoundaryBorder.Window
