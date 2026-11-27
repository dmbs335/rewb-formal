import REWB.MaskedOrderedOwnerSnapshot

/-! Owner pointers select the first node of an equal-depth class.
The inherited case is explicit, so a lower binary refinement cannot be
mistaken for a completed occurrence class. -/
namespace REWB.MaskedOrdered.Owner
variable {n σ : Nat}

def ParentLe (parent : Option Parent) (d : Nat) : Prop :=
  match parent with
  | none => True
  | some p => p.depth≤d

def Inherited (parent : Option Parent) (H owner : Nat) : Prop :=
  ∃p,parent=some p ∧ p.depth=H ∧ p.owner=owner

def Inside (t : Trie n Nat) (parent : Option Parent) (base H owner : Nat) (target : Trie n Nat) : Prop :=
  ∃v pv,Location t parent base v pv owner ∧ v.depth=H ∧
    select pv H owner=owner ∧ BoundaryTrie.Tree.Locus t H v ∧
    (∀p,parent=some p→p.depth<H) ∧ (∀a,a∈target.leaves→a∈v.leaves)

theorem location_mem {t u : Trie n Nat} {parent pu : Option Parent} {base id : Nat}
    (hl : Location t parent base u pu id) : ∀a,a∈u.leaves→a∈t.leaves := by
  induction hl with
  | here => exact fun _ ha=>ha
  | left _ ih => exact fun a ha=>List.mem_append_left _ (ih a ha)
  | right _ ih => exact fun a ha=>List.mem_append_right _ (ih a ha)

theorem root_owner (t : Trie n Nat) (parent : Option Parent) (base : Nat)
    (hp : ParentLe parent t.depth) :
    Inherited parent t.depth (select parent t.depth base) ∨
      Inside t parent base t.depth (select parent t.depth base) t := by
  cases parent with
  | none =>
    exact Or.inr ⟨t,none,.here _ _ _,rfl,rfl,.here _ (Nat.le_refl _),
      (by intro p he; cases he),fun _ ha=>ha⟩
  | some p =>
    by_cases hd : p.depth<t.depth
    · simp only [select,hd,if_true]
      exact Or.inr ⟨t,some p,.here _ _ _,rfl,by simp [select,hd],
        .here _ (Nat.le_refl _),(by intro q he; cases he; exact hd),fun _ ha=>ha⟩
    · have he : p.depth=t.depth := by change p.depth≤t.depth at hp; omega
      apply Or.inl
      exact ⟨p,rfl,he,by simp [select,hd]⟩

theorem location_owner_cases (f : Nat→Fin σ) {t u : Trie n Nat}
    {parent pu : Option Parent} {base id : Nat}
    (hl : Location t parent base u pu id) (hg : t.Good f) (hp : ParentLe parent t.depth) :
    Inherited parent u.depth (select pu u.depth id) ∨
      Inside t parent base u.depth (select pu u.depth id) u := by
  induction hl with
  | here t parent base => exact root_owner t parent base hp
  | @left stem d l r parent base u pu id hh ih =>
    have hdepth:=(BoundaryTrie.Tree.edge_depths f stem d l r hg).1
    have hv:=ih hg.1 hdepth
    rcases hv with hv|hv
    · obtain ⟨p,hp',hd,ho⟩:=hv
      cases hp'
      have hr:=root_owner (.node stem d l r) parent base hp
      change d=u.depth at hd
      change select parent d base=select pu u.depth id at ho
      rw [←ho,←hd]
      rcases hr with hr|hr
      · exact Or.inl hr
      · obtain ⟨v,pv,hlv,hdv,hov,hc,hs,hm⟩:=hr
        exact Or.inr ⟨v,pv,hlv,hdv,hov,hc,hs,
          fun a ha=>hm a (location_mem (.left hh) a ha)⟩
    · obtain ⟨v,pv,hlv,hd,ho,hlocus,hstrict,hmem⟩:=hv
      have hdu:=hstrict _ rfl
      change d<u.depth at hdu
      refine Or.inr ⟨v,pv,.left hlv,hd,ho,.left hdu hlocus,?_,hmem⟩
      intro p he
      rw [he] at hp
      change p.depth≤d at hp
      omega
  | @right stem d l r parent base u pu id hh ih =>
    have hdepth:=(BoundaryTrie.Tree.edge_depths f stem d l r hg).2
    have hv:=ih hg.2.1 hdepth
    rcases hv with hv|hv
    · obtain ⟨p,hp',hd,ho⟩:=hv
      cases hp'
      have hr:=root_owner (.node stem d l r) parent base hp
      change d=u.depth at hd
      change select parent d base=select pu u.depth id at ho
      rw [←ho,←hd]
      rcases hr with hr|hr
      · exact Or.inl hr
      · obtain ⟨v,pv,hlv,hdv,hov,hc,hs,hm⟩:=hr
        exact Or.inr ⟨v,pv,hlv,hdv,hov,hc,hs,
          fun a ha=>hm a (location_mem (.right hh) a ha)⟩
    · obtain ⟨v,pv,hlv,hd,ho,hlocus,hstrict,hmem⟩:=hv
      have hdu:=hstrict _ rfl
      change d<u.depth at hdu
      refine Or.inr ⟨v,pv,.right hlv,hd,ho,.right hdu hlocus,?_,hmem⟩
      intro p he
      rw [he] at hp
      change p.depth≤d at hp
      omega

/-- The propagated ID resolves to an actual stored node at the same
depth, with a self owner and a qualified complete-class locus. -/
theorem location_owner (f : Nat→Fin σ) {t u : Trie n Nat} {pu : Option Parent} {base id : Nat}
    (hg : t.Good f) (hl : Location t none base u pu id) :
    ∃v pv,Location t none base v pv (select pu u.depth id) ∧
      v.depth=u.depth ∧ select pv v.depth (select pu u.depth id)=select pu u.depth id ∧
      BoundaryTrie.Tree.Locus t u.depth v := by
  rcases location_owner_cases f hl hg True.intro with hh|hh
  · obtain ⟨p,hp,_,_⟩:=hh
    cases hp
  · obtain ⟨v,pv,hlv,hd,ho,hc,_⟩:=hh
    exact ⟨v,pv,hlv,hd,by simpa only [hd] using ho,hc⟩

theorem location_owner_mem (f : Nat→Fin σ) {t u : Trie n Nat} {pu : Option Parent} {base id : Nat}
    (hg : t.Good f) (hl : Location t none base u pu id) :
    ∃v pv,Location t none base v pv (select pu u.depth id) ∧
      v.depth=u.depth ∧ select pv v.depth (select pu u.depth id)=select pu u.depth id ∧
      BoundaryTrie.Tree.Locus t u.depth v ∧ (∀a,a∈u.leaves→a∈v.leaves) := by
  rcases location_owner_cases f hl hg True.intro with hh|hh
  · obtain ⟨p,hp,_,_⟩:=hh
    cases hp
  · obtain ⟨v,pv,hlv,hd,ho,hc,_,hm⟩:=hh
    exact ⟨v,pv,hlv,hd,by simpa only [hd] using ho,hc,hm⟩

theorem location_of_range (t : Trie n Nat) (parent : Option Parent) (base id : Nat)
    (hlo : base≤id) (hhi : id<base+slots t) :
    ∃u pu,Location t parent base u pu id := by
  induction t generalizing parent base with
  | empty =>
    have he : id=base := by simp only [slots] at hhi; omega
    subst id
    exact ⟨_,_,.here _ _ _⟩
  | leaf a =>
    have he : id=base := by simp only [slots] at hhi; omega
    subst id
    exact ⟨_,_,.here _ _ _⟩
  | node stem d l r il ir =>
    by_cases he : id=base
    · subst id
      exact ⟨_,_,.here _ _ _⟩
    · by_cases hleft : id<base+1+slots l
      · obtain ⟨u,pu,hh⟩:=il (some ⟨d,select parent d base⟩) (base+1) (by omega) hleft
        exact ⟨u,pu,.left hh⟩
      · obtain ⟨u,pu,hh⟩:=ir (some ⟨d,select parent d base⟩) (base+1+slots l) (by omega)
          (by simp only [slots] at hhi; omega)
        exact ⟨u,pu,.right hh⟩

end REWB.MaskedOrdered.Owner
