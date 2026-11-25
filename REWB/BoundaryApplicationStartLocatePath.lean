import REWB.BoundaryApplicationStartLocateBuild
import REWB.BoundaryApplicationStartLocateQuery

/-! Structural correspondence between the cached parent search and the
original annotated tree. The returned payload comes from the first
node on an actual target path whose word depth reaches the cutoff. -/
namespace REWB.BoundaryApplication.StartLocate
universe u
variable {κ : Type u} {terminals : Nat}

def Ordered (xs : Array (Cell κ)) : Prop :=
  ∀(i : Nat) (c : Cell κ),xs[i]?=some c→∀(p : Nat) (cp : Cell κ),
    c.parent=some p→xs[p]?=some cp→cp.depth≤c.depth

def ParentDepth (xs : Array (Cell κ)) (par : Option Nat) (depth : Nat) : Prop :=
  ∀(i : Nat) (c : Cell κ),par=some i→xs[i]?=some c→c.depth≤depth

theorem parentDepth_lookup (xs : Array (Cell κ)) (i : Nat) (c : Cell κ) (hc : xs[i]?=some c)
    (d : Nat) (hd : c.depth≤d) : ParentDepth xs (some i) d := by
  intro j v hj hv
  have hij : i=j := Option.some.inj hj
  subst j
  have hcv : c=v := Option.some.inj (hc.symm.trans hv)
  subst v
  exact hd

theorem push_ordered (levels : Nat) (s : Store κ terminals) (he : Earlier s.cells) (ho : Ordered s.cells)
    (par : Option Nat) (hp : ∀i,par=some i→i<s.cells.size) (d : Nat) (a : κ)
    (terminal : Option (Fin terminals)) (hd : ParentDepth s.cells par d) :
    Ordered (push levels s par d a terminal).cells := by
  intro i v hi p cp hpar hcp
  rw [push_cells,Array.getElem?_push] at hi
  split at hi
  · rename_i hii
    have hcv : (makeCell levels s.cells par d a).1=v := Option.some.inj hi
    subst v
    have hpp : par=some p := hpar
    have hpl:=hp p hpp
    rw [push_cells,Array.getElem?_push,if_neg (by omega : p≠s.cells.size)] at hcp
    exact hd p cp hpp hcp
  · have hlt : i<s.cells.size := (Array.getElem?_eq_some_iff.mp hi).choose
    have hpl:=he i v hi p hpar
    rw [push_cells,Array.getElem?_push,if_neg (by omega : p≠s.cells.size)] at hcp
    exact ho i v hi p cp hpar hcp

theorem walk_ordered (levels : Nat) (t : Tree κ terminals) (ht : t.Good)
    (s : Store κ terminals) (hg : Good levels s.cells) (ho : Ordered s.cells)
    (par : Option Nat) (hp : ∀i,par=some i→i<s.cells.size) (hd : ParentDepth s.cells par t.depth) :
    Ordered (walk levels t s par).cells := by
  induction t generalizing s par with
  | leaf d a terminal => exact push_ordered levels s hg.1 ho par hp d a terminal hd
  | node d a l r ihl ihr =>
    let out:=push levels s par d a none
    let mid:=walk levels l out (some s.cells.size)
    have hgo : Good levels out.cells := makeCell_good levels s.cells hg par hp d a
    have hoo : Ordered out.cells := push_ordered levels s hg.1 ho par hp d a none hd
    have hpo : ∀i,some s.cells.size=some i→i<out.cells.size := by
      intro i hi
      have he : s.cells.size=i := Option.some.inj hi
      simp only [out,push_size]
      omega
    have hco:=push_here levels s par d a none
    have hdl : ParentDepth out.cells (some s.cells.size) l.depth :=
      parentDepth_lookup out.cells _ _ hco _ ht.2.2.1
    have hom : Ordered mid.cells := ihl ht.1 out hgo hoo (some s.cells.size) hpo hdl
    have hgm : Good levels mid.cells := walk_good levels l out _ hgo hpo
    have hpm : ∀i,some s.cells.size=some i→i<mid.cells.size := by
      intro i hi
      have hh:=hpo i hi
      simp only [mid,walk_size]
      omega
    have hcm:=walk_extends levels l out (some s.cells.size) _ _ hco
    have hdr : ParentDepth mid.cells (some s.cells.size) r.depth :=
      parentDepth_lookup mid.cells _ _ hcm _ ht.2.2.2
    exact ihr ht.2.1 mid hgm hom (some s.cells.size) hpm hdr

theorem build_ordered (levels : Nat) (t : Tree κ terminals) (ht : t.Good) :
    Ordered (build levels t).cells := by
  apply walk_ordered levels t ht (empty κ terminals) (empty_good levels)
  · intro i c hi
    simp only [empty,Array.getElem?_empty] at hi
    cases hi
  · intro i hi; cases hi
  · intro i c hi; cases hi

theorem eligible_back (xs : Array (Cell κ)) (he : Earlier xs) (ho : Ordered xs)
    (limit i d j : Nat) (hi : i<xs.size) (ha : ancestor xs i d=some j)
    (hj : Eligible xs limit j) : Eligible xs limit i := by
  induction d generalizing i with
  | zero => have hij : i=j := Option.some.inj ha; exact hij ▸ hj
  | succ d ih =>
    let c:=xs[i]
    have hc : xs[i]?=some c := Array.getElem?_eq_getElem hi
    simp only [ancestor,parent,hc,Option.some_bind] at ha
    cases hp : c.parent with
    | none => simp only [hp,Option.none_bind] at ha; cases ha
    | some p =>
      simp only [hp,Option.some_bind] at ha
      have hpl : p<xs.size := Nat.lt_trans (he i c hc p hp) hi
      obtain ⟨cp,hcp,hdepth⟩:=ih p hpl ha
      exact ⟨c,hc,Nat.le_trans hdepth (ho i c hc p cp hp hcp)⟩

theorem cut_no_further (xs : Array (Cell κ)) (he : Earlier xs) (ho : Ordered xs)
    (limit i d j : Nat) (hi : CutAt xs limit i) (ha : ancestor xs i d=some j)
    (hj : Eligible xs limit j) : d=0 := by
  cases d with
  | zero => rfl
  | succ d =>
    obtain ⟨c,hc,hdepth⟩:=hi.1
    have hib : i<xs.size := (Array.getElem?_eq_some_iff.mp hc).choose
    simp only [ancestor,parent,hc,Option.some_bind] at ha
    cases hp : c.parent with
    | none => simp only [hp,Option.none_bind] at ha; cases ha
    | some p =>
      simp only [hp,Option.some_bind] at ha
      have hpl : p<xs.size := Nat.lt_trans (he i c hc p hp) hib
      have hqual:=eligible_back xs he ho limit p d j hpl ha hj
      exact False.elim (hi.2 p (by simp only [parent,hc,Option.some_bind,hp]) hqual)

theorem cut_unique (xs : Array (Cell κ)) (he : Earlier xs) (ho : Ordered xs)
    (limit start i j di dj : Nat) (hai : ancestor xs start di=some i) (haj : ancestor xs start dj=some j)
    (hi : CutAt xs limit i) (hj : CutAt xs limit j) : i=j := by
  have hforward : ∀a b da db,ancestor xs start da=some a→ancestor xs start db=some b→
      CutAt xs limit a→CutAt xs limit b→da≤db→a=b := by
    intro a b da db ha hb hca hcb hle
    have hd : da+(db-da)=db := by omega
    have hab : ancestor xs a (db-da)=some b := by
      rw [←hd,ancestor_add,ha,Option.some_bind] at hb
      exact hb
    have hz:=cut_no_further xs he ho limit a (db-da) b hca hab hcb.1
    rw [hz] at hab
    exact Option.some.inj hab
  rcases Nat.le_total di dj with hle | hle
  · exact hforward i j di dj hai haj hi hj hle
  · exact (hforward j i dj di haj hai hj hi hle).symm

inductive CutPath (p : Fin terminals) (limit : Nat) : Tree κ terminals→Tree κ terminals→Prop
  | here (t) : HasTarget p t→limit≤t.depth→CutPath p limit t t
  | left {d a l r u} : d<limit→CutPath p limit l u→CutPath p limit (.node d a l r) u
  | right {d a l r u} : d<limit→CutPath p limit r u→CutPath p limit (.node d a l r) u

theorem cutPath_target (p : Fin terminals) (limit : Nat) (t u : Tree κ terminals)
    (hc : CutPath p limit t u) : HasTarget p u ∧ limit≤u.depth := by
  induction hc with
  | here _ ht hd => exact ⟨ht,hd⟩
  | left _ _ ih => exact ih
  | right _ _ ih => exact ih

theorem path_has (xs : Array (Cell κ)) (p : Fin terminals) (par : Option Nat)
    (t : Tree κ terminals) (i : Nat) (hp : Path xs p par t i) : HasTarget p t := by
  induction hp with
  | leaf _ _ _ _ ht => exact ht
  | left _ _ _ _ _ ih => exact Or.inl ih
  | right _ _ _ _ _ ih => exact Or.inr ih

theorem path_root (xs : Array (Cell κ)) (p : Fin terminals) (par : Option Nat)
    (t : Tree κ terminals) (i : Nat) (hp : Path xs p par t i) :
    ∃j c,xs[j]?=some c ∧ c.depth=t.depth ∧ c.payload=t.payload ∧ c.parent=par ∧
      ∃distance,ancestor xs i distance=some j := by
  induction hp with
  | @leaf par d a terminal i c hc hd ha hpar ht => exact ⟨i,c,hc,hd,ha,hpar,0,rfl⟩
  | @left par d a l r root c i hc hd ha hpar hp ih =>
    obtain ⟨j,cj,hj,_,_,hjpar,dist,hanc⟩:=ih
    refine ⟨root,c,hc,hd,ha,hpar,dist+1,?_⟩
    rw [ancestor_add,hanc,Option.some_bind,ancestor_one,parent,hj,Option.some_bind,hjpar]
  | @right par d a l r root c i hc hd ha hpar hp ih =>
    obtain ⟨j,cj,hj,_,_,hjpar,dist,hanc⟩:=ih
    refine ⟨root,c,hc,hd,ha,hpar,dist+1,?_⟩
    rw [ancestor_add,hanc,Option.some_bind,ancestor_one,parent,hj,Option.some_bind,hjpar]

theorem path_root_cut (xs : Array (Cell κ)) (p : Fin terminals) (par : Option Nat)
    (t : Tree κ terminals) (i limit : Nat) (hp : Path xs p par t i) (hd : limit≤t.depth)
    (hpar : ∀j,par=some j→¬Eligible xs limit j) :
    ∃u j c,CutPath p limit t u ∧ xs[j]?=some c ∧ c.depth=u.depth ∧ c.payload=u.payload ∧
      (∃distance,ancestor xs i distance=some j) ∧ CutAt xs limit j := by
  obtain ⟨j,c,hc,hdepth,hpayload,hparent,hanc⟩:=path_root xs p par t i hp
  refine ⟨t,j,c,CutPath.here t (path_has xs p par t i hp) hd,hc,hdepth,hpayload,hanc,?_,?_⟩
  · exact ⟨c,hc,by rw [hdepth]; exact hd⟩
  · intro k hk
    apply hpar k
    simpa only [parent,hc,Option.some_bind,hparent] using hk

theorem path_cut_exists (xs : Array (Cell κ)) (p : Fin terminals) (par : Option Nat)
    (t : Tree κ terminals) (i limit : Nat) (hp : Path xs p par t i) (hi : Eligible xs limit i)
    (hpar : ∀j,par=some j→¬Eligible xs limit j) :
    ∃u j c,CutPath p limit t u ∧ xs[j]?=some c ∧ c.depth=u.depth ∧ c.payload=u.payload ∧
      (∃distance,ancestor xs i distance=some j) ∧ CutAt xs limit j := by
  induction hp with
  | @leaf par d a terminal i c hc hd ha hparent ht =>
    have hdepth : limit≤d := by
      obtain ⟨v,hv,hdep⟩:=hi
      have hcv : c=v := Option.some.inj (hc.symm.trans hv)
      subst v
      rwa [hd] at hdep
    exact path_root_cut xs p par _ i limit (Path.leaf hc hd ha hparent ht) hdepth hpar
  | @left par d a l r root c i hc hd ha hparent hp ih =>
    by_cases hdepth : limit≤d
    · exact path_root_cut xs p par _ i limit (Path.left hc hd ha hparent hp) hdepth hpar
    · have hnone : ∀j,some root=some j→¬Eligible xs limit j := by
        intro j hj hqual
        have he : root=j := Option.some.inj hj
        subst j
        obtain ⟨v,hv,hdep⟩:=hqual
        have hcv : c=v := Option.some.inj (hc.symm.trans hv)
        subst v
        rw [hd] at hdep
        exact hdepth hdep
      obtain ⟨u,j,cj,hcut,hj,hdj,haj,hanc,hstop⟩:=ih hi hnone
      exact ⟨u,j,cj,CutPath.left (by omega) hcut,hj,hdj,haj,hanc,hstop⟩
  | @right par d a l r root c i hc hd ha hparent hp ih =>
    by_cases hdepth : limit≤d
    · exact path_root_cut xs p par _ i limit (Path.right hc hd ha hparent hp) hdepth hpar
    · have hnone : ∀j,some root=some j→¬Eligible xs limit j := by
        intro j hj hqual
        have he : root=j := Option.some.inj hj
        subst j
        obtain ⟨v,hv,hdep⟩:=hqual
        have hcv : c=v := Option.some.inj (hc.symm.trans hv)
        subst v
        rw [hd] at hdep
        exact hdepth hdep
      obtain ⟨u,j,cj,hcut,hj,hdj,haj,hanc,hstop⟩:=ih hi hnone
      exact ⟨u,j,cj,CutPath.right (by omega) hcut,hj,hdj,haj,hanc,hstop⟩

theorem ascend_path (levels : Nat) (xs : Array (Cell κ)) (hg : Good levels xs) (ho : Ordered xs)
    (hcap : xs.size≤2^levels) (p : Fin terminals) (t : Tree κ terminals) (i limit : Nat)
    (hp : Path xs p none t i) (hi : Eligible xs limit i) :
    ∃u c,CutPath p limit t u ∧ xs[(ascend xs limit levels i 0).1]?=some c ∧
      c.depth=u.depth ∧ c.payload=u.payload := by
  have hib : i<xs.size := (Array.getElem?_eq_some_iff.mp hi.choose_spec.1).choose
  obtain ⟨⟨da,ha⟩,hcut⟩:=ascend_complete levels xs hg hcap limit i hib hi
  obtain ⟨u,j,c,hpath,hj,hdepth,hpayload,⟨db,hb⟩,hstop⟩:=
    path_cut_exists xs p none t i limit hp hi (by intro j hj; cases hj)
  have heq:=cut_unique xs hg.1 ho limit i _ j da db ha hb hcut hstop
  exact ⟨u,c,hpath,by rw [heq]; exact hj,hdepth,hpayload⟩

end REWB.BoundaryApplication.StartLocate
