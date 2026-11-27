import REWB.BoundaryApplicationStartLocatePath

/-! Direct target-slot queries for the materialized ancestor index.
Both construction and query use only cached integers and arrays; the
input tree and all path relations occur only in correctness statements. -/
namespace REWB.BoundaryApplication.StartLocate
universe u
variable {κ : Type u} {terminals : Nat}

structure Located (κ : Type u) where
  address : Nat
  cell : Cell κ

structure Answer (κ : Type u) where
  value : Option (Located κ)
  work : Nat

def query (levels : Nat) (s : Store κ terminals) (p : Fin terminals) (limit : Nat) : Answer κ :=
  match s.targets.get p with
  | none => ⟨none,1⟩
  | some i =>
    match s.cells[i]? with
    | none => ⟨none,2⟩
    | some c =>
      if limit≤c.depth then
        let out:=ascend s.cells limit levels i 0
        ⟨(s.cells[out.1]?).map (fun cell=>⟨out.1,cell⟩),out.2+5⟩
      else ⟨none,3⟩

theorem query_work (levels : Nat) (s : Store κ terminals) (p : Fin terminals) (limit : Nat) :
    (query levels s p limit).work≤6*levels+6 := by
  unfold query
  split
  · dsimp only; omega
  · rename_i i _
    split
    · dsimp only; omega
    · split
      · have hh:=ascend_work s.cells limit levels i 0
        dsimp only
        omega
      · dsimp only; omega

/-- Input validity for a cutoff at a named terminal. Duplicate labels
are allowed; all matching terminal leaves must support the cutoff. -/
def TargetDepth (p : Fin terminals) (limit : Nat) : Tree κ terminals→Prop
  | .leaf d _ terminal => terminal=some p→limit≤d
  | .node _ _ l r => TargetDepth p limit l ∧ TargetDepth p limit r

theorem targetDepth_zero (p : Fin terminals) (t : Tree κ terminals) : TargetDepth p 0 t := by
  induction t with
  | leaf _ _ _ => exact fun _=>Nat.zero_le _
  | node _ _ _ _ ihl ihr => exact ⟨ihl,ihr⟩

theorem targetDepth_path (xs : Array (Cell κ)) (p : Fin terminals) (par : Option Nat)
    (t : Tree κ terminals) (i limit : Nat) (hp : Path xs p par t i) (hd : TargetDepth p limit t) :
    Eligible xs limit i := by
  induction hp with
  | leaf hc hdepth _ _ hterm => exact ⟨_,hc,by rw [hdepth]; exact hd hterm⟩
  | left _ _ _ _ _ ih => exact ih hd.1
  | right _ _ _ _ _ ih => exact ih hd.2

theorem query_path (levels : Nat) (s : Store κ terminals) (hg : Good levels s.cells)
    (ho : Ordered s.cells) (hcap : s.cells.size≤2^levels)
    (p : Fin terminals) (t : Tree κ terminals) (i limit : Nat)
    (hslot : s.targets.get p=some i) (hp : Path s.cells p none t i) (hi : Eligible s.cells limit i) :
    ∃out u,(query levels s p limit).value=some out ∧ CutPath p limit t u ∧
      out.cell.depth=u.depth ∧ out.cell.payload=u.payload ∧ s.cells[out.address]?=some out.cell := by
  obtain ⟨u,c,hpath,hc,hd,ha⟩:=ascend_path levels s.cells hg ho hcap p t i limit hp hi
  obtain ⟨ci,hci,hlim⟩:=hi
  refine ⟨⟨(ascend s.cells limit levels i 0).1,c⟩,u,?_,hpath,hd,ha,hc⟩
  simp only [query,hslot,hci,if_pos hlim,hc]
  rfl

/-- The returned cell is the exact payload of the first qualifying
annotated subtree on the path chosen by the actual target slot. -/
theorem query_located (levels : Nat) (t : Tree κ terminals) (hg : t.Good) (hcap : t.nodes≤2^levels)
    (p : Fin terminals) (hp : HasTarget p t) (limit : Nat) (hd : TargetDepth p limit t) :
    ∃out u,(query levels (build levels t) p limit).value=some out ∧ CutPath p limit t u ∧
      out.cell.depth=u.depth ∧ out.cell.payload=u.payload ∧
      (build levels t).cells[out.address]?=some out.cell := by
  obtain ⟨i,hslot,hpath⟩:=build_path levels t p hp
  apply query_path levels (build levels t) (build_good levels t) (build_ordered levels t hg)
    (by rw [build_size]; exact hcap) p t i limit hslot hpath
  exact targetDepth_path _ p none t i limit hpath hd

theorem query_correct (levels : Nat) (t : Tree κ terminals) (hg : t.Good) (hcap : t.nodes≤2^levels)
    (p : Fin terminals) (hp : HasTarget p t) (limit : Nat) (hd : TargetDepth p limit t)
    (out : Located κ) (hout : (query levels (build levels t) p limit).value=some out) :
    ∃u,CutPath p limit t u ∧ out.cell.depth=u.depth ∧ out.cell.payload=u.payload := by
  obtain ⟨v,u,hv,hpath,hdepth,hpayload,_⟩:=query_located levels t hg hcap p hp limit hd
  have hvo : v=out := Option.some.inj (hv.symm.trans hout)
  subst v
  exact ⟨u,hpath,hdepth,hpayload⟩

theorem cutPath_zero (p : Fin terminals) (t u : Tree κ terminals) (hc : CutPath p 0 t u) : u=t := by
  cases hc with
  | here _ _ _ => rfl
  | left hd _ => omega
  | right hd _ => omega

theorem query_zero (levels : Nat) (t : Tree κ terminals) (hg : t.Good) (hcap : t.nodes≤2^levels)
    (p : Fin terminals) (hp : HasTarget p t) :
    ∃out,(query levels (build levels t) p 0).value=some out ∧
      out.cell.depth=t.depth ∧ out.cell.payload=t.payload := by
  obtain ⟨out,u,hout,hpath,hd,ha,_⟩:=query_located levels t hg hcap p hp 0 (targetDepth_zero p t)
  have he:=cutPath_zero p t u hpath
  subst u
  exact ⟨out,hout,hd,ha⟩

/-- A cached upper bound determines the row width without traversing
or counting the annotated tree. -/
def levelsFor (bound : Nat) : Nat := bound.log2+1

theorem levelsFor_capacity (bound : Nat) : bound≤2^(levelsFor bound) := by
  exact Nat.le_of_lt (Nat.lt_log2_self (n:=bound))

theorem bounded_query_located (bound : Nat) (t : Tree κ terminals) (hg : t.Good) (hn : t.nodes≤bound)
    (p : Fin terminals) (hp : HasTarget p t) (limit : Nat) (hd : TargetDepth p limit t) :
    ∃out u,(query (levelsFor bound) (build (levelsFor bound) t) p limit).value=some out ∧
      CutPath p limit t u ∧ out.cell.depth=u.depth ∧ out.cell.payload=u.payload ∧
      (build (levelsFor bound) t).cells[out.address]?=some out.cell :=
  query_located (levelsFor bound) t hg (Nat.le_trans hn (levelsFor_capacity bound)) p hp limit hd

theorem bounded_build_work (bound : Nat) (t : Tree κ terminals) (hn : t.nodes≤bound) :
    (build (levelsFor bound) t).work≤terminals+1+bound*(6*(bound.log2+1)+8) := by
  have hb:=build_work (levelsFor bound) t
  have hm:=Nat.mul_le_mul_right (6*(bound.log2+1)+8) hn
  exact Nat.le_trans hb (Nat.add_le_add_left hm (terminals+1))

theorem query_absent (levels : Nat) (t : Tree κ terminals) (p : Fin terminals) (hp : ¬HasTarget p t)
    (limit : Nat) : (query levels (build levels t) p limit).value=none := by
  have hh:=walk_unchanged levels t (empty κ terminals) none p hp
  have hslot : (build levels t).targets.get p=none := by
    apply hh.trans
    change (Vector.replicate terminals none)[p.val]=none
    simp only [Vector.getElem_replicate]
  simp only [query,hslot]

end REWB.BoundaryApplication.StartLocate
