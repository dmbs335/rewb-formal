import REWB.BoundaryBorderWindowGeometry

/-! Actual short-window border equality query. It extracts at most two
occurrence components and applies the measured period-break selector to
each. The result consists of two physical AP/point/empty choices. No AP
seed, periodic interval, occurrence list, or answer relation is supplied
to the executable query. -/
namespace REWB.BoundaryBorder.Window
open REWB.Periodic REWB.MaskedRunDiscovery REWB.MaskedOrdered REWB.LCEIndex
variable {σ h : Nat}

def selectOption (idx : RankIndex.Index) (n a j : Nat) : Option Band→Selection
  | none => ⟨.empty,1⟩
  | some b =>
    let picked:=select idx n b.first b.step b.first b.last a j
    ⟨picked.choice,picked.work+2⟩

theorem selectOption_work (idx : RankIndex.Index) (n a j : Nat) (band : Option Band) :
    (selectOption idx n a j band).work≤39*(n.log2+1)+36 := by
  cases band with
  | none => simp only [selectOption]; omega
  | some b =>
    have hh:=select_work idx n b.first b.step b.first b.last a j
    change (select idx n b.first b.step b.first b.last a j).work+2≤_
    omega

theorem valid_seed (f : Nat→Fin σ) (n j L hi : Nat) (xs : List Nat) (b : Band)
    (hfull : Complete f n j L xs) (hv : Valid f n L hi xs b) :
    b.first+b.step≤n ∧ segment f b.first b.step=segment f j b.step := by
  have ho:=(hfull b.first).mp hv.first_mem
  have hbound : b.first+L≤n := ho.1
  refine ⟨by have hq:=hv.step_le; omega,?_⟩
  apply (segment_eq_points f b.first j b.step).mpr
  intro i hi
  exact (segment_eq_points f b.first j L).mp ho.2 i (Nat.lt_of_lt_of_le hi hv.step_le)

theorem selectOption_correct (f : Nat→Fin σ) (n a j L hi : Nat) (xs : List Nat)
    (band : Option Band) (hfull : Complete f n j L xs)
    (hv : ∀b,band=some b→Valid f n L hi xs b) (ha : a≤n) (hj : j+L≤n) (p : Nat) :
    (selectOption (prepare f n) n a j band).choice.Holds p ↔
      ∃b,band=some b ∧ b.Holds p ∧ p≤a ∧ Agree f n p j (a-p) := by
  cases band with
  | none =>
    change False ↔ _
    constructor
    · exact False.elim
    · rintro ⟨_,he,_⟩
      cases he
  | some b =>
    have hb:=hv b rfl
    have hs:=valid_seed f n j L hi xs b hfull hb
    have hh:=select_from_seed f n b.first b.step b.first b.last a j hb.positive hs.1
      (by have hq:=hb.step_le; omega) ha hb.span hs.2 p
    change (select (prepare f n) n b.first b.step b.first b.last a j).choice.Holds p ↔ _
    rw [hh]
    constructor
    · intro hp
      exact ⟨b,rfl,hp⟩
    · rintro ⟨c,he,hp⟩
      have heq : b=c := Option.some.inj he
      exact heq ▸ hp

structure Selected where
  first : Choice
  second : Choice
  work : Nat
  deriving Repr, DecidableEq

def Selected.Holds (out : Selected) (p : Nat) : Prop := out.first.Holds p ∨ out.second.Holds p

def query (idx : RankIndex.Index) (t : Tree h) (capacity n L lo hi a j : Nat) : Selected :=
  let bands:=extract idx t capacity n L lo hi
  let left:=selectOption idx n a j bands.first
  let right:=selectOption idx n a j bands.second
  ⟨left.choice,right.choice,bands.work+left.work+right.work+3⟩

theorem query_work (idx : RankIndex.Index) (t : Tree h) (capacity n L lo hi a j : Nat) :
    (query idx t capacity n L lo hi a j).work≤28*h+104*(n.log2+1)+146 := by
  have he:=extract_work idx t capacity n L lo hi
  have hl:=selectOption_work idx n a j (extract idx t capacity n L lo hi).first
  have hr:=selectOption_work idx n a j (extract idx t capacity n L lo hi).second
  change _+_+_+3≤_
  omega

theorem query_correct (f : Nat→Fin σ) (n j L lo hi a : Nat) (t : Tree h) (capacity : Nat)
    (hg : Tree.Good t) (ht : Tree.Fits t 0) (hc : capacity=2^h)
    (hfull : Complete f n j L t.entries) (hwidth : hi-lo<L)
    (ha : a≤n) (hj : j+L≤n) (p : Nat) :
    (query (prepare f n) t capacity n L lo hi a j).Holds p ↔
      p∈t.entries ∧ lo≤p ∧ p≤hi ∧ p≤a ∧ Agree f n p j (a-p) := by
  have hL : 0<L := by omega
  have hl:=selectOption_correct f n a j L hi t.entries
    (extract (prepare f n) t capacity n L lo hi).first hfull
    (fun b hb=>(extract_valid f n j L lo hi t capacity hg ht hc hfull hL b (Or.inl hb)).1) ha hj p
  have hr:=selectOption_correct f n a j L hi t.entries
    (extract (prepare f n) t capacity n L lo hi).second hfull
    (fun b hb=>(extract_valid f n j L lo hi t capacity hg ht hc hfull hL b (Or.inr hb)).1) ha hj p
  change ((selectOption (prepare f n) n a j (extract (prepare f n) t capacity n L lo hi).first).choice.Holds p ∨
    (selectOption (prepare f n) n a j (extract (prepare f n) t capacity n L lo hi).second).choice.Holds p) ↔ _
  rw [hl,hr]
  have he:=extract_correct f n j L lo hi t capacity hg ht hc hfull hwidth p
  constructor
  · rintro (⟨b,hb,hm,hpa,heq⟩|⟨b,hb,hm,hpa,heq⟩)
    · have hx:=he.mp (Or.inl ⟨b,hb,hm⟩)
      exact ⟨hx.1,hx.2.1,hx.2.2,hpa,heq⟩
    · have hx:=he.mp (Or.inr ⟨b,hb,hm⟩)
      exact ⟨hx.1,hx.2.1,hx.2.2,hpa,heq⟩
  · rintro ⟨hp,hlo,hhi,hpa,heq⟩
    rcases he.mpr ⟨hp,hlo,hhi⟩ with ⟨b,hb,hm⟩|⟨b,hb,hm⟩
    · exact Or.inl ⟨b,hb,hm,hpa,heq⟩
    · exact Or.inr ⟨b,hb,hm,hpa,heq⟩

end REWB.BoundaryBorder.Window
