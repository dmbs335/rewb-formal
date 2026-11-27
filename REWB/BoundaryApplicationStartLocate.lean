import REWB.BoundaryApplicationLocate

/-! A generic, materialized parent-doubling index for annotated tries.
The payload and cached word depth are copied once from each input node.
The caller supplies a logarithmic row width from its cached input bound;
the construction performs one preorder traversal and no text scans. -/
namespace REWB.BoundaryApplication.StartLocate
universe u
variable {κ : Type u} {terminals : Nat}

inductive Tree (κ : Type u) (terminals : Nat) where
  | leaf (depth : Nat) (payload : κ) (terminal : Option (Fin terminals))
  | node (depth : Nat) (payload : κ) (left right : Tree κ terminals)

def Tree.depth : Tree κ terminals→Nat
  | .leaf d _ _ => d
  | .node d _ _ _ => d

def Tree.payload : Tree κ terminals→κ
  | .leaf _ a _ => a
  | .node _ a _ _ => a

def Tree.nodes : Tree κ terminals→Nat
  | .leaf _ _ _ => 1
  | .node _ _ l r => l.nodes+r.nodes+1

def Tree.Good : Tree κ terminals→Prop
  | .leaf _ _ _ => True
  | .node d _ l r => l.Good ∧ r.Good ∧ d≤l.depth ∧ d≤r.depth

structure Cell (κ : Type u) where
  depth : Nat
  payload : κ
  parent : Option Nat
  jumps : Array (Option Nat)

def parent (xs : Array (Cell κ)) (i : Nat) : Option Nat :=
  (xs[i]?).bind fun c=>c.parent

/-- Specification only: the ordinary parent walk is never executed by
the locator. Its step count describes the materialized jump rows. -/
def ancestor (xs : Array (Cell κ)) (i : Nat) : Nat→Option Nat
  | 0 => some i
  | n+1 => (parent xs i).bind fun p=>ancestor xs p n

def Earlier (xs : Array (Cell κ)) : Prop :=
  ∀(i : Nat) (c : Cell κ),xs[i]?=some c→∀p,c.parent=some p→p<i

def Extends (xs ys : Array (Cell κ)) : Prop :=
  ∀(i : Nat) (c : Cell κ),xs[i]?=some c→ys[i]?=some c

def Good (levels : Nat) (xs : Array (Cell κ)) : Prop :=
  Earlier xs ∧ ∀(i : Nat) (c : Cell κ),xs[i]?=some c→c.jumps.size=levels ∧
    ∀k,k<levels→c.jumps[k]?=some (ancestor xs i (2^k))

theorem ancestor_add (xs : Array (Cell κ)) (i a b : Nat) :
    ancestor xs i (a+b)=(ancestor xs i a).bind fun j=>ancestor xs j b := by
  induction a generalizing i with
  | zero => simp only [Nat.zero_add,ancestor,Option.some_bind]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [ancestor]
    cases hp : parent xs i with
    | none => rfl
    | some p => exact ih p

theorem ancestor_bound (xs : Array (Cell κ)) (he : Earlier xs) (i d j : Nat)
    (ha : ancestor xs i d=some j) : j+d≤i := by
  induction d generalizing i with
  | zero => have hh : i=j := Option.some.inj ha; omega
  | succ d ih =>
    simp only [ancestor,parent] at ha
    cases hc : xs[i]? with
    | none => simp only [hc,Option.none_bind] at ha; cases ha
    | some c =>
      simp only [hc,Option.some_bind] at ha
      cases hp : c.parent with
      | none => simp only [hp,Option.none_bind] at ha; cases ha
      | some p =>
        simp only [hp,Option.some_bind] at ha
        have hprev:=ih p ha
        have hlt:=he i c hc p hp
        omega

theorem ancestor_extends (xs ys : Array (Cell κ)) (he : Earlier xs) (hxy : Extends xs ys)
    (i d : Nat) (hi : i<xs.size) : ancestor ys i d=ancestor xs i d := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih =>
    let c:=xs[i]
    have hc : xs[i]?=some c := Array.getElem?_eq_getElem hi
    have hy:=hxy i c hc
    simp only [ancestor,parent,hc,hy,Option.some_bind]
    cases hp : c.parent with
    | none => rfl
    | some p =>
      simp only [Option.some_bind]
      exact ih p (Nat.lt_trans (he i c hc p hp) hi)

theorem push_extends (xs : Array (Cell κ)) (c : Cell κ) : Extends xs (xs.push c) := by
  intro i v hi
  have hlt : i<xs.size := (Array.getElem?_eq_some_iff.mp hi).choose
  rw [Array.getElem?_push,if_neg (by omega : i≠xs.size)]
  exact hi

theorem push_earlier (xs : Array (Cell κ)) (he : Earlier xs) (c : Cell κ)
    (hp : ∀p,c.parent=some p→p<xs.size) : Earlier (xs.push c) := by
  intro i v hi p hv
  have hib : i<(xs.push c).size := (Array.getElem?_eq_some_iff.mp hi).choose
  simp only [Array.size_push] at hib
  by_cases hl : i<xs.size
  · rw [Array.getElem?_push,if_neg (by omega : i≠xs.size)] at hi
    exact he i v hi p hv
  · have hei : i=xs.size := by omega
    subst i
    have hvc : c=v := by simpa only [Array.getElem?_push,Nat.lt_irrefl,if_false,if_true,Option.some.injEq] using hi
    subst v
    exact hp p hv

/-- One cell lookup and one cached-row lookup, with explicit counters. -/
def readJump (xs : Array (Cell κ)) (i k : Nat) : Option Nat×Nat :=
  match xs[i]? with
  | none => (none,1)
  | some c => ((c.jumps[k]?).getD none,2)

theorem readJump_work (xs : Array (Cell κ)) (i k : Nat) : (readJump xs i k).2≤2 := by
  unfold readJump
  split <;> omega

theorem readJump_correct (levels : Nat) (xs : Array (Cell κ)) (hg : Good levels xs)
    (i k : Nat) (hi : i<xs.size) (hk : k<levels) :
    (readJump xs i k).1=ancestor xs i (2^k) := by
  have hc : xs[i]?=some xs[i] := Array.getElem?_eq_getElem hi
  simp only [readJump,hc,(hg.2 i _ hc).2 k hk,Option.getD_some]

def rowNext (xs : Array (Cell κ)) (next : Option Nat) (k : Nat) : Option Nat×Nat :=
  match next with
  | none => (none,1)
  | some i => let out:=readJump xs i k; (out.1,out.2+1)

def rowLoop (xs : Array (Cell κ)) : Nat→Nat→Option Nat→Array (Option Nat)→Nat→Array (Option Nat)×Nat
  | 0,_,_,acc,work => (acc,work)
  | fuel+1,k,next,acc,work =>
    let out:=rowNext xs next k
    rowLoop xs fuel (k+1) out.1 (acc.push next) (work+out.2+3)

def makeRow (xs : Array (Cell κ)) (levels : Nat) (p : Option Nat) : Array (Option Nat)×Nat :=
  rowLoop xs levels 0 p #[] 1

theorem rowNext_work (xs : Array (Cell κ)) (next : Option Nat) (k : Nat) : (rowNext xs next k).2≤3 := by
  cases next with
  | none => change 1≤3; omega
  | some i => have hh:=readJump_work xs i k; exact Nat.add_le_add_right hh 1

theorem rowLoop_work (xs : Array (Cell κ)) (fuel k : Nat) (next : Option Nat)
    (acc : Array (Option Nat)) (work : Nat) :
    (rowLoop xs fuel k next acc work).2≤work+6*fuel := by
  induction fuel generalizing k next acc work with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    have hr:=ih (k+1) (rowNext xs next k).1 (acc.push next) (work+(rowNext xs next k).2+3)
    have hs:=rowNext_work xs next k
    change (rowLoop xs fuel (k+1) (rowNext xs next k).1 (acc.push next) (work+(rowNext xs next k).2+3)).2≤_
    omega

theorem makeRow_work (xs : Array (Cell κ)) (levels : Nat) (p : Option Nat) :
    (makeRow xs levels p).2≤1+6*levels := rowLoop_work xs levels 0 p #[] 1


theorem rowLoop_size (xs : Array (Cell κ)) (fuel k : Nat) (next : Option Nat)
    (acc : Array (Option Nat)) (work : Nat) :
    (rowLoop xs fuel k next acc work).1.size=acc.size+fuel := by
  induction fuel generalizing k next acc work with
  | zero => rfl
  | succ fuel ih =>
    simp only [rowLoop,ih,Array.size_push]
    omega

theorem rowLoop_correct (xs : Array (Cell κ)) (levels : Nat) (f : Nat→Option Nat)
    (hf : ∀k,k<levels→(rowNext xs (f k) k).1=f (k+1))
    (fuel k : Nat) (acc : Array (Option Nat)) (work : Nat) (hk : k+fuel≤levels)
    (hsize : acc.size=k) (hacc : ∀j,j<k→acc[j]?=some (f j)) :
    ∀j,j<k+fuel→(rowLoop xs fuel k (f k) acc work).1[j]?=some (f j) := by
  induction fuel generalizing k acc work with
  | zero => exact hacc
  | succ fuel ih =>
    have hnew : ∀j,j<k+1→(acc.push (f k))[j]?=some (f j) := by
      intro j hj
      by_cases hjk : j=k
      · subst j
        rw [←hsize,Array.getElem?_push_size,hsize]
      · rw [Array.getElem?_push,if_neg (by omega : j≠acc.size)]
        exact hacc j (by omega)
    have hcall:=ih (k+1) (acc.push (f k)) (work+(rowNext xs (f k) k).2+3)
      (by omega) (by simpa only [Array.size_push,hsize]) hnew
    simp only [rowLoop,hf k (by omega)]
    intro j hj
    exact hcall j (by omega)

theorem rowNext_ancestor (levels : Nat) (xs ys : Array (Cell κ))
    (hg : Good levels xs) (he : Earlier ys) (hxy : Extends xs ys)
    (k : Nat) (hk : k<levels) :
    (rowNext xs (ancestor ys xs.size (2^k)) k).1=ancestor ys xs.size (2^(k+1)) := by
  rw [Nat.pow_succ,Nat.mul_two,ancestor_add]
  cases ha : ancestor ys xs.size (2^k) with
  | none => rfl
  | some j =>
    have hb:=ancestor_bound ys he xs.size (2^k) j ha
    have hp : 0<2^k := Nat.two_pow_pos k
    have hj : j<xs.size := by omega
    change (readJump xs j k).1=ancestor ys j (2^k)
    rw [readJump_correct levels xs hg j k hj hk]
    exact (ancestor_extends xs ys hg.1 hxy j (2^k) hj).symm

def makeCell (levels : Nat) (xs : Array (Cell κ)) (p : Option Nat) (d : Nat) (a : κ) : Cell κ×Nat :=
  let row:=makeRow xs levels p
  (⟨d,a,p,row.1⟩,row.2+1)

theorem makeCell_work (levels : Nat) (xs : Array (Cell κ)) (p : Option Nat) (d : Nat) (a : κ) :
    (makeCell levels xs p d a).2≤6*levels+2 := by
  have hh:=makeRow_work xs levels p
  change (makeRow xs levels p).2+1≤_
  omega

theorem makeCell_good (levels : Nat) (xs : Array (Cell κ)) (hg : Good levels xs)
    (p : Option Nat) (hp : ∀j,p=some j→j<xs.size) (d : Nat) (a : κ) :
    Good levels (xs.push (makeCell levels xs p d a).1) := by
  let c:=(makeCell levels xs p d a).1
  let ys:=xs.push c
  have hxy : Extends xs ys := push_extends xs c
  have he : Earlier ys := push_earlier xs hg.1 c hp
  have hone : ancestor ys xs.size (2^0)=p := by
    simp only [Nat.pow_zero,ancestor,parent,ys,Array.getElem?_push_size,Option.some_bind,c,makeCell]
    cases p <;> rfl
  have hrow:=rowLoop_correct xs levels (fun k=>ancestor ys xs.size (2^k))
    (rowNext_ancestor levels xs ys hg he hxy) levels 0 #[] 1 (by omega) rfl
    (by intro j hj; omega)
  dsimp only at hrow
  rw [hone] at hrow
  refine ⟨he,?_⟩
  intro i v hi
  have hib : i<ys.size := (Array.getElem?_eq_some_iff.mp hi).choose
  simp only [ys,Array.size_push] at hib
  by_cases hl : i<xs.size
  · have hix : xs[i]?=some v := by
      change (xs.push c)[i]?=some v at hi
      rwa [Array.getElem?_push,if_neg (by omega : i≠xs.size)] at hi
    refine ⟨(hg.2 i v hix).1,?_⟩
    intro k hk
    rw [(hg.2 i v hix).2 k hk]
    congr 1
    exact (ancestor_extends xs ys hg.1 hxy i (2^k) hl).symm
  · have hie : i=xs.size := by omega
    subst i
    have hv : c=v := by simpa only [ys,Array.getElem?_push_size,Option.some.injEq] using hi
    subst v
    refine ⟨?_,?_⟩
    · simpa only [c,makeCell,makeRow,Array.size_empty,Nat.zero_add] using rowLoop_size xs levels 0 p #[] 1
    · intro k hk
      exact hrow k (by omega)

end REWB.BoundaryApplication.StartLocate
