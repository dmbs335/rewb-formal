import REWB.BoundaryApplicationAddressSound

/-! Direct source-address queries follow only materialized head-parent
jumps. Rank correctness proves that the measured fuel visits the entire
jump chain. The probe is instantiated with the two actual endpoint index
queries in the fixed-end application wrapper. -/
namespace REWB.BoundaryApplication.Address
variable {σ : Nat} {A D E : DFA (Fin σ)} {n : Nat}

structure Answer where
  value : Bool
  work : Nat
  visits : Nat

def scan (probe : Cell A D E n→Bool×Nat) (xs : Array (Cell A D E n)) : Nat→Option Nat→Answer
  | 0,_ => ⟨false,1,0⟩
  | _+1,none => ⟨false,1,0⟩
  | fuel+1,some i =>
    match xs[i]? with
    | none => ⟨false,2,0⟩
    | some c =>
      let here:=probe c
      let tail:=scan probe xs fuel c.jump
      ⟨here.1 || tail.value,here.2+tail.work+4,tail.visits+1⟩

def query (probe : Cell A D E n→Bool×Nat) (s : Store A D E n) (p : Fin (n+1)) : Answer :=
  match s.sources.get p with
  | none => ⟨false,1,0⟩
  | some i =>
    match s.nodes[i]? with
    | none => ⟨false,2,0⟩
    | some c =>
      let out:=scan probe s.nodes (c.rank+1) (some i)
      {out with work:=out.work+3}

inductive Reaches (xs : Array (Cell A D E n)) : Nat→Cell A D E n→Prop
  | here {i c} : xs[i]?=some c→Reaches xs i c
  | next {i j c d} : xs[i]?=some d→d.jump=some j→Reaches xs j c→Reaches xs i c

def Hits (probe : Cell A D E n→Bool×Nat) (xs : Array (Cell A D E n)) : Option Nat→Prop
  | none => False
  | some i => ∃c,Reaches xs i c ∧ (probe c).1=true

theorem hits_step (probe : Cell A D E n→Bool×Nat) (xs : Array (Cell A D E n))
    (i : Nat) (c : Cell A D E n) (hc : xs[i]?=some c) :
    Hits probe xs (some i) ↔ (probe c).1=true ∨ Hits probe xs c.jump := by
  constructor
  · rintro ⟨d,hd,hp⟩
    cases hd with
    | here he =>
      have hh : c=d := Option.some.inj (hc.symm.trans he)
      exact Or.inl (hh ▸ hp)
    | @next _ j _ e he hj hh =>
      have hce : c=e := Option.some.inj (hc.symm.trans he)
      subst e
      right
      rw [hj]
      exact ⟨d,hh,hp⟩
  · rintro (hp | ht)
    · exact ⟨c,Reaches.here hc,hp⟩
    · cases hj : c.jump with
      | none => rw [hj] at ht; exact False.elim ht
      | some j =>
        rw [hj] at ht
        obtain ⟨d,hd,hp⟩:=ht
        exact ⟨d,Reaches.next hc hj hd,hp⟩

def Ready (xs : Array (Cell A D E n)) (cursor : Option Nat) (fuel : Nat) : Prop :=
  match cursor with
  | none => True
  | some i => ∃c,xs[i]?=some c ∧ c.rank<fuel

theorem scan_correct (probe : Cell A D E n→Bool×Nat) (xs : Array (Cell A D E n))
    (fuel : Nat) (cursor : Option Nat) (hg : Good xs) (hr : Ready xs cursor fuel) :
    (scan probe xs fuel cursor).value=true ↔ Hits probe xs cursor := by
  induction fuel generalizing cursor with
  | zero =>
    cases cursor with
    | none => simp only [scan,Hits,Bool.false_eq_true]
    | some i => obtain ⟨c,_,hc⟩:=hr; omega
  | succ fuel ih =>
    cases cursor with
    | none => simp only [scan,Hits,Bool.false_eq_true]
    | some i =>
      obtain ⟨c,hc,hfuel⟩:=hr
      have hj : Ready xs c.jump fuel := by
        have hgood:=hg i c hc
        cases he : c.jump with
        | none => trivial
        | some j =>
          rw [he] at hgood
          obtain ⟨d,hd,hdr⟩:=hgood
          exact ⟨d,hd,by omega⟩
      simp only [scan,hc,Bool.or_eq_true]
      rw [ih c.jump hj,hits_step probe xs i c hc]

theorem scan_visits (probe : Cell A D E n→Bool×Nat) (xs : Array (Cell A D E n))
    (fuel : Nat) (cursor : Option Nat) : (scan probe xs fuel cursor).visits≤fuel := by
  induction fuel generalizing cursor with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    cases cursor with
    | none => exact Nat.zero_le _
    | some i =>
      cases hc : xs[i]? with
      | none => simp only [scan,hc]; exact Nat.zero_le _
      | some c => simp only [scan,hc]; exact Nat.add_le_add_right (ih c.jump) 1

theorem scan_work (probe : Cell A D E n→Bool×Nat) (xs : Array (Cell A D E n))
    (C : Nat) (hp : ∀(i : Nat) (c : Cell A D E n),xs[i]?=some c→(probe c).2≤C)
    (fuel : Nat) (cursor : Option Nat) :
    (scan probe xs fuel cursor).work≤fuel*(C+4)+2 := by
  induction fuel generalizing cursor with
  | zero => simp only [scan,Nat.zero_mul,Nat.zero_add]; omega
  | succ fuel ih =>
    cases cursor with
    | none => simp only [scan]; omega
    | some i =>
      cases hc : xs[i]? with
      | none => simp only [scan,hc]; omega
      | some c =>
        have hh:=ih c.jump
        have hcell:=hp i c hc
        simp only [scan,hc,Nat.add_mul,Nat.one_mul]
        omega

theorem query_correct (probe : Cell A D E n→Bool×Nat) (s : Store A D E n) (p : Fin (n+1))
    (hg : Good s.nodes) (hs : SlotsGood s) :
    (query probe s p).value=true ↔ Hits probe s.nodes (s.sources.get p) := by
  cases hi : s.sources.get p with
  | none => simp only [query,hi,Hits,Bool.false_eq_true]
  | some i =>
    obtain ⟨c,hc,_⟩:=hs p i hi
    simp only [query,hi,hc]
    exact scan_correct probe s.nodes (c.rank+1) (some i) hg ⟨c,hc,by omega⟩

theorem query_bound (probe : Cell A D E n→Bool×Nat) (s : Store A D E n) (p : Fin (n+1))
    (C limit : Nat) (hb : Bounded s.nodes limit)
    (hp : ∀(i : Nat) (c : Cell A D E n),s.nodes[i]?=some c→(probe c).2≤C) :
    (query probe s p).visits≤limit+1 ∧ (query probe s p).work≤(limit+1)*(C+4)+5 := by
  cases hi : s.sources.get p with
  | none => simp only [query,hi]; constructor <;> omega
  | some i =>
    cases hc : s.nodes[i]? with
    | none => simp only [query,hi,hc]; constructor <;> omega
    | some c =>
      have hr:=hb i c hc
      have hv:=scan_visits probe s.nodes (c.rank+1) (some i)
      have hw:=scan_work probe s.nodes C hp (c.rank+1) (some i)
      have hm:=Nat.mul_le_mul_right (C+4) (Nat.add_le_add_right hr 1)
      simp only [query,hi,hc]
      constructor <;> omega

end REWB.BoundaryApplication.Address
