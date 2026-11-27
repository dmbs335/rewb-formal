import REWB.BoundaryApplicationStartLocate

/-! The depth-cut query reads the doubling levels from high to low.
Every successful jump uses a cached ancestor depth; there are no powers,
text lengths, parent walks, or path-list traversals in executable code. -/
namespace REWB.BoundaryApplication.StartLocate
universe u
variable {κ : Type u}

def Eligible (xs : Array (Cell κ)) (limit i : Nat) : Prop :=
  ∃c,xs[i]?=some c ∧ limit≤c.depth

def CutAt (xs : Array (Cell κ)) (limit i : Nat) : Prop :=
  Eligible xs limit i ∧ ∀p,parent xs i=some p→¬Eligible xs limit p

def jumpProbe (xs : Array (Cell κ)) (limit i k : Nat) : Option Nat×Nat :=
  let out:=readJump xs i k
  match out.1 with
  | none => (none,out.2+1)
  | some j =>
    match xs[j]? with
    | none => (none,out.2+2)
    | some c => (if limit≤c.depth then some j else none,out.2+3)

theorem jumpProbe_work (xs : Array (Cell κ)) (limit i k : Nat) : (jumpProbe xs limit i k).2≤5 := by
  have hh:=readJump_work xs i k
  unfold jumpProbe
  dsimp only
  split
  · omega
  · split <;> omega

theorem jumpProbe_correct (xs : Array (Cell κ)) (limit i k j : Nat) :
    (jumpProbe xs limit i k).1=some j ↔ (readJump xs i k).1=some j ∧ Eligible xs limit j := by
  unfold jumpProbe
  dsimp only
  cases hr : (readJump xs i k).1 with
  | none => simp only [hr,reduceCtorEq,false_and]
  | some a =>
    cases hc : xs[a]? with
    | none =>
      simp only [hr,hc,reduceCtorEq,false_iff]
      rintro ⟨he,c,hec,_⟩
      have haj : a=j := Option.some.inj he
      subst j
      rw [hc] at hec
      cases hec
    | some c =>
      by_cases hl : limit≤c.depth
      · simp only [hr,hc,if_pos hl,Option.some.injEq]
        constructor
        · intro he; subst j; exact ⟨rfl,c,hc,hl⟩
        · exact fun h=>h.1
      · simp only [hr,hc,if_neg hl,reduceCtorEq,false_iff]
        rintro ⟨he,d,hed,hdep⟩
        have haj : a=j := Option.some.inj he
        subst j
        have hcd : c=d := Option.some.inj (hc.symm.trans hed)
        subst d
        exact hl hdep

def ascend (xs : Array (Cell κ)) (limit : Nat) : Nat→Nat→Nat→Nat×Nat
  | 0,i,work => (i,work+1)
  | k+1,i,work =>
    let out:=jumpProbe xs limit i k
    ascend xs limit k (out.1.getD i) (work+out.2+1)

theorem ascend_work (xs : Array (Cell κ)) (limit fuel i work : Nat) :
    (ascend xs limit fuel i work).2≤work+6*fuel+1 := by
  induction fuel generalizing i work with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    have hh:=ih ((jumpProbe xs limit i fuel).1.getD i) (work+(jumpProbe xs limit i fuel).2+1)
    have hp:=jumpProbe_work xs limit i fuel
    change (ascend xs limit fuel ((jumpProbe xs limit i fuel).1.getD i) (work+(jumpProbe xs limit i fuel).2+1)).2≤_
    omega

theorem ancestor_one (xs : Array (Cell κ)) (i : Nat) : ancestor xs i 1=parent xs i := by
  simp only [ancestor,Option.bind_some]

/-- A power-sized excluded ancestor bounds each recursive search. This
invariant proves the exact stopping edge without executing any linear
walk or constructing powers in the query. -/
theorem ascend_correct (levels : Nat) (xs : Array (Cell κ)) (hg : Good levels xs)
    (limit fuel i work : Nat) (hf : fuel≤levels) (hi : i<xs.size) (he : Eligible xs limit i)
    (hb : ∀j,ancestor xs i (2^fuel)=some j→¬Eligible xs limit j) :
    ∃distance,distance<2^fuel ∧ ancestor xs i distance=some (ascend xs limit fuel i work).1 ∧
      CutAt xs limit (ascend xs limit fuel i work).1 := by
  induction fuel generalizing i work with
  | zero =>
    refine ⟨0,by decide,rfl,he,?_⟩
    intro p hp
    apply hb p
    simpa only [Nat.pow_zero,ancestor_one] using hp
  | succ fuel ih =>
    have hk : fuel<levels := by omega
    have hjump:=readJump_correct levels xs hg i fuel hi hk
    cases hp : (jumpProbe xs limit i fuel).1 with
    | none =>
      have hbound : ∀j,ancestor xs i (2^fuel)=some j→¬Eligible xs limit j := by
        intro j haj hel
        have hpr:=(jumpProbe_correct xs limit i fuel j).mpr ⟨hjump.trans haj,hel⟩
        rw [hp] at hpr
        cases hpr
      obtain ⟨dist,hdit,had,hcut⟩:=ih i (work+(jumpProbe xs limit i fuel).2+1) (by omega) hi he hbound
      refine ⟨dist,?_,?_,?_⟩
      · rw [Nat.pow_succ,Nat.mul_two]
        omega
      · simpa only [ascend,hp,Option.getD_none] using had
      · simpa only [ascend,hp,Option.getD_none] using hcut
    | some j =>
      obtain ⟨hread,hqual⟩:=(jumpProbe_correct xs limit i fuel j).mp hp
      have haj : ancestor xs i (2^fuel)=some j := hjump.symm.trans hread
      have hjlt : j<xs.size := by
        have hh:=ancestor_bound xs hg.1 i (2^fuel) j haj
        exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right j (2^fuel)) hh) hi
      have hbound : ∀a,ancestor xs j (2^fuel)=some a→¬Eligible xs limit a := by
        intro a haa
        apply hb a
        rw [Nat.pow_succ,Nat.mul_two,ancestor_add,haj,Option.some_bind]
        exact haa
      obtain ⟨dist,hdit,had,hcut⟩:=ih j (work+(jumpProbe xs limit i fuel).2+1) (by omega) hjlt hqual hbound
      refine ⟨2^fuel+dist,?_,?_,?_⟩
      · rw [Nat.pow_succ,Nat.mul_two]
        omega
      · rw [ancestor_add,haj,Option.some_bind]
        simpa only [ascend,hp,Option.getD_some] using had
      · simpa only [ascend,hp,Option.getD_some] using hcut

theorem ascend_complete (levels : Nat) (xs : Array (Cell κ)) (hg : Good levels xs)
    (hcap : xs.size≤2^levels) (limit i : Nat) (hi : i<xs.size) (he : Eligible xs limit i) :
    (∃distance,ancestor xs i distance=some (ascend xs limit levels i 0).1) ∧
      CutAt xs limit (ascend xs limit levels i 0).1 := by
  have hb : ∀j,ancestor xs i (2^levels)=some j→¬Eligible xs limit j := by
    intro j hj
    have hh:=ancestor_bound xs hg.1 i (2^levels) j hj
    omega
  obtain ⟨d,_,hd,hcut⟩:=ascend_correct levels xs hg limit levels i 0 (Nat.le_refl _) hi he hb
  exact ⟨⟨d,hd⟩,hcut⟩

end REWB.BoundaryApplication.StartLocate
