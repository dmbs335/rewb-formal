import REWB.MaskedOrderedErase
import REWB.MaskedThresholdValidation

/-! Dense-component leaders depend on the full occurrence set, never on
either mask. This representation remains meaningful during partial merges,
when a dense component need not yet be an arithmetic progression. -/
namespace REWB.MaskedClusterLeaders
open REWB.MaskedOrdered
variable {h : Nat}

/-- The first occurrence and every occurrence following a sparse gap. -/
def Leader (xs : List Nat) (length p : Nat) : Prop :=
  p∈xs ∧ ∀ q,q∈xs → q<p → length<2*(p-q)

def beforeAllows (length p : Nat) : Option Nat→Bool
  | none => true
  | some q => decide (length<2*(p-q))

theorem beforeAllows_correct (xs : List Nat) (length p : Nat) (before : Option Nat)
    (hb : Tree.PredSpec xs p before) :
    beforeAllows length p before=true ↔
      ∀ q,q∈xs → q<p → length<2*(p-q) := by
  cases before with
  | none =>
    simp only [beforeAllows,true_iff]
    intro q hq hqp
    have hp:=hb q hq
    omega
  | some a =>
    simp only [beforeAllows,decide_eq_true_eq]
    constructor
    · intro ha q hq hqp
      have hqa:=hb.2.2 q hq hqp
      omega
    · intro hh
      exact hh a hb.1 hb.2.1

def check (occurrences : Tree h) (capacity length p : Nat) : Bool×Nat :=
  let member:=Tree.contains occurrences capacity p
  let before:=Tree.pred occurrences capacity p
  (member.1 && beforeAllows length p before.1,member.2+before.2+5)

theorem check_correct (t : Tree h) (capacity length p : Nat)
    (hg : Tree.Good t) (hf : Tree.Fits t 0) (hc : capacity=2^h) :
    (check t capacity length p).1=true ↔ Leader t.entries length p := by
  simp only [check,Bool.and_eq_true,Tree.contains_correct t capacity p hf hc,
    beforeAllows_correct _ length p _ (Tree.pred_correct t capacity p hg hf hc),Leader]

theorem check_work (t : Tree h) (capacity length p : Nat) :
    (check t capacity length p).2≤11*h+10 := by
  have hm:=Tree.contains_work t capacity p
  have hp:=Tree.pred_work t capacity p
  simp only [check]
  omega

theorem leader_mem_congr (xs ys : List Nat) (length p : Nat)
    (he : ∀ x,x∈xs ↔ x∈ys) : Leader xs length p ↔ Leader ys length p := by
  simp only [Leader,he]

/-- Inserting one occurrence can change old leader status only at its
strict successor. Temporary partial classes require no periodicity premise. -/
theorem insert_away (xs ys : List Nat) (length p x : Nat) (after : Option Nat)
    (hi : ∀ q,q∈ys ↔ q=p ∨ q∈xs) (hs : Tree.SuccSpec xs p after)
    (hx : x≠p) (ha : after≠some x) : Leader ys length x ↔ Leader xs length x := by
  constructor
  · rintro ⟨hm,hl⟩
    refine ⟨?_,?_⟩
    · rcases (hi x).mp hm with he|ho
      · exact False.elim (hx he)
      · exact ho
    · intro q hq hqx
      exact hl q ((hi q).mpr (Or.inr hq)) hqx
  · rintro ⟨hm,hl⟩
    refine ⟨(hi x).mpr (Or.inr hm),?_⟩
    intro q hq hqx
    rcases (hi q).mp hq with he|ho
    · subst q
      cases after with
      | none => have hh:=hs x hm; omega
      | some a =>
        have hax:=hs.2.2 x hm hqx
        have hne : a≠x := by intro he; exact ha (congrArg some he)
        have hh:=hl a hs.1 (by omega)
        have hpa:=hs.2.1
        omega
    · exact hl q ho hqx

def Represents (occurrences leaders : Tree h) (length : Nat) : Prop :=
  ∀ p,p∈leaders.entries ↔ Leader occurrences.entries length p

def refresh (occurrences leaders : Tree h) (capacity length p : Nat) : Tree h×Nat :=
  let answer:=check occurrences capacity length p
  let changed:=if answer.1 then Tree.insert leaders capacity p else Tree.erase leaders capacity p
  (changed.1,answer.2+changed.2+2)

theorem refresh_good (occurrences leaders : Tree h) (capacity length p : Nat)
    (hg : Tree.Good leaders) : Tree.Good (refresh occurrences leaders capacity length p).1 := by
  simp only [refresh]
  split
  · exact Tree.insert_good leaders capacity p hg
  · exact Tree.erase_good leaders capacity p hg

theorem refresh_fits (occurrences leaders : Tree h) (capacity length p : Nat)
    (hf : Tree.Fits leaders 0) (hc : capacity=2^h) (hp : p<2^h) :
    Tree.Fits (refresh occurrences leaders capacity length p).1 0 := by
  simp only [refresh]
  split
  · exact Tree.insert_fits leaders capacity p hf hc hp
  · exact Tree.erase_fits leaders capacity p hf hc

theorem refresh_mem (occurrences leaders : Tree h) (capacity length p x : Nat)
    (hg : Tree.Good occurrences) (hf : Tree.Fits occurrences 0)
    (hl : Tree.Fits leaders 0) (hc : capacity=2^h) (hp : p<2^h) :
    x∈(refresh occurrences leaders capacity length p).1.entries ↔
      (x=p ∧ Leader occurrences.entries length p) ∨ (x≠p ∧ x∈leaders.entries) := by
  have hh:=check_correct occurrences capacity length p hg hf hc
  simp only [refresh]
  split
  next ha =>
    rw [Tree.insert_mem leaders capacity p x hl hc hp]
    have hleader:=hh.mp ha
    by_cases hx : x=p <;> simp [hx,hleader]
  next ha =>
    rw [Tree.erase_mem leaders capacity p x hl hc]
    have hnot : ¬Leader occurrences.entries length p := fun he=>ha (hh.mpr he)
    by_cases hx : x=p <;> simp [hx,hnot]

theorem refresh_work (occurrences leaders : Tree h) (capacity length p : Nat) :
    (refresh occurrences leaders capacity length p).2≤23*h+15 := by
  have hc:=check_work occurrences capacity length p
  have hi:=Tree.insert_work leaders capacity p
  have he:=Tree.erase_work leaders capacity p
  simp only [refresh]
  split <;> omega

end REWB.MaskedClusterLeaders
