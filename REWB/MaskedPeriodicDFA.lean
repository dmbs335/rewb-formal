import REWB.MaskedPeriodicAP
import REWB.MaskedCutTuples

/-! DFA meaning of the three periodic arithmetic families. One `Joint`
    value carries the B pref, C suffix and E suffix maps together.
    The following tuple adapter proves that joint values are obtained
    from one actual cut, including the positive-cut and eta constraints.
-/
namespace REWB.MaskedPeriodic
open REWB.MaskedFiniteAction.Maps
open REWB.MaskedCut.DFAIndex
open REWB.Periodic (repeatWord)
variable {α : Type}

def wordTuple (b c e : DFA α) (pref cSuffix eSuffix : Word α) : Joint b c e :=
  (wordMap b pref,wordMap c cSuffix,wordMap e eSuffix)

def fromTuple (b c e : DFA α) (period cut : Joint b c e) (after : Map e.stateCount) :
    Data b.stateCount c.stateCount e.stateCount :=
  ⟨ofMaps b period.1 (identity b.stateCount) cut.1,
   ofMaps c period.2.1 cut.2.1 (identity c.stateCount),
   ofMaps e period.2.2 cut.2.2 after⟩

def WordFamily (b c e : DFA α) (V pref cSuffix eSuffix after : Word α)
    (branch : Branch) (N a k : Nat) : Prop :=
  Geometry branch N a k ∧ b.accepts (repeatWord V a++pref) ∧
    c.accepts (cSuffix++repeatWord V (k-a-branch.carry)) ∧
    e.accepts (eSuffix++repeatWord V (tailCount branch N a k)++after)

theorem fromTuple_words (b c e : DFA α) (V pref cSuffix eSuffix after : Word α)
    (branch : Branch) (N a k : Nat) :
    Accepts (fromTuple b c e (jointWord b c e V)
      (wordTuple b c e pref cSuffix eSuffix) (wordMap e after)) branch N a k ↔
        WordFamily b c e V pref cSuffix eSuffix after branch N a k := by
  have hb := ofMaps_word b V [] pref a
  have hc := ofMaps_word c V cSuffix [] (k-a-branch.carry)
  have he := ofMaps_word e V eSuffix after (tailCount branch N a k)
  simp only [List.nil_append,List.append_nil] at hb hc
  change (Geometry branch N a k ∧ _ ∧ _ ∧ _) ↔ (Geometry branch N a k ∧ _ ∧ _ ∧ _)
  exact and_congr_right (fun _=>and_congr hb (and_congr hc he))

theorem zero_family (b c e : DFA α) (V fragment tail : Word α) (N a k : Nat) :
    Accepts (fromTuple b c e (jointWord b c e V) (wordTuple b c e [] [] [])
      (wordMap e (fragment++tail))) .zero N a k ↔
        2≤a ∧ a≤k ∧ k+a≤N ∧ b.accepts (repeatWord V a) ∧
          c.accepts (repeatWord V (k-a)) ∧
          e.accepts (repeatWord V (N-k-a)++fragment++tail) := by
  rw [fromTuple_words]
  simp only [WordFamily,Geometry,Branch.carry,Branch.endOK,tailCount,
    Nat.add_zero,Nat.sub_zero,List.append_nil,List.nil_append,List.append_assoc]
  constructor
  · rintro ⟨⟨ha,hk,hn⟩,hb,hc,he⟩
    exact ⟨ha,hk,hn,hb,hc,he⟩
  · rintro ⟨ha,hk,hn,hb,hc,he⟩
    exact ⟨⟨ha,hk,hn⟩,hb,hc,he⟩

theorem interior_family (b c e : DFA α) (V pref suffix fragment tail : Word α)
    (N a k : Nat) :
    Accepts (fromTuple b c e (jointWord b c e V)
      (wordTuple b c e pref suffix suffix) (wordMap e (fragment++tail))) .interior N a k ↔
        2≤a ∧ a+1≤k ∧ k+a<N ∧ b.accepts (repeatWord V a++pref) ∧
          c.accepts (suffix++repeatWord V (k-a-1)) ∧
          e.accepts (suffix++repeatWord V (N-k-a-1)++fragment++tail) := by
  rw [fromTuple_words]
  simp only [WordFamily,Geometry,Branch.carry,Branch.endOK,tailCount,List.append_assoc]
  constructor
  · rintro ⟨⟨ha,hk,hn⟩,hb,hc,he⟩
    exact ⟨ha,hk,by omega,hb,hc,he⟩
  · rintro ⟨ha,hk,hn,hb,hc,he⟩
    exact ⟨⟨ha,hk,by omega⟩,hb,hc,he⟩

theorem ending_family (b c e : DFA α) (V pref suffix shortSuffix tail : Word α)
    (N a k : Nat) :
    Accepts (fromTuple b c e (jointWord b c e V)
      (wordTuple b c e pref suffix shortSuffix) (wordMap e tail)) .ending N a k ↔
        2≤a ∧ a+1≤k ∧ k+a=N ∧ b.accepts (repeatWord V a++pref) ∧
          c.accepts (suffix++repeatWord V (k-a-1)) ∧ e.accepts (shortSuffix++tail) := by
  rw [fromTuple_words]
  simp only [WordFamily,Geometry,Branch.carry,Branch.endOK,tailCount,repeatWord,
    List.append_nil]
  constructor
  · rintro ⟨⟨ha,hk,hn⟩,hb,hc,he⟩
    exact ⟨ha,hk,hn,hb,hc,he⟩
  · rintro ⟨ha,hk,hn,hb,hc,he⟩
    exact ⟨⟨ha,hk,hn⟩,hb,hc,he⟩

end REWB.MaskedPeriodic
