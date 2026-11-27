import REWB.MaskedPeriodicTuples

/-! Executable within-run queries over fixed-universe joint cut tuples.
    A phase supplies materialized whole-period and common-tail maps.
    Actual index queries discover realizable positive-cut tuples; the
    finite-orbit/projected-AP compiler handles each such joint tuple.
    No loop here enumerates rho, a, k, or target mask positions.

    The mask-query counter below excludes construction of descriptors,
    projected syntax and windows; the projection and cut-index counters
    are exposed separately in the preceding modules. This is not a
    complete masked-index preparation or global runtime theorem.
-/
namespace REWB.MaskedPeriodic
open REWB.MaskedFiniteAction.Maps REWB.MaskedCut REWB.MaskedCut.DFAIndex REWB.Spec
variable {α : Type}

def Marked (mask : Array Bool) (base len q s k : Nat) : Prop :=
  base≤s+k*q ∧ s+k*q<base+len ∧ MaskedProgression.readMask mask (s+k*q)=true

def tupleQuery (b c e : DFA α) (period : Joint b c e) (after : Map e.stateCount)
    (branch : Branch) (N : Nat) (counts : Array Nat) (base q s : Nat)
    (cuts : List (Joint b c e)) (K : Nat := modulus b.stateCount c.stateCount e.stateCount) :
    MaskedProgression.Answer :=
  match cuts with
  | [] => ⟨false,0,1⟩
  | cut::rest =>
    let head := queryBranch (fromTuple b c e period cut after) branch N counts base q s K
    let tail := tupleQuery b c e period after branch N counts base q s rest K
    ⟨head.answer || tail.answer,head.slots+tail.slots,head.arithmetic+tail.arithmetic+1⟩

theorem tupleQuery_correct (b c e : DFA α) (period : Joint b c e) (after : Map e.stateCount)
    (branch : Branch) (N : Nat) (mask : Array Bool) (base len q s : Nat)
    (cuts : List (Joint b c e)) (hq : 0<q) :
    (tupleQuery b c e period after branch N
      (MaskedProgression.build mask base len (modulus b.stateCount c.stateCount e.stateCount*q)).counts
      base q s cuts).answer=true ↔
        ∃ cut,cut∈cuts ∧ ∃ a k,Accepts (fromTuple b c e period cut after) branch N a k ∧
          Marked mask base len q s k := by
  induction cuts with
  | nil => simp [tupleQuery]
  | cons cut cuts ih =>
    simp only [tupleQuery,Bool.or_eq_true,queryBranch_correct _ _ _ _ _ _ _ _ hq,ih]
    constructor
    · rintro (⟨a,k,ha,hm⟩|⟨cut',hc,a,k,ha,hm⟩)
      · exact ⟨cut,List.mem_cons_self,a,k,ha,hm⟩
      · exact ⟨cut',List.mem_cons.mpr (Or.inr hc),a,k,ha,hm⟩
    · rintro ⟨cut',hc,a,k,ha,hm⟩
      rcases List.mem_cons.mp hc with he|hc
      · subst cut'
        exact Or.inl ⟨a,k,ha,hm⟩
      · exact Or.inr ⟨cut',hc,a,k,ha,hm⟩

def tupleWork (b c e : Nat) : Nat := 47*(modulus b c e*syntaxBudget b c e)+2

theorem tupleQuery_work (b c e : DFA α) (period : Joint b c e) (after : Map e.stateCount)
    (branch : Branch) (N : Nat) (counts : Array Nat) (base q s : Nat)
    (cuts : List (Joint b c e)) :
    (tupleQuery b c e period after branch N counts base q s cuts).slots+
      (tupleQuery b c e period after branch N counts base q s cuts).arithmetic≤
        tupleWork b.stateCount c.stateCount e.stateCount*cuts.length+1 := by
  induction cuts with
  | nil => simp [tupleQuery]
  | cons cut cuts ih =>
    have hh := queryBranch_work (fromTuple b c e period cut after) branch N counts base q s
    simp only [tupleQuery,List.length_cons,Nat.mul_add,Nat.mul_one]
    unfold tupleWork at ih ⊢
    omega

structure IndexedAnswer where
  result : MaskedProgression.Answer
  products : Nat
  visits : Nat

def queryInterior (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start q : Nat) (period : Joint b c e) (after : Map e.stateCount) (N : Nat)
    (counts : Array Nat) (base s : Nat)
    (K : Nat := modulus b.stateCount c.stateCount e.stateCount) : IndexedAnswer :=
  let cuts := interiorTuples b c e idx start q
  ⟨tupleQuery b c e period after .interior N counts base q s cuts.values K,cuts.products,cuts.visits⟩

def queryEnding (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start eta q : Nat) (period : Joint b c e) (tail : Map e.stateCount) (N : Nat)
    (counts : Array Nat) (base s : Nat)
    (K : Nat := modulus b.stateCount c.stateCount e.stateCount) : IndexedAnswer :=
  let cuts := endingTuples b c e idx start eta q
  ⟨tupleQuery b c e period tail .ending N counts base q s cuts.values K,cuts.products,cuts.visits⟩

theorem queryInterior_cached (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start q : Nat) (period : Joint b c e) (after : Map e.stateCount) (N : Nat)
    (counts : Array Nat) (base s : Nat) (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount) :
    queryInterior b c e idx start q period after N counts base s prepared.K=
      queryInterior b c e idx start q period after N counts base s := by rw [prepared.exact]

theorem queryEnding_cached (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start eta q : Nat) (period : Joint b c e) (tail : Map e.stateCount) (N : Nat)
    (counts : Array Nat) (base s : Nat) (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount) :
    queryEnding b c e idx start eta q period tail N counts base s prepared.K=
      queryEnding b c e idx start eta q period tail N counts base s := by rw [prepared.exact]

theorem queryInterior_correct (b c e : DFA α) (w after : Word α)
    (start q N : Nat) (mask : Array Bool) (base len s : Nat)
    (hq : 0<q) (hn : start+q≤w.length) :
    (queryInterior b c e (DFAIndex.build b c e w).1 start q
      (jointWord b c e (slice w start (start+q))) (wordMap e after) N
      (MaskedProgression.build mask base len (modulus b.stateCount c.stateCount e.stateCount*q)).counts
      base s).result.answer=true ↔
        ∃ rho a k,0<rho ∧ rho<q ∧
          WordFamily b c e (slice w start (start+q)) (slice w start (start+rho))
            (slice w (start+rho) (start+q)) (slice w (start+rho) (start+q)) after
            .interior N a k ∧ Marked mask base len q s k := by
  unfold queryInterior
  rw [tupleQuery_correct _ _ _ _ _ _ _ _ _ _ _ _ _ hq]
  constructor
  · rintro ⟨cut,hcut,a,k,ha,hm⟩
    obtain ⟨rho,hlo,hhi,he⟩ := (interiorTuples_correct b c e w start q hn cut).mp hcut
    rw [←he,fromTuple_words] at ha
    exact ⟨rho,a,k,hlo,hhi,ha,hm⟩
  · rintro ⟨rho,a,k,hlo,hhi,ha,hm⟩
    refine ⟨wordTuple b c e (slice w start (start+rho))
      (slice w (start+rho) (start+q)) (slice w (start+rho) (start+q)),?_,a,k,?_,hm⟩
    · exact (interiorTuples_correct b c e w start q hn _).mpr ⟨rho,hlo,hhi,rfl⟩
    · exact (fromTuple_words _ _ _ _ _ _ _ _ _ _ _ _).mpr ha

theorem queryEnding_correct (b c e : DFA α) (w tail : Word α)
    (start eta q N : Nat) (mask : Array Bool) (base len s : Nat)
    (hq : 0<q) (he : eta≤q) (hn : start+q≤w.length) :
    (queryEnding b c e (DFAIndex.build b c e w).1 start eta q
      (jointWord b c e (slice w start (start+q))) (wordMap e tail) N
      (MaskedProgression.build mask base len (modulus b.stateCount c.stateCount e.stateCount*q)).counts
      base s).result.answer=true ↔
        ∃ rho a k,0<rho ∧ rho≤eta ∧
          WordFamily b c e (slice w start (start+q)) (slice w start (start+rho))
            (slice w (start+rho) (start+q)) (slice w (start+rho) (start+eta)) tail
            .ending N a k ∧ Marked mask base len q s k := by
  unfold queryEnding
  rw [tupleQuery_correct _ _ _ _ _ _ _ _ _ _ _ _ _ hq]
  constructor
  · rintro ⟨cut,hcut,a,k,ha,hm⟩
    obtain ⟨rho,hlo,hhi,hcut⟩ := (endingTuples_correct b c e w start eta q he hn cut).mp hcut
    rw [←hcut,fromTuple_words] at ha
    exact ⟨rho,a,k,hlo,hhi,ha,hm⟩
  · rintro ⟨rho,a,k,hlo,hhi,ha,hm⟩
    refine ⟨wordTuple b c e (slice w start (start+rho))
      (slice w (start+rho) (start+q)) (slice w (start+rho) (start+eta)),?_,a,k,?_,hm⟩
    · exact (endingTuples_correct b c e w start eta q he hn _).mpr ⟨rho,hlo,hhi,rfl⟩
    · exact (fromTuple_words _ _ _ _ _ _ _ _ _ _ _ _).mpr ha

theorem queryInterior_mask_work (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start q : Nat) (period : Joint b c e) (after : Map e.stateCount) (N : Nat)
    (counts : Array Nat) (base s : Nat) :
    (queryInterior b c e idx start q period after N counts base s).result.slots+
      (queryInterior b c e idx start q period after N counts base s).result.arithmetic≤
        tupleWork b.stateCount c.stateCount e.stateCount*(jointEnum b c e).elems.length+1 := by
  have hh := tupleQuery_work b c e period after .interior N counts base q s
    (interiorTuples b c e idx start q).values
  have hl := Nat.mul_le_mul_left (tupleWork b.stateCount c.stateCount e.stateCount)
    (interiorTuples_size b c e idx start q)
  exact Nat.le_trans hh (by omega)

theorem queryEnding_mask_work (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start eta q : Nat) (period : Joint b c e) (tail : Map e.stateCount) (N : Nat)
    (counts : Array Nat) (base s : Nat) :
    (queryEnding b c e idx start eta q period tail N counts base s).result.slots+
      (queryEnding b c e idx start eta q period tail N counts base s).result.arithmetic≤
        tupleWork b.stateCount c.stateCount e.stateCount*(jointEnum b c e).elems.length+1 := by
  have hh := tupleQuery_work b c e period tail .ending N counts base q s
    (endingTuples b c e idx start eta q).values
  have hl := Nat.mul_le_mul_left (tupleWork b.stateCount c.stateCount e.stateCount)
    (endingTuples_size b c e idx start eta q)
  exact Nat.le_trans hh (by omega)

end REWB.MaskedPeriodic
