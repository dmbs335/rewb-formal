import REWB.BoundaryTrieKeys
import REWB.BoundaryTrieSort

/-! Actual preparation of descriptor keys over an already materialized
text. The exact rank index is built once, the measured comparator sort
reuses it, and the sorted descriptors are materialized as one array.
No represented substring is copied or traversed. -/
namespace REWB.BoundaryTrie

structure Prepared (n : Nat) (ρ : Type) where
  ranks : RankIndex.Index
  keys : Array (Key n ρ)
  work : Nat
  deriving Repr

variable {σ : Nat} {ρ : Type}

def prepare (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) : Prepared text.size ρ :=
  let ranks:=LCEIndex.prepare (ArrayText.read text fallback) text.size
  let s:=Sort.sort (compare text fallback ranks) descriptors
  let keys:=s.1.toArray
  ⟨ranks,keys,ranks.countedWork+s.2+keys.size+1⟩

theorem prepare_ranks (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) :
    (prepare text fallback descriptors).ranks=
      LCEIndex.prepare (ArrayText.read text fallback) text.size := rfl

theorem prepare_keys (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) :
    (prepare text fallback descriptors).keys.toList=
      (Sort.sort (compare text fallback
        (LCEIndex.prepare (ArrayText.read text fallback) text.size)) descriptors).1 := by
  simp only [prepare,List.toList_toArray]

theorem prepare_perm (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) :
    (prepare text fallback descriptors).keys.toList.Perm descriptors := by
  rw [prepare_keys]
  exact Sort.sort_perm _ _

theorem prepare_length (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) :
    (prepare text fallback descriptors).keys.size=descriptors.length := by
  simp only [prepare,List.size_toArray,Sort.sort_length]

theorem prepare_mem (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) (a : Key text.size ρ) :
    a∈(prepare text fallback descriptors).keys.toList ↔ a∈descriptors :=
  (prepare_perm text fallback descriptors).mem_iff

theorem prepare_sorted (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) :
    (prepare text fallback descriptors).keys.toList.Pairwise
      (Key.ordered (ArrayText.read text fallback)) := by
  let ranks:=LCEIndex.prepare (ArrayText.read text fallback) text.size
  let cmp : Key text.size ρ→Key text.size ρ→Bool×Nat:=compare text fallback ranks
  have hcmp : ∀ a b,Sort.order cmp a b=true ↔
      Key.ordered (ArrayText.read text fallback) a b := fun a b=>compare_correct text fallback a b
  have ht : ∀ a b c,Sort.order cmp a b→Sort.order cmp b c→Sort.order cmp a c := by
    intro a b c hab hbc
    exact (hcmp a c).mpr (Key.ordered_trans _ a b c ((hcmp a b).mp hab) ((hcmp b c).mp hbc))
  have ho : ∀ a b,Sort.order cmp a b || Sort.order cmp b a := by
    intro a b
    rcases Key.ordered_total (ArrayText.read text fallback) a b with hab | hba
    · simp only [(hcmp a b).mpr hab,Bool.true_or]
    · simp only [(hcmp b a).mpr hba,Bool.or_true]
  rw [prepare_keys]
  exact (Sort.sort_sorted cmp ht ho descriptors).imp (fun h=>(hcmp _ _).mp h)

theorem prepare_commonPrefix (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) (a b : Key text.size ρ) :
    Key.Exact (ArrayText.read text fallback) a b
      (commonPrefix (prepare text fallback descriptors).ranks a b).1 := by
  rw [prepare_ranks]
  exact commonPrefix_correct _ a b

/-- The first term is the existing exact rank-index construction; the
second is the actual variable-cost descriptor sort; the last term charges
the descriptor array materialization and fixed return. -/
theorem prepare_work (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) :
    (prepare text fallback descriptors).work≤
      (text.size+1)*((text.size.log2+1)*(16*RankIndex.width σ text.size+4)+1)+
      (13*(text.size.log2+1)+12)*(8*descriptors.length*(descriptors.length.log2+1))+
      descriptors.length+1 := by
  let ranks:=LCEIndex.prepare (ArrayText.read text fallback) text.size
  have hr:=LCEIndex.prepare_work (ArrayText.read text fallback) text.size
  have hs:=Sort.sort_steps (compare text fallback ranks) (13*(text.size.log2+1)+11)
    (fun a b=>compare_work text fallback ranks a b) descriptors
  have hs' : (Sort.sort (compare text fallback ranks) descriptors).2≤
      (13*(text.size.log2+1)+12)*(8*descriptors.length*(descriptors.length.log2+1)) := hs
  simp only [prepare,List.size_toArray,Sort.sort_length]
  change ranks.countedWork+(Sort.sort (compare text fallback ranks) descriptors).2+
    descriptors.length+1≤_
  change ranks.countedWork≤_ at hr
  omega

end REWB.BoundaryTrie
