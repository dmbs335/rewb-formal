import REWB.BoundaryTriePartition
import REWB.BoundaryTriePrepare
import Init.Data.List.Nat.Pairwise

/-! Specification lists for array intervals. Executable trie construction
uses the array directly; these lists describe the keys carried by a
subtree and are not traversed or constructed by that execution. -/
namespace REWB.BoundaryTrie
variable {σ n : Nat} {ρ : Type}

def entries (xs : Array (Key n ρ)) (fallback : Key n ρ) (lo hi : Nat) : List (Key n ρ) :=
  (List.range' lo (hi-lo)).map (Partition.keyAt xs fallback)

theorem entries_length (xs : Array (Key n ρ)) (fallback : Key n ρ) (lo hi : Nat) :
    (entries xs fallback lo hi).length=hi-lo := by
  simp only [entries,List.length_map,List.length_range']

theorem entries_empty (xs : Array (Key n ρ)) (fallback : Key n ρ) (lo : Nat) :
    entries xs fallback lo lo=[] := by simp [entries]

theorem entries_one (xs : Array (Key n ρ)) (fallback : Key n ρ) (lo : Nat) :
    entries xs fallback lo (lo+1)=[Partition.keyAt xs fallback lo] := by
  rw [entries,show lo+1-lo=1 by omega]
  rfl

theorem entries_append (xs : Array (Key n ρ)) (fallback : Key n ρ) (lo mid hi : Nat)
    (hlo : lo≤mid) (hmid : mid≤hi) :
    entries xs fallback lo hi=entries xs fallback lo mid++entries xs fallback mid hi := by
  have hsum : hi-lo=(mid-lo)+(hi-mid) := by omega
  have hstart : lo+(mid-lo)=mid := by omega
  simp only [entries]
  rw [hsum,← List.range'_append_1,hstart,List.map_append]

theorem entries_mem (xs : Array (Key n ρ)) (fallback : Key n ρ) (lo hi : Nat)
    (a : Key n ρ) :
    a∈entries xs fallback lo hi ↔
      ∃ i,lo≤i ∧ i<hi ∧ Partition.keyAt xs fallback i=a := by
  simp only [entries,List.mem_map]
  constructor
  · rintro ⟨i,hi',he⟩
    obtain ⟨j,hj,hij⟩:=List.mem_range'.mp hi'
    simp only [Nat.one_mul] at hij
    exact ⟨i,by omega,by omega,he⟩
  · rintro ⟨i,hil,hih,he⟩
    refine ⟨i,List.mem_range'.mpr ⟨i-lo,by omega,?_⟩,he⟩
    omega

theorem entries_full (xs : Array (Key n ρ)) (fallback : Key n ρ) :
    entries xs fallback 0 xs.size=xs.toList := by
  apply List.ext_getElem
  · simp only [entries_length,Nat.sub_zero,Array.length_toList]
  · intro i hi hj
    have hb : i<xs.size := by simpa only [Array.length_toList] using hj
    simp only [entries,List.getElem_map,List.getElem_range',Nat.one_mul,Nat.zero_add,
      Partition.keyAt,Array.getElem?_eq_getElem hb,Option.getD_some,Array.getElem_toList]

theorem indexed_sorted (f : Nat→Fin σ) (xs : Array (Key n ρ)) (fallback : Key n ρ)
    (hs : xs.toList.Pairwise (Key.ordered f)) : Partition.Sorted f xs fallback := by
  intro i j hij hj
  by_cases he : i=j
  · subst j
    exact (Key.ordered_total f (Partition.keyAt xs fallback i)
      (Partition.keyAt xs fallback i)).elim id id
  · have hi : i<xs.size := by omega
    have hr:=(List.pairwise_iff_getElem.mp hs) i j
      (by simpa only [Array.length_toList] using hi)
      (by simpa only [Array.length_toList] using hj) (by omega)
    simpa only [Partition.keyAt,Array.getElem?_eq_getElem hi,
      Array.getElem?_eq_getElem hj,Option.getD_some,Array.getElem_toList] using hr

theorem prepare_indexed_sorted (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) (defaultKey : Key text.size ρ) :
    Partition.Sorted (ArrayText.read text fallback)
      (prepare text fallback descriptors).keys defaultKey :=
  indexed_sorted _ _ _ (prepare_sorted text fallback descriptors)

end REWB.BoundaryTrie
