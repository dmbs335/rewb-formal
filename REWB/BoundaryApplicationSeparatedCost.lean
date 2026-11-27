import REWB.BoundaryApplicationSeparatedQuery

/-! Total measured separated-boundary construction and logarithmic E
queries. The bound includes the actual exact-LCE/rank/sort trie builder,
shared range and cut indexes, both node passes, endpoint-vector writes,
and the static E tree. The scalar/map/matrix primitive model is inherited
from those executable components; this is not an allocator/bit theorem. -/
namespace REWB.BoundaryApplication.Separated
open REWB.BoundaryTrie
open REWB.BoundaryIndex
variable {σ : Nat}

def rangeBound (D : DFA (Fin σ)) (n : Nat) : Nat :=
  D.stateCount*((n.log2+1)*n)+n*D.stateCount+n+3

def cutBound (A B D : DFA (Fin σ)) (n : Nat) : Nat :=
  let z:=(MarkedTransfer.enum (BoundaryIndex.FixedEnd.leftDFA A D) B).elems.length
  2*((n.log2+1)*n)+2*(n+1)*(z*z)+3*n+4

theorem rangeBuildWork_build (D : DFA (Fin σ)) (w : Word (Fin σ)) :
    rangeBuildWork D (Range.build D w)=rangeBound D w.length := by
  unfold rangeBuildWork
  rw [Range.build_products]
  rfl

theorem cutBuildWork_prepare (A B D : DFA (Fin σ)) (w : Word (Fin σ)) :
    cutBuildWork A B D (RTable.prepare A B D w)=cutBound A B D w.length := by
  simp only [cutBuildWork,RTable.prepare,BoundaryIndex.FixedEnd.build_products,cutBound]

theorem trie_work (w : Word (Fin σ)) (fallback : Fin σ) (g0 g1 : Nat) (h1 : g1≤w.length) :
    (trie w fallback g0 g1 h1).work≤FixedEnd.trieBound σ w.length := by
  let N:=(keys w g0 g1 h1).length
  have hN : N≤w.length+2 := keys_length w g0 g1 h1
  have hl:=CountedJoin.log2_mono hN
  have hb : BoundaryTrie.Build.budget w.length N≤BoundaryTrie.Build.budget w.length (w.length+2) := by
    unfold BoundaryTrie.Build.budget
    omega
  have hsort:=Nat.mul_le_mul_left (13*(w.length.log2+1)+12)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hN) (Nat.add_le_add_right hl 1))
  have hnodes:=Nat.mul_le_mul (Nat.mul_le_mul_left 2 hN) hb
  have hh:=BoundaryTrie.Build.run_work (reversed w) fallback (keys w g0 g1 h1)
  change (trie w fallback g0 g1 h1).work≤
    ((reversed w).size+1)*(((reversed w).size.log2+1)*(16*RankIndex.width σ (reversed w).size+4)+1)+
    (13*((reversed w).size.log2+1)+12)*(8*N*(N.log2+1))+N+2+2*N*BoundaryTrie.Build.budget (reversed w).size N at hh
  conv at hh => rhs; rw [reversed_size]
  unfold FixedEnd.trieBound
  omega

def bitBound (A B C D : DFA (Fin σ)) (n : Nat) : Nat :=
  FixedEnd.trieBound σ n+rangeBound A n+rangeBound C n+rangeBound D n+cutBound A B D n+
    2*(n+2)*Summary.budget A C n+2*(n+2)*Pass.budget A D n+12*(n+2)+D.stateCount+10

theorem buildBits_work (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h01 : g0≤g1) (h1 : g1≤w.length) :
    (buildBits A B C D w fallback g0 g1 h1).work≤bitBound A B C D w.length := by
  let t:=trie w fallback g0 g1 h1
  let sources:=Summary.build A C w g0 (Range.build A w) (Range.build C w) t.tree
  let out:=Pass.go A B D (RTable.prepare A B D w) (Range.build D w) sources.1 0
    (Vector.ofFn (fun _=>false)) (Vector.ofFn (fun _=>false))
  have ht:=trie_work w fallback g0 g1 h1
  change t.work≤_ at ht
  have hg:=trie_good w fallback g0 g1 h1
  have hn:=trie_nonempty w fallback g0 g1 h1
  have hnodes : t.tree.nodes≤2*(w.length+2) :=
    Nat.le_trans (trie_nodes w fallback g0 g1 h1) (Nat.mul_le_mul_left 2 (keys_length w g0 g1 h1))
  have hs:=Summary.build_work A C w fallback g0 (by omega) t.tree hg hn
    (trie_source_bound w fallback g0 g1 h1)
  have hsb:=Nat.le_trans hs (Nat.mul_le_mul_right (Summary.budget A C w.length) hnodes)
  change sources.2≤_ at hsb
  have hshape : StartSummary.shape sources.1=t.tree := Summary.build_shape A C w g0 _ _ t.tree
  have hp:=Pass.go_work A B D w fallback sources.1 (by rw [hshape]; exact hg)
    (by rw [hshape]; exact hn) 0 (Nat.zero_le _) (Vector.ofFn (fun _=>false)) (Vector.ofFn (fun _=>false))
  rw [hshape] at hp
  have hpb:=Nat.le_trans hp (Nat.mul_le_mul_right (Pass.budget A D w.length) hnodes)
  change out.2≤_ at hpb
  change t.work+rangeBuildWork A (Range.build A w)+rangeBuildWork C (Range.build C w)+
    rangeBuildWork D (Range.build D w)+cutBuildWork A B D (RTable.prepare A B D w)+
    sources.2+out.2+12*(w.length+2)+D.stateCount+10≤_
  rw [rangeBuildWork_build,rangeBuildWork_build,rangeBuildWork_build,cutBuildWork_prepare]
  unfold bitBound
  omega

def bound (A B C D E : DFA (Fin σ)) (n : Nat) : Nat := bitBound A B C D n+Suffix.budget E n+3

theorem build_work (A B C D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (h01 : g0≤g1) (h1 : g1≤w.length) :
    (build A B C D E w fallback g0 g1 h1).work≤bound A B C D E w.length := by
  have hb:=buildBits_work A B C D w fallback g0 g1 h01 h1
  have hs:=Suffix.build_work E w (buildBits A B C D w fallback g0 g1 h1).bits
  change (buildBits A B C D w fallback g0 g1 h1).work+
    (Suffix.build E w (buildBits A B C D w fallback g0 g1 h1).bits).work+3≤_
  unfold bound
  omega

end REWB.BoundaryApplication.Separated
