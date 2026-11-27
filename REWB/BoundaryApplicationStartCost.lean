import REWB.BoundaryApplicationStartQuery

/-! Total measured fixed-start construction. The bound includes the
actual descriptor sorting/LCE trie builder, shared DFA/cut indexes,
source-summary and top-down passes, and cached parent rows. Counters
use the existing fixed-pattern range/matrix primitive model; this is
not a bit-complexity or allocator-cost theorem. -/
namespace REWB.BoundaryApplication.StartIndex
open REWB.BoundaryTrie
open REWB.BoundaryIndex
variable {σ : Nat}

def rangeBound (D : DFA (Fin σ)) (n : Nat) : Nat :=
  D.stateCount*((n.log2+1)*n)+n*D.stateCount+n+3

def cutBound (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  let z:=(MarkedTransfer.enum B (StartCuts.rightDFA C E)).elems.length
  (n.log2+1)*n+(n+1)*(z*z)+n+2

theorem rangeBuildWork_build (D : DFA (Fin σ)) (w : Word (Fin σ)) :
    rangeBuildWork D (Range.build D w)=rangeBound D w.length := by
  unfold rangeBuildWork
  rw [Range.build_products]
  rfl

theorem cutBuildWork_build (B C E : DFA (Fin σ)) (w : Word (Fin σ)) :
    cutBuildWork B C E (StartCuts.build B C E w)=cutBound B C E w.length := by
  unfold cutBuildWork
  rw [StartCuts.build_products]
  rfl

def trieBound (σ n : Nat) : Nat :=
  (n+1)*((n.log2+1)*(16*RankIndex.width σ n+4)+1)+
    (13*(n.log2+1)+12)*(8*(n+2)*((n+2).log2+1))+
    (n+2)+2+2*(n+2)*BoundaryTrie.Build.budget n (n+2)

def bound (A B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  trieBound σ n+rangeBound A n+rangeBound B n+rangeBound C n+rangeBound E n+cutBound B C E n+
    2*(n+2)*StartSummary.budget A C n+2*(n+2)*StartPass.budget B C E n+
    (n+2)+2*(n+2)*(6*levels n+8)+3*n+E.stateCount+10

theorem build_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (hg : g≤w.length) : (build A B C E w fallback g hg).work≤bound A B C E w.length := by
  let trie:=BoundaryTrie.Build.run w.toArray fallback (StartKeys.forwardKeys w g hg)
  let summaries:=StartSummary.build A C w (Range.build A w) (Range.build C w) trie.tree
  let paths:=StartPass.go B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w)
    summaries.1 0 B.initial (Vector.ofFn (fun _=>false))
  have htGood:=trie_good w fallback g hg
  have htNon:=trie_nonempty w fallback g hg
  have htWork:=BoundaryTrie.Build.run_work w.toArray fallback (StartKeys.forwardKeys w g hg)
  conv at htWork => rhs; rw [StartKeys.forwardKeys_length,List.size_toArray]
  change trie.work≤trieBound σ w.length at htWork
  have htNodes:=(BoundaryTrie.Build.run_correct w.toArray fallback (StartKeys.forwardKeys w g hg)).2.2.1
  rw [StartKeys.forwardKeys_length] at htNodes
  change trie.tree.nodes≤2*(w.length+2) at htNodes
  have hsWork:=StartSummary.build_work A C w fallback trie.tree htGood htNon
  change summaries.2≤trie.tree.nodes*StartSummary.budget A C w.length at hsWork
  have hsBound:=Nat.le_trans hsWork (Nat.mul_le_mul_right (StartSummary.budget A C w.length) htNodes)
  have hsShape : StartSummary.shape summaries.1=trie.tree := StartSummary.build_shape A C w _ _ trie.tree
  have hpWork:=StartPass.go_work B C E w fallback summaries.1
    (by rw [hsShape]; exact htGood) (by rw [hsShape]; exact htNon) 0 (Nat.zero_le _) B.initial (Vector.ofFn (fun _=>false))
  rw [hsShape] at hpWork
  change paths.2≤trie.tree.nodes*StartPass.budget B C E w.length at hpWork
  have hpBound:=Nat.le_trans hpWork (Nat.mul_le_mul_right (StartPass.budget B C E w.length) htNodes)
  have hpNodes : paths.1.nodes≤2*(w.length+2) := build_nodes A B C E w fallback g hg
  have haWork:=StartLocate.build_work (levels w.toArray.size) paths.1
  have haBound:=Nat.mul_le_mul_right (6*levels w.length+8) hpNodes
  rw [List.size_toArray] at haWork
  change trie.work+rangeBuildWork A (Range.build A w)+rangeBuildWork B (Range.build B w)+
    rangeBuildWork C (Range.build C w)+rangeBuildWork E (Range.build E w)+
    cutBuildWork B C E (StartCuts.build B C E w)+summaries.2+paths.2+
    (StartLocate.build (levels w.toArray.size) paths.1).work+3*w.toArray.size+E.stateCount+10≤_
  rw [rangeBuildWork_build,rangeBuildWork_build,rangeBuildWork_build,rangeBuildWork_build,
    cutBuildWork_build]
  simp only [List.size_toArray]
  unfold bound
  omega

theorem build_nodes_exact (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (hg : g≤w.length) : (build A B C E w fallback g hg).paths.nodes+1=2*(w.length+2) := by
  have htNon:=trie_nonempty w fallback g hg
  have htGood:=trie_good w fallback g hg
  have hn:=StartPass.go_nodes B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w)
    (StartKeys.text w fallback)
    (StartSummary.build A C w (Range.build A w) (Range.build C w)
      (BoundaryTrie.Build.run w.toArray fallback (StartKeys.forwardKeys w g hg)).tree).1
    (by rw [StartSummary.build_shape]; exact htGood)
    (by rw [StartSummary.build_shape]; exact htNon) 0 B.initial (Vector.ofFn (fun _=>false))
  rw [StartSummary.build_shape] at hn
  have hkeys : StartKeys.forwardKeys w g hg≠[] := by
    intro he
    have hh:=StartKeys.forwardKeys_length w g hg
    rw [he,List.length_nil] at hh
    omega
  have ht:=BoundaryTrie.Build.run_nodes w.toArray fallback (StartKeys.forwardKeys w g hg) hkeys
  rw [StartKeys.forwardKeys_length] at ht
  exact (congrArg (fun x=>x+1) hn).trans ht

theorem build_addresses_exact (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (hg : g≤w.length) : (build A B C E w fallback g hg).addresses.cells.size+1=2*(w.length+2) := by
  have hh:=StartLocate.build_size (build A B C E w fallback g hg).levels (build A B C E w fallback g hg).paths
  exact (congrArg (fun x=>x+1) hh).trans (build_nodes_exact A B C E w fallback g hg)

end REWB.BoundaryApplication.StartIndex
