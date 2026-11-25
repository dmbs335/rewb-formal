import REWB.BoundaryApplicationJump

/-! The executable fixed-end heavy index: build the normal D versions,
one shared A range index, one shared bounded-cut index, the subset path
versions, and direct source/head-jump arrays. The subset and address
passes each visit a trie node once. Neither scans a retained heavy list
or reconstructs a source path. -/
namespace REWB.BoundaryApplication.HeavyIndex
open REWB.BoundaryIndex
variable {σ : Nat}

def base (k : Nat) (E : DFA (Fin σ)) (w : Word (Fin σ)) :=
  MergeBuild.prepare (k:=k) (FixedEnd.rows E w) (height w.length)

structure Index (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) where
  normal : FixedEnd.Index D E w
  ranges : Range.Index A
  cuts : RTable.Shared A B D
  paths : Heavy.Result A D E w.length
  addresses : Address.Store A D E w.length
  cachedLength : Nat
  length_eq : cachedLength=w.length
  work : Nat

def inputWork (n m : Nat) : Nat := 2*n+(n+1)*m+6

def build (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) : Index A B D E w :=
  let normal:=FixedEnd.build D E w fallback g hg
  let ranges:=Range.build A w
  let cuts:=RTable.prepare A B D w
  let b:=base (Subset.count A) E w
  let paths:=Heavy.go A B D E w cuts ranges b.1 normal.trie.tree normal.versions (Heavy.blank b.1)
  let addresses:=Address.build paths.saved
  ⟨normal,ranges,cuts,paths,addresses,w.length,rfl,
    normal.work+ranges.products*A.stateCount+ranges.letterCells+cuts.buildProducts+
      b.2+paths.work+addresses.work+inputWork w.length E.stateCount⟩

theorem build_good (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) : Address.Good (build A B D E w fallback g hg).addresses.nodes :=
  Address.build_good _

theorem build_slots (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) : Address.SlotsGood (build A B D E w fallback g hg).addresses :=
  Address.build_slots _

theorem build_source (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (p : Fin (w.length+1)) (hp : p.val≤g) :
    ∃i,(build A B D E w fallback g hg).addresses.sources.get p=some i := by
  apply (Address.build_source_exists _ p).mpr
  apply (Address.go_source A B D E w _ _ _ _ _ _ p).mpr
  exact FixedEnd.trie_source w fallback g hg p hp

theorem build_stored (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) :
    Address.Stored (Heavy.EntryGood A D E w.length (base D.stateCount E w).1
      (base (Subset.count A) E w).1) (build A B D E w fallback g hg).addresses.nodes := by
  apply Address.build_stored
  exact Heavy.go_all A B D E w _ _ _ _ (MergeBuild.prepare_good _ _) (MergeBuild.prepare_blank _ _)
    _ (MergeBuild.prepare_good _ _) (MergeBuild.prepare_blank _ _) _ _
    (Heavy.blank_good _ (MergeBuild.prepare_good _ _) (MergeBuild.prepare_blank _ _))

theorem build_rank (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) :
    Address.Bounded (build A B D E w fallback g hg).addresses.nodes (w.length+2).log2 := by
  have hh:=Heavy.lightHeight_bound A B D E w (RTable.prepare A B D w) (Range.build A w) (Range.build D w)
    (base (Subset.count A) E w).1 (base D.stateCount E w).1 fallback (FixedEnd.trie w fallback g hg).tree
    (FixedEnd.trie_good w fallback g hg) (FixedEnd.trie_nonempty w fallback g hg) (Heavy.blank (base (Subset.count A) E w).1)
  rw [FixedEnd.trie_length] at hh
  have hb:=Address.build_bounded (build A B D E w fallback g hg).paths.saved
  intro i c hc
  exact Nat.le_trans (hb i c hc) hh

theorem build_imports (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) :
    (build A B D E w fallback g hg).paths.imports≤(w.length+2)*(w.length+2).log2+(w.length+2) := by
  have hh:=Heavy.imports_bound A B D E w (RTable.prepare A B D w) (Range.build A w) (Range.build D w)
    (base (Subset.count A) E w).1 (base D.stateCount E w).1 fallback (FixedEnd.trie w fallback g hg).tree
    (FixedEnd.trie_good w fallback g hg) (FixedEnd.trie_nonempty w fallback g hg) (Heavy.blank (base (Subset.count A) E w).1)
  rwa [FixedEnd.trie_length] at hh

theorem build_nodes (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) :
    (build A B D E w fallback g hg).addresses.nodes.size≤2*(w.length+2) := by
  change (Address.build _).nodes.size≤_
  rw [Address.build_size,Address.go_nodes,Heavy.allocated A B D E w fallback]
  · exact FixedEnd.trie_nodes w fallback g hg
  · exact FixedEnd.trie_good w fallback g hg
  · exact FixedEnd.trie_nonempty w fallback g hg

def baseBudget (k m n : Nat) : Nat :=
  (n+1)*(k*m+1)+2*(n+2)*(Tree.joinBudget k m+Tree.leafBudget k m)

theorem base_steps (k : Nat) (E : DFA (Fin σ)) (w : Word (Fin σ)) :
    (base k E w).2≤baseBudget k E.stateCount w.length := by
  have hb:=MergeBuild.prepare_steps (k:=k) (FixedEnd.rows E w) (height w.length)
  have hc:=Nat.mul_le_mul_right (Tree.joinBudget k E.stateCount+Tree.leafBudget k E.stateCount)
    (Tree.capacity_upper (w.length+1))
  rw [FixedEnd.rows_size] at hb
  rw [show w.length+1+1=w.length+2 by omega] at hc
  change (base k E w).2+_=_ at hb
  change 2^(height w.length)*_≤_ at hc
  unfold baseBudget
  omega

def bound (A B D E : DFA (Fin σ)) (n : Nat) : Nat :=
  FixedEnd.bound σ D.stateCount E.stateCount n+((n.log2+1)*n)*A.stateCount+n*A.stateCount+
    2*((n.log2+1)*n)+baseBudget (Subset.count A) E.stateCount n+
    2*(n+2)*Heavy.nodeBudget A B D E n+
    ((n+2)*(n+2).log2+(n+2))*Lift.budget D.stateCount (Subset.count A) E.stateCount (height n)+
    (n+2+24*(n+2))+inputWork n E.stateCount

theorem build_work (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) :
    (build A B D E w fallback g hg).work≤bound A B D E w.length := by
  let normal:=FixedEnd.build D E w fallback g hg
  let paths:=(build A B D E w fallback g hg).paths
  let addresses:=(build A B D E w fallback g hg).addresses
  have hn:=FixedEnd.build_work D E w fallback g hg
  change normal.work≤_ at hn
  have hb:=base_steps (Subset.count A) E w
  have hh:=Heavy.work_bound A B D E w fallback (Range.build D w)
    (base (Subset.count A) E w).1 (base D.stateCount E w).1 (FixedEnd.trie w fallback g hg).tree
    (FixedEnd.trie_good w fallback g hg) (FixedEnd.trie_nonempty w fallback g hg) (Heavy.blank (base (Subset.count A) E w).1)
  rw [FixedEnd.trie_length] at hh
  have hnodes:=Nat.mul_le_mul_right (Heavy.nodeBudget A B D E w.length) (FixedEnd.trie_nodes w fallback g hg)
  have hpaths : paths.work≤2*(w.length+2)*Heavy.nodeBudget A B D E w.length+
      ((w.length+2)*(w.length+2).log2+(w.length+2))*
        Lift.budget D.stateCount (Subset.count A) E.stateCount (height w.length) := by
    change paths.work≤_ at hh
    omega
  have ha:=Address.build_work paths.saved
  have hsize:=build_nodes A B D E w fallback g hg
  change (Address.build paths.saved).nodes.size≤_ at hsize
  rw [Address.build_size] at hsize
  have haddr : addresses.work≤w.length+2+24*(w.length+2) := by
    change addresses.work=_ at ha
    omega
  have hcut : (RTable.prepare A B D w).buildProducts=2*((w.length.log2+1)*w.length) :=
    BoundaryIndex.FixedEnd.build_products A B D w
  change normal.work+(Range.build A w).products*A.stateCount+(Range.build A w).letterCells+
    (RTable.prepare A B D w).buildProducts+(base (Subset.count A) E w).2+paths.work+addresses.work+
      inputWork w.length E.stateCount≤_
  rw [Range.build_products,hcut]
  change normal.work+((w.length.log2+1)*w.length)*A.stateCount+w.length*A.stateCount+
    2*((w.length.log2+1)*w.length)+(base (Subset.count A) E w).2+paths.work+addresses.work+
      inputWork w.length E.stateCount≤_
  unfold bound
  omega

end REWB.BoundaryApplication.HeavyIndex
