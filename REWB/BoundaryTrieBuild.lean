import REWB.BoundaryTrieTree
import REWB.BoundaryTrieEntries
import REWB.CountedJoin

/-! Executable descriptor-only compressed trie construction. Each
nontrivial sorted interval is split using one capped endpoint LCE and
one next-symbol binary search. No key word or subtree key list is built
by the recursion. The input descriptors, alphabet array, and rank index
are shared throughout construction. -/
namespace REWB.BoundaryTrie.Build
variable {σ n : Nat} {ρ : Type}

structure Result (n : Nat) (ρ : Type) where
  tree : Tree n ρ
  work : Nat
  deriving Repr

def go (text : Array (Fin σ)) (fallback : Fin σ) (ranks : RankIndex.Index)
    (xs : Array (Key text.size ρ)) (defaultKey : Key text.size ρ) :
    Nat→Nat→Nat→Result text.size ρ
  | 0,_,_ => ⟨.empty,1⟩
  | fuel+1,lo,hi =>
    if hi≤lo then ⟨.empty,1⟩
    else if hi=lo+1 then ⟨.leaf (Partition.keyAt xs defaultKey lo),3⟩
    else
      let p:=Partition.run text fallback ranks xs defaultKey lo hi
      let l:=go text fallback ranks xs defaultKey fuel lo p.split
      let r:=go text fallback ranks xs defaultKey fuel p.split hi
      ⟨.node (Partition.keyAt xs defaultKey lo) p.depth l.tree r.tree,l.work+r.work+p.work+7⟩

def budget (n N : Nat) : Nat := 13*(n.log2+1)+15*(N.log2+1)+30

theorem partition_budget (text : Array (Fin σ)) (fallback : Fin σ) (ranks : RankIndex.Index)
    (xs : Array (Key text.size ρ)) (defaultKey : Key text.size ρ) (lo hi : Nat)
    (hh : hi≤xs.size) :
    (Partition.run text fallback ranks xs defaultKey lo hi).work+7≤budget text.size xs.size := by
  have hp:=Partition.run_work text fallback ranks xs defaultKey lo hi
  have hl:=CountedJoin.log2_mono (by omega : hi-lo≤xs.size)
  unfold budget
  omega

theorem go_correct (text : Array (Fin σ)) (fallback : Fin σ)
    (xs : Array (Key text.size ρ)) (defaultKey : Key text.size ρ) (fuel lo hi : Nat)
    (hs : Partition.Sorted (ArrayText.read text fallback) xs defaultKey)
    (hlo : lo<hi) (hhi : hi≤xs.size) (hf : hi-lo≤fuel) :
    let r:=go text fallback (LCEIndex.prepare (ArrayText.read text fallback) text.size)
      xs defaultKey fuel lo hi
    r.tree.leaves=entries xs defaultKey lo hi ∧
      r.tree.Good (ArrayText.read text fallback) ∧
      r.tree.nodes+1=2*(hi-lo) ∧
      r.work≤r.tree.nodes*budget text.size xs.size := by
  induction fuel generalizing lo hi with
  | zero => omega
  | succ fuel ih =>
    have hempty : ¬hi≤lo := by omega
    rw [go,if_neg hempty]
    by_cases hone : hi=lo+1
    · rw [if_pos hone]
      refine ⟨?_,True.intro,?_,?_⟩
      · simp only [Tree.leaves,hone,entries_one]
      · simp only [Tree.nodes,hone]
        omega
      · simp only [Tree.nodes,Nat.one_mul,budget]
        omega
    · rw [if_neg hone]
      let f:=ArrayText.read text fallback
      let ranks:=LCEIndex.prepare f text.size
      let p:=Partition.run text fallback ranks xs defaultKey lo hi
      let l:=go text fallback ranks xs defaultKey fuel lo p.split
      let r:=go text fallback ranks xs defaultKey fuel p.split hi
      have hp : Partition.Spec f xs defaultKey lo hi p :=
        Partition.run_correct text fallback xs defaultKey lo hi (by omega) hhi hs
      have hl:=ih lo p.split hp.1 (by have hh:=hp.2.1; omega)
        (by have hh:=hp.2.1; omega)
      have hr:=ih p.split hi hp.2.1 hhi (by have hh:=hp.1; omega)
      change l.tree.leaves=entries xs defaultKey lo p.split ∧ l.tree.Good f ∧
        l.tree.nodes+1=2*(p.split-lo) ∧ l.work≤l.tree.nodes*budget text.size xs.size at hl
      change r.tree.leaves=entries xs defaultKey p.split hi ∧ r.tree.Good f ∧
        r.tree.nodes+1=2*(hi-p.split) ∧ r.work≤r.tree.nodes*budget text.size xs.size at hr
      change (Tree.node (Partition.keyAt xs defaultKey lo) p.depth l.tree r.tree).leaves=
          entries xs defaultKey lo hi ∧
        (Tree.node (Partition.keyAt xs defaultKey lo) p.depth l.tree r.tree).Good f ∧
        (Tree.node (Partition.keyAt xs defaultKey lo) p.depth l.tree r.tree).nodes+1=2*(hi-lo) ∧
        l.work+r.work+p.work+7≤
          (Tree.node (Partition.keyAt xs defaultKey lo) p.depth l.tree r.tree).nodes*
            budget text.size xs.size
      refine ⟨?_,?_,?_,?_⟩
      · rw [Tree.leaves,hl.1,hr.1]
        exact (entries_append xs defaultKey lo p.split hi
          (Nat.le_of_lt hp.1) (Nat.le_of_lt hp.2.1)).symm
      · refine ⟨hl.2.1,hr.2.1,?_,?_,?_,?_,?_⟩
        · intro he
          have hh:=congrArg List.length hl.1
          rw [he,List.length_nil,entries_length] at hh
          have hh':=hp.1
          omega
        · intro he
          have hh:=congrArg List.length hr.1
          rw [he,List.length_nil,entries_length] at hh
          have hh':=hp.2.1
          omega
        · rw [hl.1]
          exact (entries_mem xs defaultKey lo p.split _).mpr ⟨lo,Nat.le_refl _,hp.1,rfl⟩
        · intro a ha
          rw [hl.1,hr.1,← entries_append xs defaultKey lo p.split hi
            (Nat.le_of_lt hp.1) (Nat.le_of_lt hp.2.1)] at ha
          obtain ⟨i,hil,hir,he⟩:=(entries_mem xs defaultKey lo hi a).mp ha
          have hh:=hp.2.2.2.1 i hil hir
          rwa [he] at hh
        · intro a ha b hb
          rw [hl.1] at ha
          rw [hr.1] at hb
          obtain ⟨i,hil,hir,hei⟩:=(entries_mem xs defaultKey lo p.split a).mp ha
          obtain ⟨j,hjl,hjr,hej⟩:=(entries_mem xs defaultKey p.split hi b).mp hb
          have hh:=hp.2.2.2.2 i j hil hir hjl hjr
          rwa [hei,hej] at hh
      · simp only [Tree.nodes]
        have hh₁:=hl.2.2.1
        have hh₂:=hr.2.2.1
        have hb₁:=hp.1
        have hb₂:=hp.2.1
        omega
      · have hb:=partition_budget text fallback ranks xs defaultKey lo hi hhi
        change p.work+7≤budget text.size xs.size at hb
        have hh₁:=hl.2.2.2
        have hh₂:=hr.2.2.2
        simp only [Tree.nodes,Nat.add_mul,Nat.one_mul]
        omega

structure Index (n : Nat) (ρ : Type) where
  prepared : Prepared n ρ
  tree : Tree n ρ
  work : Nat
  deriving Repr

/-- The one preparation is retained for subsequent exact LCE queries.
The first input record supplies only an unreachable array fallback. -/
def run (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) : Index text.size ρ :=
  let p:=prepare text fallback descriptors
  match descriptors with
  | [] => ⟨p,.empty,p.work+1⟩
  | a::_ =>
    let r:=go text fallback p.ranks p.keys a p.keys.size 0 p.keys.size
    ⟨p,r.tree,p.work+r.work+1⟩

theorem run_prepared (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) :
    (run text fallback descriptors).prepared=prepare text fallback descriptors := by
  cases descriptors <;> rfl

theorem run_correct (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) :
    (run text fallback descriptors).tree.leaves.Perm descriptors ∧
      (run text fallback descriptors).tree.Good (ArrayText.read text fallback) ∧
      (run text fallback descriptors).tree.nodes≤2*descriptors.length ∧
      (run text fallback descriptors).work≤
        (prepare text fallback descriptors).work+
          2*descriptors.length*budget text.size descriptors.length+1 := by
  cases descriptors with
  | nil => simp only [run,Tree.leaves,Tree.Good,Tree.nodes,List.length_nil,
      Nat.mul_zero,Nat.zero_mul,Nat.add_zero, Nat.le_refl, true_and, List.Perm.refl]
  | cons a rest =>
    let p:=prepare text fallback (a::rest)
    have hn : 0<p.keys.size := by simp only [p,prepare_length,List.length_cons]; omega
    have hg:=go_correct text fallback p.keys a p.keys.size 0 p.keys.size
      (prepare_indexed_sorted text fallback (a::rest) a) hn (Nat.le_refl _) (by omega)
    rw [entries_full] at hg
    let r:=go text fallback p.ranks p.keys a p.keys.size 0 p.keys.size
    change r.tree.leaves=p.keys.toList ∧ r.tree.Good (ArrayText.read text fallback) ∧
      r.tree.nodes+1=2*(p.keys.size-0) ∧ r.work≤r.tree.nodes*budget text.size p.keys.size at hg
    have hsize : p.keys.size=(a::rest).length := prepare_length text fallback (a::rest)
    change r.tree.leaves.Perm (a::rest) ∧ r.tree.Good (ArrayText.read text fallback) ∧
      r.tree.nodes≤2*(a::rest).length ∧ p.work+r.work+1≤
        p.work+2*(a::rest).length*budget text.size (a::rest).length+1
    have hnodes : r.tree.nodes≤2*(a::rest).length := by
      have hh:=hg.2.2.1
      rw [hsize,Nat.sub_zero] at hh
      omega
    refine ⟨?_,hg.2.1,hnodes,?_⟩
    · rw [hg.1]
      exact prepare_perm text fallback (a::rest)
    · have hw:=hg.2.2.2
      rw [hsize] at hw
      have hb:=Nat.mul_le_mul_right (budget text.size (a::rest).length) hnodes
      omega

theorem run_nodes (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) (hn : descriptors≠[]) :
    (run text fallback descriptors).tree.nodes+1=2*descriptors.length := by
  cases descriptors with
  | nil => exact False.elim (hn rfl)
  | cons a rest =>
    let p:=prepare text fallback (a::rest)
    have hpos : 0<p.keys.size := by simp only [p,prepare_length,List.length_cons]; omega
    have hg:=go_correct text fallback p.keys a p.keys.size 0 p.keys.size
      (prepare_indexed_sorted text fallback (a::rest) a) hpos (Nat.le_refl _) (by omega)
    have hh:=hg.2.2.1
    rw [Nat.sub_zero] at hh
    exact hh.trans (congrArg (fun x=>2*x) (prepare_length text fallback (a::rest)))

theorem run_leaves (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) :
    (run text fallback descriptors).tree.leaves=(prepare text fallback descriptors).keys.toList := by
  cases descriptors with
  | nil => rfl
  | cons a rest =>
    let p:=prepare text fallback (a::rest)
    have hpos : 0<p.keys.size := by simp only [p,prepare_length,List.length_cons]; omega
    have hg:=go_correct text fallback p.keys a p.keys.size 0 p.keys.size
      (prepare_indexed_sorted text fallback (a::rest) a) hpos (Nat.le_refl _) (by omega)
    have hh:=hg.1
    rw [entries_full] at hh
    exact hh

theorem run_paths (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) (a : Key text.size ρ) :
    (∃path,(run text fallback descriptors).tree.lookup path=some a) ↔ a∈descriptors := by
  rw [Tree.lookup_iff_mem]
  exact (run_correct text fallback descriptors).1.mem_iff

theorem run_path_lcp (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) (a b : Key text.size ρ) (pa pb : List Bool)
    (ha : (run text fallback descriptors).tree.lookup pa=some a)
    (hb : (run text fallback descriptors).tree.lookup pb=some b) :
    ∃d,Tree.LCA (run text fallback descriptors).tree a b d ∧
      Key.Exact (ArrayText.read text fallback) a b d :=
  Tree.path_commonPrefix _ _ _ _ pa pb (run_correct text fallback descriptors).2.1 ha hb

theorem run_work (text : Array (Fin σ)) (fallback : Fin σ)
    (descriptors : List (Key text.size ρ)) :
    (run text fallback descriptors).work≤
      (text.size+1)*((text.size.log2+1)*(16*RankIndex.width σ text.size+4)+1)+
      (13*(text.size.log2+1)+12)*(8*descriptors.length*(descriptors.length.log2+1))+
      descriptors.length+2+2*descriptors.length*budget text.size descriptors.length := by
  have hp:=prepare_work text fallback descriptors
  have hb:=(run_correct text fallback descriptors).2.2.2
  omega

end REWB.BoundaryTrie.Build
