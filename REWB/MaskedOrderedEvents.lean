import REWB.MaskedOrderedReference

/-! Actual persistent insertion and local adjacency repair. Membership
prevents duplicate records. A fresh insertion performs one membership
query, one predecessor query, one successor query, and one path copy;
it emits at most two new edges and retires at most one old edge. -/
namespace REWB.MaskedOrdered
open Tree
open REWB.MaskedEventBudget (Edge)
variable {h : Nat}

structure Insertion (h : Nat) where
  tree : Tree h
  fresh : List Edge
  retired : List Edge
  inserted : Bool
  work : Nat
  deriving Repr

def insert (t : Tree h) (capacity p : Nat) : Insertion h :=
  let membership:=Tree.contains t capacity p
  if membership.1 then ⟨t,[],[],false,membership.2+1⟩
  else
    let before:=Tree.pred t capacity p
    let after:=Tree.succ t capacity p
    let next:=Tree.insert t capacity p
    ⟨next.1,freshEdges p before.1 after.1,retiredEdges before.1 after.1,true,
      membership.2+before.2+after.2+next.2+8⟩

theorem insert_existing (t : Tree h) (capacity p : Nat) (hf : Fits t 0)
    (hb : capacity=2^h) (hp : p∈t.entries) :
    (insert t capacity p).tree=t ∧ (insert t capacity p).fresh=[] ∧
      (insert t capacity p).retired=[] ∧ (insert t capacity p).inserted=false := by
  have hh:=(contains_correct t capacity p hf hb).mpr hp
  simp only [insert,hh,if_true,true_and]

theorem insert_new (t : Tree h) (capacity p : Nat) (hf : Fits t 0)
    (hb : capacity=2^h) (hp : p∉t.entries) :
    (insert t capacity p).tree=(Tree.insert t capacity p).1 ∧
      (insert t capacity p).fresh=freshEdges p (Tree.pred t capacity p).1 (Tree.succ t capacity p).1 ∧
      (insert t capacity p).retired=retiredEdges (Tree.pred t capacity p).1 (Tree.succ t capacity p).1 ∧
      (insert t capacity p).inserted=true := by
  have hh : ¬(Tree.contains t capacity p).1=true :=
    fun he=>hp ((contains_correct t capacity p hf hb).mp he)
  simp only [insert,if_neg hh,true_and]

theorem insert_good (t : Tree h) (capacity p : Nat) (hg : Good t) :
    Good (insert t capacity p).tree := by
  simp only [insert]
  split
  · exact hg
  · exact Tree.insert_good t capacity p hg

theorem insert_fits (t : Tree h) (capacity p : Nat) (hf : Fits t 0)
    (hb : capacity=2^h) (hp : p<2^h) : Fits (insert t capacity p).tree 0 := by
  simp only [insert]
  split
  · exact hf
  · exact Tree.insert_fits t capacity p hf hb hp

theorem insert_mem (t : Tree h) (capacity p x : Nat) (hf : Fits t 0)
    (hb : capacity=2^h) (hp : p<2^h) :
    x∈(insert t capacity p).tree.entries ↔ x=p ∨ x∈t.entries := by
  by_cases hmem : p∈t.entries
  · rw [(insert_existing t capacity p hf hb hmem).1]
    constructor
    · exact Or.inr
    · rintro (he|hx)
      · simpa only [he] using hmem
      · exact hx
  · rw [(insert_new t capacity p hf hb hmem).1]
    exact Tree.insert_mem t capacity p x hf hb hp

theorem insert_reference (t : Tree h) (capacity p : Nat) (hg : Good t) (hf : Fits t 0)
    (hb : capacity=2^h) (hp : p<2^h) (hnew : p∉t.entries) :
    (insert t capacity p).tree.entries=(MaskedEventBudget.insert p t.entries).positions ∧
      (insert t capacity p).fresh=(MaskedEventBudget.insert p t.entries).fresh ∧
      (insert t capacity p).retired=(MaskedEventBudget.insert p t.entries).retired ∧
      (insert t capacity p).inserted=true := by
  have hh:=insert_new t capacity p hf hb hnew
  have he:=reference_edges p t.entries (Tree.pred t capacity p).1 (Tree.succ t capacity p).1
    (ordered t 0 hf) hnew (pred_correct t capacity p hg hf hb) (succ_correct t capacity p hg hf hb)
  refine ⟨?_,hh.2.1.trans he.1.symm,hh.2.2.1.trans he.2.symm,hh.2.2.2⟩
  rw [hh.1]
  exact tree_insert_reference t capacity p hg hf hb hp hnew

theorem insert_new_count (t : Tree h) (capacity p : Nat) (hg : Good t) (hf : Fits t 0)
    (hb : capacity=2^h) (hp : p<2^h) (hnew : p∉t.entries) :
    (insert t capacity p).tree.count=t.count+1 := by
  rw [(insert_new t capacity p hf hb hnew).1]
  exact tree_insert_new_count t capacity p hg hf hb hp hnew

theorem insert_count (t : Tree h) (capacity p : Nat) (hg : Good t) (hf : Fits t 0)
    (hb : capacity=2^h) (hp : p<2^h) :
    (insert t capacity p).tree.count=t.count+(if (insert t capacity p).inserted then 1 else 0) := by
  by_cases hmem : p∈t.entries
  · have hh:=insert_existing t capacity p hf hb hmem
    rw [hh.1,hh.2.2.2]
    simp only [Bool.false_eq_true,if_false,Nat.add_zero]
  · rw [(insert_new t capacity p hf hb hmem).2.2.2]
    exact insert_new_count t capacity p hg hf hb hp hmem

theorem insert_work (t : Tree h) (capacity p : Nat) : (insert t capacity p).work≤28*h+18 := by
  have hm:=contains_work t capacity p
  have hp:=pred_work t capacity p
  have hs:=succ_work t capacity p
  have hi:=Tree.insert_work t capacity p
  simp only [insert]
  split <;> dsimp only <;> omega

theorem insert_fresh_bound (t : Tree h) (capacity p : Nat) : (insert t capacity p).fresh.length≤2 := by
  simp only [insert]
  split
  · exact Nat.zero_le _
  · exact freshEdges_length _ _ _

theorem insert_retired_bound (t : Tree h) (capacity p : Nat) : (insert t capacity p).retired.length≤1 := by
  simp only [insert]
  split
  · exact Nat.zero_le _
  · exact retiredEdges_length _ _

theorem insert_edge_repair (t : Tree h) (capacity p : Nat) (hg : Good t) (hf : Fits t 0)
    (hb : capacity=2^h) (hp : p<2^h) :
    ∃pre post : List Edge,
      MaskedEventBudget.edges (insert t capacity p).tree.entries=pre++(insert t capacity p).fresh++post ∧
      MaskedEventBudget.edges t.entries=pre++(insert t capacity p).retired++post := by
  by_cases hmem : p∈t.entries
  · have hh:=insert_existing t capacity p hf hb hmem
    refine ⟨[],MaskedEventBudget.edges t.entries,?_,?_⟩
    · simp only [hh.1,hh.2.1,List.nil_append]
    · simp only [hh.2.2.1,List.nil_append]
  · have hh:=insert_reference t capacity p hg hf hb hp hmem
    obtain ⟨pre,post,ha,hb⟩:=MaskedEventBudget.insert_edge_repair p t.entries
    exact ⟨pre,post,by rwa [hh.1,hh.2.1],by rwa [hh.2.2.1]⟩

end REWB.MaskedOrdered
