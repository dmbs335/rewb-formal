import REWB.MaskedOrderedMembership

/-! Persistent one-path deletion from the sparse ordered position tree.
Empty subtrees remain single shared constructors. Every untouched child
is reused; neither the specification list nor a full tree scan occurs in
the executable operations. The stored block is halved at each descent. -/
namespace REWB.MaskedOrdered.Tree

variable {h : Nat}

/-- Restore the shared empty constructor after deleting the last leaf. -/
def isEmpty : {h : Nat}→Tree h→Bool
  | _,.empty => true
  | _,_ => false

def pruneJoin (l r : Tree h) : Tree (h+1) :=
  if isEmpty l && isEmpty r then .empty else join l r

theorem pruneJoin_entries (l r : Tree h) :
    entries (pruneJoin l r)=entries l++entries r := by
  cases l <;> cases r <;> rfl

theorem pruneJoin_good (l r : Tree h) (hl : Good l) (hr : Good r) :
    Good (pruneJoin l r) := by
  cases l <;> cases r <;> simp_all [pruneJoin,isEmpty,Good,join]

theorem pruneJoin_fits (l r : Tree h) (lo : Nat)
    (hl : Fits l lo) (hr : Fits r (lo+2^h)) : Fits (pruneJoin l r) lo := by
  cases l <;> cases r <;> simp_all [pruneJoin,isEmpty,Fits,join]

def erase.go : {h : Nat}→Tree h→Nat→Nat→Nat→Tree h×Nat
  | _,.empty,_,_,_ => (.empty,1)
  | 0,.tip q,_,_,p => if p=q then (.empty,3) else (.tip q,3)
  | _+1,.node _ _ _ l r,lo,block,p =>
    let half:=block/2
    if p<lo+half then
      let out:=go l lo half p
      (pruneJoin out.1 r,out.2+12)
    else
      let out:=go r (lo+half) half p
      (pruneJoin l out.1,out.2+12)

theorem erase.go_work (t : Tree h) (lo block p : Nat) :
    (go t lo block p).2≤12*h+3 := by
  induction t generalizing lo block with
  | empty => simp [go]
  | tip q => simp [go]; split <;> omega
  | @node h c a b l r ihl ihr =>
    simp only [go]
    split
    · have hh:=ihl lo (block/2); omega
    · have hh:=ihr (lo+block/2) (block/2); omega

theorem erase.go_good (t : Tree h) (lo block p : Nat) (hg : Good t) :
    Good (go t lo block p).1 := by
  induction t generalizing lo block with
  | empty => simp [go,Good,Fits]
  | tip q => simp only [go]; split <;> exact True.intro
  | node c a b l r ihl ihr =>
    simp only [go]
    split
    · exact pruneJoin_good _ _ (ihl _ _ hg.1) hg.2.1
    · exact pruneJoin_good _ _ hg.1 (ihr _ _ hg.2.1)

theorem erase.go_fits (t : Tree h) (lo block p : Nat)
    (hf : Fits t lo) (hb : block=2^h) : Fits (go t lo block p).1 lo := by
  induction t generalizing lo block with
  | empty => simp [go,Good,Fits]
  | tip q =>
    simp only [go]
    split
    · exact True.intro
    · exact hf
  | @node h c a b l r ihl ihr =>
    have hhalf:=half_block h block hb
    simp only [go,hhalf]
    split
    · exact pruneJoin_fits _ _ lo (ihl lo _ hf.1 rfl) hf.2
    · exact pruneJoin_fits _ _ lo hf.1 (ihr (lo+2^h) _ hf.2 rfl)

/-- Deletion is exact even if the requested position is outside the tree. -/
theorem erase.go_mem (t : Tree h) (lo block p x : Nat)
    (hf : Fits t lo) (hb : block=2^h) :
    x∈entries (go t lo block p).1 ↔ x≠p ∧ x∈entries t := by
  induction t generalizing lo block with
  | empty => simp [go,entries]
  | tip q =>
    simp only [go]
    split
    next he => simp [entries,he]
    next he => simp only [entries,List.mem_singleton]; omega
  | @node h c a b l r ihl ihr =>
    have hhalf:=half_block h block hb
    simp only [go,hhalf]
    split
    next hp =>
      rw [pruneJoin_entries,List.mem_append,ihl lo _ hf.1 rfl]
      change (x≠p ∧ x∈entries l) ∨ x∈entries r ↔
        x≠p ∧ x∈(entries l++entries r)
      constructor
      · rintro (⟨hne,hl⟩|hr)
        · exact ⟨hne,List.mem_append_left _ hl⟩
        · have hx:=within r (lo+2^h) hf.2 x hr
          exact ⟨by omega,List.mem_append_right _ hr⟩
      · rintro ⟨hne,hx⟩
        rcases List.mem_append.mp hx with hl|hr
        · exact Or.inl ⟨hne,hl⟩
        · exact Or.inr hr
    next hp =>
      rw [pruneJoin_entries,List.mem_append,ihr (lo+2^h) _ hf.2 rfl]
      change x∈entries l ∨ (x≠p ∧ x∈entries r) ↔
        x≠p ∧ x∈(entries l++entries r)
      constructor
      · rintro (hl|⟨hne,hr⟩)
        · have hx:=within l lo hf.1 x hl
          exact ⟨by omega,List.mem_append_left _ hl⟩
        · exact ⟨hne,List.mem_append_right _ hr⟩
      · rintro ⟨hne,hx⟩
        rcases List.mem_append.mp hx with hl|hr
        · exact Or.inl hl
        · exact Or.inr ⟨hne,hr⟩

def erase (t : Tree h) (capacity p : Nat) : Tree h×Nat := erase.go t 0 capacity p

theorem erase_work (t : Tree h) (capacity p : Nat) :
    (erase t capacity p).2≤12*h+3 := erase.go_work t 0 capacity p

theorem erase_good (t : Tree h) (capacity p : Nat) (hg : Good t) :
    Good (erase t capacity p).1 := erase.go_good t 0 capacity p hg

theorem erase_fits (t : Tree h) (capacity p : Nat) (hf : Fits t 0)
    (hb : capacity=2^h) : Fits (erase t capacity p).1 0 :=
  erase.go_fits t 0 capacity p hf hb

theorem erase_mem (t : Tree h) (capacity p x : Nat) (hf : Fits t 0)
    (hb : capacity=2^h) :
    x∈entries (erase t capacity p).1 ↔ x≠p ∧ x∈entries t :=
  erase.go_mem t 0 capacity p x hf hb

end REWB.MaskedOrdered.Tree
