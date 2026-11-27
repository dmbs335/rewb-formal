import REWB.MaskedEventBudget

/-! A sparse persistent fixed-height position tree. The empty subtree is
one constructor at every height, shared by all untouched regions. Nodes
cache the cardinality and both extrema. Specification lists below are
never constructed by insertion or lookup. The descent carries a block
width and halves it, instead of recomputing powers at every level. -/
namespace REWB.MaskedOrdered

inductive Tree : Nat→Type where
  | empty {h : Nat} : Tree h
  | tip (position : Nat) : Tree 0
  | node {h : Nat} (count : Nat) (first last : Option Nat) (left right : Tree h) : Tree (h+1)
  deriving Repr

namespace Tree
variable {h : Nat}

def count : Tree h→Nat
  | .empty => 0
  | .tip _ => 1
  | .node c _ _ _ _ => c

def first : Tree h→Option Nat
  | .empty => none
  | .tip p => some p
  | .node _ a _ _ _ => a

def last : Tree h→Option Nat
  | .empty => none
  | .tip p => some p
  | .node _ _ b _ _ => b

def left : Tree (h+1)→Tree h
  | .empty => .empty
  | .node _ _ _ l _ => l

def right : Tree (h+1)→Tree h
  | .empty => .empty
  | .node _ _ _ _ r => r

def entries : {h : Nat}→Tree h→List Nat
  | _,.empty => []
  | _,.tip p => [p]
  | _,.node _ _ _ l r => entries l++entries r

def Good : {h : Nat}→Tree h→Prop
  | _,.empty => True
  | _,.tip _ => True
  | _,.node c a b l r =>
    Good l ∧ Good r ∧ c=l.count+r.count ∧ a=l.first.or r.first ∧ b=r.last.or l.last

def Fits : {h : Nat}→Tree h→Nat→Prop
  | _,.empty,_ => True
  | _,.tip p,lo => p=lo
  | h+1,.node _ _ _ l r,lo => Fits l lo ∧ Fits r (lo+2^h)

theorem entries_children (t : Tree (h+1)) : entries t=entries t.left++entries t.right := by
  cases t <;> rfl

theorem good_left (t : Tree (h+1)) (hg : Good t) : Good t.left := by
  cases t with
  | empty => exact True.intro
  | node _ _ _ _ _ => exact hg.1

theorem good_right (t : Tree (h+1)) (hg : Good t) : Good t.right := by
  cases t with
  | empty => exact True.intro
  | node _ _ _ _ _ => exact hg.2.1

theorem fits_children (t : Tree (h+1)) (lo : Nat) (hf : Fits t lo) :
    Fits t.left lo ∧ Fits t.right (lo+2^h) := by
  cases t with
  | empty => simp only [left,right,Fits,true_and]
  | node _ _ _ _ _ => exact hf

theorem within (t : Tree h) (lo : Nat) (hf : Fits t lo) (p : Nat) (hp : p∈entries t) :
    lo≤p ∧ p<lo+2^h := by
  induction t generalizing lo with
  | empty => simp [entries] at hp
  | tip a =>
    simp only [entries,List.mem_singleton] at hp
    change a=lo at hf
    simp only [hp,hf,Nat.pow_zero]
    omega
  | @node k c a b l r ihl ihr =>
    rcases List.mem_append.mp hp with hpl|hpr
    · have hh:=ihl lo hf.1 hpl
      rw [Nat.pow_succ]
      omega
    · have hh:=ihr (lo+2^k) hf.2 hpr
      rw [Nat.pow_succ]
      omega

theorem ordered (t : Tree h) (lo : Nat) (hf : Fits t lo) : entries t |>.Pairwise (·<·) := by
  induction t generalizing lo with
  | empty => exact List.Pairwise.nil
  | tip _ => simp [entries]
  | @node k c a b l r ihl ihr =>
    rw [entries,List.pairwise_append]
    refine ⟨ihl lo hf.1,ihr (lo+2^k) hf.2,?_⟩
    intro x hx y hy
    have hl:=within l lo hf.1 x hx
    have hr:=within r (lo+2^k) hf.2 y hy
    omega

theorem nodup (t : Tree h) (lo : Nat) (hf : Fits t lo) : (entries t).Nodup :=
  (ordered t lo hf).imp (fun h=>Nat.ne_of_lt h)

theorem count_correct (t : Tree h) (hg : Good t) : count t=(entries t).length := by
  induction t with
  | empty => rfl
  | tip _ => rfl
  | node c a b l r ihl ihr =>
    simp only [count,entries,List.length_append]
    rw [hg.2.2.1,ihl hg.1,ihr hg.2.1]

theorem first_correct (t : Tree h) (hg : Good t) : first t=(entries t).head? := by
  induction t with
  | empty => rfl
  | tip _ => rfl
  | node c a b l r ihl ihr =>
    simp only [first,entries,List.head?_append]
    rw [hg.2.2.2.1,ihl hg.1,ihr hg.2.1]

theorem last_correct (t : Tree h) (hg : Good t) : last t=(entries t).getLast? := by
  induction t with
  | empty => rfl
  | tip _ => rfl
  | node c a b l r ihl ihr =>
    simp only [last,entries,List.getLast?_append]
    rw [hg.2.2.2.2,ihl hg.1,ihr hg.2.1]

def join (l r : Tree h) : Tree (h+1) :=
  .node (l.count+r.count) (l.first.or r.first) (r.last.or l.last) l r

theorem join_entries (l r : Tree h) : entries (join l r)=entries l++entries r := rfl
theorem join_count (l r : Tree h) : count (join l r)=count l+count r := rfl

theorem join_good (l r : Tree h) (hl : Good l) (hr : Good r) : Good (join l r) :=
  ⟨hl,hr,rfl,rfl,rfl⟩

theorem join_fits (l r : Tree h) (lo : Nat) (hl : Fits l lo) (hr : Fits r (lo+2^h)) :
    Fits (join l r) lo := ⟨hl,hr⟩

/-- Ten scalar/cache slots per internal path step and two at the leaf.
Only one recursive branch is visited; the other subtree is shared. -/
def insert.go : {h : Nat}→Tree h→Nat→Nat→Nat→Tree h×Nat
  | 0,.empty,_,_,p => (.tip p,2)
  | 0,.tip q,_,_,_ => (.tip q,2)
  | _+1,t,lo,block,p =>
    let half:=block/2
    if p<lo+half then
      let r:=go t.left lo half p
      (join r.1 t.right,r.2+10)
    else
      let r:=go t.right (lo+half) half p
      (join t.left r.1,r.2+10)

theorem insert.go_work (t : Tree h) (lo block p : Nat) :
    (go t lo block p).2≤10*h+2 := by
  induction h generalizing lo block p with
  | zero => cases t <;> simp [go]
  | succ h ih =>
    simp only [go]
    split
    · have hh:=ih t.left lo (block/2) p
      omega
    · have hh:=ih t.right (lo+block/2) (block/2) p
      omega

theorem insert.go_good (t : Tree h) (lo block p : Nat) (hg : Good t) :
    Good (go t lo block p).1 := by
  induction h generalizing lo block p with
  | zero => cases t <;> exact True.intro
  | succ h ih =>
    simp only [go]
    split
    · exact join_good _ _ (ih t.left _ _ _ (good_left t hg)) (good_right t hg)
    · exact join_good _ _ (good_left t hg) (ih t.right _ _ _ (good_right t hg))

theorem half_block (h block : Nat) (hb : block=2^(h+1)) : block/2=2^h := by
  rw [hb,Nat.pow_succ,Nat.mul_div_cancel _ (by decide : 0<2)]

theorem insert.go_fits (t : Tree h) (lo block p : Nat) (hf : Fits t lo)
    (hb : block=2^h) (hp : lo≤p ∧ p<lo+2^h) : Fits (go t lo block p).1 lo := by
  induction h generalizing lo block p with
  | zero =>
    have he : p=lo := by simp only [Nat.pow_zero] at hp; omega
    cases t with
    | empty => exact he
    | tip q => exact hf
  | succ h ih =>
    have hhalf:=half_block h block hb
    have hc:=fits_children t lo hf
    simp only [go,hhalf]
    split
    next hpivot =>
      exact join_fits _ _ lo (ih t.left lo (2^h) p hc.1 rfl ⟨hp.1,hpivot⟩) hc.2
    next hpivot =>
      have hpr : lo+2^h≤p ∧ p<(lo+2^h)+2^h := by
        rw [Nat.pow_succ] at hp
        omega
      exact join_fits _ _ lo hc.1 (ih t.right _ (2^h) p hc.2 rfl hpr)

theorem insert.go_mem (t : Tree h) (lo block p x : Nat) (hf : Fits t lo)
    (hb : block=2^h) (hp : lo≤p ∧ p<lo+2^h) :
    x∈entries (go t lo block p).1 ↔ x=p ∨ x∈entries t := by
  induction h generalizing lo block p with
  | zero =>
    have he : p=lo := by simp only [Nat.pow_zero] at hp; omega
    cases t with
    | empty => simp [go,entries]
    | tip q =>
      have hq : q=p := by change q=lo at hf; omega
      simp only [go,entries,List.mem_singleton,hq,or_self]
  | succ h ih =>
    have hhalf:=half_block h block hb
    have hc:=fits_children t lo hf
    simp only [go,hhalf]
    split
    next hpivot =>
      rw [join_entries,List.mem_append,ih t.left lo (2^h) p hc.1 rfl ⟨hp.1,hpivot⟩,
        entries_children,List.mem_append]
      exact or_assoc
    next hpivot =>
      have hpr : lo+2^h≤p ∧ p<(lo+2^h)+2^h := by
        rw [Nat.pow_succ] at hp
        omega
      rw [join_entries,List.mem_append,ih t.right _ (2^h) p hc.2 rfl hpr,
        entries_children,List.mem_append]
      exact or_left_comm

/-- The capacity is stored once by the enclosing position-set index. -/
def insert (t : Tree h) (capacity p : Nat) : Tree h×Nat := insert.go t 0 capacity p

theorem insert_work (t : Tree h) (capacity p : Nat) :
    (insert t capacity p).2≤10*h+2 := insert.go_work t 0 capacity p

theorem insert_good (t : Tree h) (capacity p : Nat) (hg : Good t) :
    Good (insert t capacity p).1 := insert.go_good t 0 capacity p hg

theorem insert_fits (t : Tree h) (capacity p : Nat) (hf : Fits t 0)
    (hb : capacity=2^h) (hp : p<2^h) : Fits (insert t capacity p).1 0 :=
  insert.go_fits t 0 capacity p hf hb ⟨Nat.zero_le _,by omega⟩

theorem insert_mem (t : Tree h) (capacity p x : Nat) (hf : Fits t 0)
    (hb : capacity=2^h) (hp : p<2^h) :
    x∈entries (insert t capacity p).1 ↔ x=p ∨ x∈entries t :=
  insert.go_mem t 0 capacity p x hf hb ⟨Nat.zero_le _,by omega⟩

end Tree
end REWB.MaskedOrdered
