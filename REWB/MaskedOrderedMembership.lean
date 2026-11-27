import REWB.MaskedOrderedQuery

namespace REWB.MaskedOrdered.Tree
variable {h : Nat}

def contains.go : {h : Nat}→Tree h→Nat→Nat→Nat→Bool×Nat
  | _,.empty,_,_,_ => (false,1)
  | 0,.tip q,_,_,p => (decide (p=q),2)
  | _+1,.node _ _ _ l r,lo,block,p =>
    let half:=block/2
    let a:=if p<lo+half then go l lo half p else go r (lo+half) half p
    (a.1,a.2+4)

theorem contains.go_work (t : Tree h) (lo block p : Nat) : (go t lo block p).2≤4*h+2 := by
  induction h generalizing lo block p with
  | zero => cases t <;> simp [go]
  | succ h ih =>
    cases t with
    | empty => simp [go]
    | node c a b l r =>
      simp only [go]
      split
      · have hh:=ih l lo (block/2) p
        omega
      · have hh:=ih r (lo+block/2) (block/2) p
        omega

theorem contains.go_correct (t : Tree h) (lo block p : Nat) (hf : Fits t lo)
    (hb : block=2^h) : (go t lo block p).1=true ↔ p∈entries t := by
  induction h generalizing lo block p with
  | zero =>
    cases t <;> simp [go,entries]
  | succ h ih =>
    cases t with
    | empty => simp [go,entries]
    | node c a b l r =>
      have hh:=half_block h block hb
      simp only [go,hh,entries,List.mem_append]
      split
      next hpivot =>
        rw [ih l lo (2^h) p hf.1 rfl]
        have hn : p∉entries r := by
          intro hp
          have hr:=within r (lo+2^h) hf.2 p hp
          omega
        simp only [hn,or_false]
      next hpivot =>
        rw [ih r (lo+2^h) (2^h) p hf.2 rfl]
        have hn : p∉entries l := by
          intro hp
          have hl:=within l lo hf.1 p hp
          omega
        simp only [hn,false_or]

def contains (t : Tree h) (capacity p : Nat) : Bool×Nat := contains.go t 0 capacity p

theorem contains_correct (t : Tree h) (capacity p : Nat) (hf : Fits t 0)
    (hb : capacity=2^h) : (contains t capacity p).1=true ↔ p∈entries t :=
  contains.go_correct t 0 capacity p hf hb

theorem contains_work (t : Tree h) (capacity p : Nat) : (contains t capacity p).2≤4*h+2 :=
  contains.go_work t 0 capacity p

end REWB.MaskedOrdered.Tree
