import REWB.MaskedOrderedTree

/-! Exact strict neighbors in the persistent position set. Each query
descends only one child at each level. If that child has no answer, the
sibling's cached extremum supplies the answer without a second descent. -/
namespace REWB.MaskedOrdered
namespace Tree
variable {h : Nat}

def MinSpec (xs : List Nat) : Option Nat→Prop
  | none => xs=[]
  | some q => q∈xs ∧ ∀r,r∈xs→q≤r

def MaxSpec (xs : List Nat) : Option Nat→Prop
  | none => xs=[]
  | some q => q∈xs ∧ ∀r,r∈xs→r≤q

def PredSpec (xs : List Nat) (p : Nat) : Option Nat→Prop
  | none => ∀r,r∈xs→p≤r
  | some q => q∈xs ∧ q<p ∧ ∀r,r∈xs→r<p→r≤q

def SuccSpec (xs : List Nat) (p : Nat) : Option Nat→Prop
  | none => ∀r,r∈xs→r≤p
  | some q => q∈xs ∧ p<q ∧ ∀r,r∈xs→p<r→q≤r

theorem head_spec (xs : List Nat) (hs : xs.Pairwise (·<·)) : MinSpec xs xs.head? := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    refine ⟨by simp,?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with he|hm
    · omega
    · exact Nat.le_of_lt ((List.pairwise_cons.mp hs).1 r hm)

theorem last_spec_list (xs : List Nat) (hs : xs.Pairwise (·<·)) :
    MaxSpec xs xs.getLast? := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp [MaxSpec,List.getLast?]
    | cons y ys =>
      have hh:=ih (List.pairwise_cons.mp hs).2
      change MaxSpec (x::y::ys) (y::ys).getLast?
      cases he : (y::ys).getLast? with
      | none => simp only [he,MaxSpec,List.cons_ne_nil] at hh
      | some q =>
        simp only [he,MaxSpec] at hh ⊢
        refine ⟨List.mem_cons_of_mem _ hh.1,?_⟩
        intro r hr
        rcases List.mem_cons.mp hr with hr|hr
        · have hx:=(List.pairwise_cons.mp hs).1 q hh.1
          omega
        · exact hh.2 r hr

theorem first_spec (t : Tree h) (lo : Nat) (hg : Good t) (hf : Fits t lo) :
    MinSpec t.entries t.first := by
  rw [first_correct t hg]
  exact head_spec _ (ordered t lo hf)

theorem last_spec (t : Tree h) (lo : Nat) (hg : Good t) (hf : Fits t lo) :
    MaxSpec t.entries t.last := by
  rw [last_correct t hg]
  exact last_spec_list _ (ordered t lo hf)

def pred.go : {h : Nat}→Tree h→Nat→Nat→Nat→Option Nat×Nat
  | _,.empty,_,_,_ => (none,1)
  | 0,.tip q,_,_,p => (if q<p then some q else none,3)
  | _+1,.node _ _ _ l r,lo,block,p =>
    let half:=block/2
    if p≤lo+half then
      let a:=go l lo half p
      (a.1,a.2+6)
    else
      let a:=go r (lo+half) half p
      (a.1.or l.last,a.2+7)

def succ.go : {h : Nat}→Tree h→Nat→Nat→Nat→Option Nat×Nat
  | _,.empty,_,_,_ => (none,1)
  | 0,.tip q,_,_,p => (if p<q then some q else none,3)
  | _+1,.node _ _ _ l r,lo,block,p =>
    let half:=block/2
    if p<lo+half then
      let a:=go l lo half p
      (a.1.or r.first,a.2+7)
    else
      let a:=go r (lo+half) half p
      (a.1,a.2+6)

theorem pred.go_work (t : Tree h) (lo block p : Nat) : (go t lo block p).2≤7*h+3 := by
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

theorem succ.go_work (t : Tree h) (lo block p : Nat) : (go t lo block p).2≤7*h+3 := by
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

theorem pred.go_correct (t : Tree h) (lo block p : Nat) (hg : Good t) (hf : Fits t lo)
    (hb : block=2^h) : PredSpec t.entries p (go t lo block p).1 := by
  induction h generalizing lo block p with
  | zero =>
    cases t with
    | empty => simp [go,PredSpec,entries]
    | tip q =>
      simp only [go,entries]
      split <;> simp_all [PredSpec]
  | succ h ih =>
    cases t with
    | empty => simp [go,PredSpec,entries]
    | node c a b l r =>
      have hh:=half_block h block hb
      simp only [go,hh,entries]
      split
      next hpivot =>
        have hl:=ih l lo (2^h) p hg.1 hf.1 rfl
        cases he : (go l lo (2^h) p).1 with
        | none =>
          simp only [he,PredSpec] at hl ⊢
          intro x hx
          rcases List.mem_append.mp hx with hx|hx
          · exact hl x hx
          · have hr:=within r (lo+2^h) hf.2 x hx
            omega
        | some q =>
          simp only [he,PredSpec] at hl ⊢
          refine ⟨List.mem_append_left _ hl.1,hl.2.1,?_⟩
          intro x hx hxp
          rcases List.mem_append.mp hx with hx|hx
          · exact hl.2.2 x hx hxp
          · have hr:=within r (lo+2^h) hf.2 x hx
            omega
      next hpivot =>
        have hr:=ih r (lo+2^h) (2^h) p hg.2.1 hf.2 rfl
        cases he : (go r (lo+2^h) (2^h) p).1 with
        | some q =>
          simp only [he,Option.some_or,PredSpec] at hr ⊢
          refine ⟨List.mem_append_right _ hr.1,hr.2.1,?_⟩
          intro x hx hxp
          rcases List.mem_append.mp hx with hx|hx
          · have hlx:=within l lo hf.1 x hx
            have hrq:=within r (lo+2^h) hf.2 q hr.1
            omega
          · exact hr.2.2 x hx hxp
        | none =>
          simp only [he,Option.none_or,PredSpec] at hr ⊢
          have hl:=last_spec l lo hg.1 hf.1
          cases hm : l.last with
          | none =>
            simp only [hm,MaxSpec,PredSpec] at hl ⊢
            intro x hx
            rw [hl,List.nil_append] at hx
            exact hr x hx
          | some q =>
            simp only [hm,MaxSpec,PredSpec] at hl ⊢
            have hq:=within l lo hf.1 q hl.1
            refine ⟨List.mem_append_left _ hl.1,by omega,?_⟩
            intro x hx hxp
            rcases List.mem_append.mp hx with hx|hx
            · exact hl.2 x hx
            · have hh:=hr x hx
              omega

theorem succ.go_correct (t : Tree h) (lo block p : Nat) (hg : Good t) (hf : Fits t lo)
    (hb : block=2^h) : SuccSpec t.entries p (go t lo block p).1 := by
  induction h generalizing lo block p with
  | zero =>
    cases t with
    | empty => simp [go,SuccSpec,entries]
    | tip q =>
      simp only [go,entries]
      split <;> simp_all [SuccSpec]
  | succ h ih =>
    cases t with
    | empty => simp [go,SuccSpec,entries]
    | node c a b l r =>
      have hh:=half_block h block hb
      simp only [go,hh,entries]
      split
      next hpivot =>
        have hl:=ih l lo (2^h) p hg.1 hf.1 rfl
        cases he : (go l lo (2^h) p).1 with
        | some q =>
          simp only [he,Option.some_or,SuccSpec] at hl ⊢
          refine ⟨List.mem_append_left _ hl.1,hl.2.1,?_⟩
          intro x hx hpx
          rcases List.mem_append.mp hx with hx|hx
          · exact hl.2.2 x hx hpx
          · have hlq:=within l lo hf.1 q hl.1
            have hrx:=within r (lo+2^h) hf.2 x hx
            omega
        | none =>
          simp only [he,Option.none_or,SuccSpec] at hl ⊢
          have hr:=first_spec r (lo+2^h) hg.2.1 hf.2
          cases hm : r.first with
          | none =>
            simp only [hm,MinSpec,SuccSpec] at hr ⊢
            intro x hx
            rw [hr,List.append_nil] at hx
            exact hl x hx
          | some q =>
            simp only [hm,MinSpec,SuccSpec] at hr ⊢
            have hq:=within r (lo+2^h) hf.2 q hr.1
            refine ⟨List.mem_append_right _ hr.1,by omega,?_⟩
            intro x hx hpx
            rcases List.mem_append.mp hx with hx|hx
            · have hh:=hl x hx
              omega
            · exact hr.2 x hx
      next hpivot =>
        have hr:=ih r (lo+2^h) (2^h) p hg.2.1 hf.2 rfl
        cases he : (go r (lo+2^h) (2^h) p).1 with
        | none =>
          simp only [he,SuccSpec] at hr ⊢
          intro x hx
          rcases List.mem_append.mp hx with hx|hx
          · have hl:=within l lo hf.1 x hx
            omega
          · exact hr x hx
        | some q =>
          simp only [he,SuccSpec] at hr ⊢
          refine ⟨List.mem_append_right _ hr.1,hr.2.1,?_⟩
          intro x hx hpx
          rcases List.mem_append.mp hx with hx|hx
          · have hl:=within l lo hf.1 x hx
            omega
          · exact hr.2.2 x hx hpx

def pred (t : Tree h) (capacity p : Nat) : Option Nat×Nat := pred.go t 0 capacity p
def succ (t : Tree h) (capacity p : Nat) : Option Nat×Nat := succ.go t 0 capacity p

theorem pred_correct (t : Tree h) (capacity p : Nat) (hg : Good t) (hf : Fits t 0)
    (hb : capacity=2^h) : PredSpec t.entries p (pred t capacity p).1 :=
  pred.go_correct t 0 capacity p hg hf hb

theorem succ_correct (t : Tree h) (capacity p : Nat) (hg : Good t) (hf : Fits t 0)
    (hb : capacity=2^h) : SuccSpec t.entries p (succ t capacity p).1 :=
  succ.go_correct t 0 capacity p hg hf hb

theorem pred_work (t : Tree h) (capacity p : Nat) : (pred t capacity p).2≤7*h+3 :=
  pred.go_work t 0 capacity p

theorem succ_work (t : Tree h) (capacity p : Nat) : (succ t capacity p).2≤7*h+3 :=
  succ.go_work t 0 capacity p

end Tree
end REWB.MaskedOrdered
