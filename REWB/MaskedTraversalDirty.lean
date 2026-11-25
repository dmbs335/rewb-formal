import REWB.MaskedTraversalFrontierMerge

/-! Concrete finite dirty-key collection from leader-neighbor queries.
The exact queried keys, sparse deduplication, and operation counts are
verified here.  Descriptor/cursor locality outside these keys is a further
obligation: this module alone does not justify a global bank repair.
-/
namespace REWB.MaskedTraversalDirty
open REWB.MaskedOrdered
variable {h : Nat}

structure Around where
  earlier : Option Nat
  left : Option Nat
  right : Option Nat
  later : Option Nat
  work : Nat
  deriving Repr

def optionalPred (t : Tree h) (capacity : Nat) : Option Nat→Option Nat×Nat
  | none => (none,1)
  | some p => let out:=Tree.pred t capacity p; (out.1,out.2+1)

def optionalSucc (t : Tree h) (capacity : Nat) : Option Nat→Option Nat×Nat
  | none => (none,1)
  | some p => let out:=Tree.succ t capacity p; (out.1,out.2+1)

theorem optionalPred_work (t : Tree h) (capacity : Nat) (p : Option Nat) :
    (optionalPred t capacity p).2≤7*h+4 := by
  cases p with
  | none => simp [optionalPred]
  | some p => have hw:=Tree.pred_work t capacity p; simp only [optionalPred]; omega

theorem optionalSucc_work (t : Tree h) (capacity : Nat) (p : Option Nat) :
    (optionalSucc t capacity p).2≤7*h+4 := by
  cases p with
  | none => simp [optionalSucc]
  | some p => have hw:=Tree.succ_work t capacity p; simp only [optionalSucc]; omega

/-- Two neighbors on each side of a physical cut, including the leader
at that cut on the left.  This requires exactly four logarithmic reads. -/
def around (t : Tree h) (capacity p : Nat) : Around :=
  let left:=Tree.pred t capacity (p+1)
  let right:=Tree.succ t capacity p
  let earlier:=optionalPred t capacity left.1
  let later:=optionalSucc t capacity right.1
  ⟨earlier.1,left.1,right.1,later.1,left.2+right.2+earlier.2+later.2+14⟩

def Around.keys (a : Around) : List Nat :=
  a.earlier.toList++a.left.toList++a.right.toList++a.later.toList

theorem Around.length (a : Around) : a.keys.length≤4 := by
  rcases a with ⟨earlier,left,right,later,work⟩
  cases earlier <;> cases left <;> cases right <;> cases later <;> simp [Around.keys]

theorem around_work (t : Tree h) (capacity p : Nat) : (around t capacity p).work≤28*h+28 := by
  have hl:=Tree.pred_work t capacity (p+1)
  have hr:=Tree.succ_work t capacity p
  have he:=optionalPred_work t capacity (Tree.pred t capacity (p+1)).1
  have hn:=optionalSucc_work t capacity (Tree.succ t capacity p).1
  simp only [around]
  omega

private theorem pred_mem (t : Tree h) (capacity p x : Nat) (hg : t.Good) (hf : t.Fits 0)
    (hc : capacity=2^h) (he : (Tree.pred t capacity p).1=some x) : x∈t.entries := by
  have hs:=Tree.pred_correct t capacity p hg hf hc
  rw [he] at hs
  exact hs.1

private theorem succ_mem (t : Tree h) (capacity p x : Nat) (hg : t.Good) (hf : t.Fits 0)
    (hc : capacity=2^h) (he : (Tree.succ t capacity p).1=some x) : x∈t.entries := by
  have hs:=Tree.succ_correct t capacity p hg hf hc
  rw [he] at hs
  exact hs.1

private theorem optionalPred_mem (t : Tree h) (capacity x : Nat) (p : Option Nat)
    (hg : t.Good) (hf : t.Fits 0) (hc : capacity=2^h)
    (he : (optionalPred t capacity p).1=some x) : x∈t.entries := by
  cases p with
  | none => cases he
  | some p => exact pred_mem t capacity p x hg hf hc he

private theorem optionalSucc_mem (t : Tree h) (capacity x : Nat) (p : Option Nat)
    (hg : t.Good) (hf : t.Fits 0) (hc : capacity=2^h)
    (he : (optionalSucc t capacity p).1=some x) : x∈t.entries := by
  cases p with
  | none => cases he
  | some p => exact succ_mem t capacity p x hg hf hc he

theorem around_mem (t : Tree h) (capacity p x : Nat) (hg : t.Good) (hf : t.Fits 0)
    (hc : capacity=2^h) (hx : x∈(around t capacity p).keys) : x∈t.entries := by
  simp only [Around.keys,around,List.mem_append,Option.mem_toList] at hx
  rcases hx with ((he|he)|he)|he
  · exact optionalPred_mem t capacity x _ hg hf hc he
  · exact pred_mem t capacity (p+1) x hg hf hc he
  · exact succ_mem t capacity p x hg hf hc he
  · exact optionalSucc_mem t capacity x _ hg hf hc he

structure Marked (h : Nat) where
  keys : MaskedOrdered.State h
  requests : Nat
  work : Nat
  deriving Repr

def empty (h : Nat) : Marked h := ⟨MaskedOrdered.State.empty h,0,1⟩

def mark (capacity p : Nat) (out : Marked h) : Marked h :=
  let added:=MaskedOrdered.add out.keys capacity p
  ⟨added.1,out.requests+1,out.work+added.2.work+4⟩

def markList (capacity : Nat) : List Nat→Marked h→Marked h
  | [],out => {out with work:=out.work+1}
  | p::ps,out => markList capacity ps (mark capacity p out)

theorem markList_spec (capacity : Nat) (ps : List Nat) (out : Marked h)
    (hv : out.keys.Valid) (hc : capacity=2^h) (hb : ∀p,p∈ps → p<2^h) :
    (markList capacity ps out).keys.Valid ∧
    (∀x,x∈(markList capacity ps out).keys.tree.entries ↔ x∈ps ∨ x∈out.keys.tree.entries) ∧
    (markList capacity ps out).requests=out.requests+ps.length ∧
    (markList capacity ps out).work≤out.work+(28*h+22)*ps.length+1 := by
  induction ps generalizing out with
  | nil =>
    exact ⟨hv,by intro x; simp [markList],rfl,by simp [markList]⟩
  | cons p ps ih =>
    have hp:=hb p List.mem_cons_self
    have hv':=(MaskedOrdered.add_valid out.keys capacity p hv hc hp)
    have ht:=ih (mark capacity p out) hv' (fun x hx=>hb x (List.mem_cons_of_mem p hx))
    rw [markList]
    refine ⟨ht.1,?_,?_,?_⟩
    · intro x
      rw [ht.2.1]
      change (x∈ps ∨ x∈(MaskedOrdered.add out.keys capacity p).1.tree.entries) ↔ _
      rw [MaskedOrdered.add_mem out.keys capacity p x hv hc hp,List.mem_cons]
      simp only [eq_comm,or_assoc,or_left_comm]
    · have h:=ht.2.2.1
      change _=out.requests+1+ps.length at h
      change _=out.requests+(ps.length+1)
      omega
    · have htwork:=ht.2.2.2
      change _≤out.work+(MaskedOrdered.add out.keys capacity p).2.work+4+(28*h+22)*ps.length+1 at htwork
      have hw:=MaskedOrdered.insert_work out.keys.tree capacity p
      change _≤out.work+(28*h+22)*(ps.length+1)+1
      rw [Nat.mul_succ]
      change (MaskedOrdered.add out.keys capacity p).2.work≤28*h+18 at hw
      omega

theorem markList_card (capacity : Nat) (ps : List Nat) (out : Marked h) :
    (markList capacity ps out).keys.positions.length≤out.keys.positions.length+ps.length := by
  induction ps generalizing out with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
    have hm : (mark capacity p out).keys.positions.length≤out.keys.positions.length+1 := by
      change (if (MaskedOrdered.insert out.keys.tree capacity p).inserted
        then p::out.keys.positions else out.keys.positions).length≤out.keys.positions.length+1
      split <;> simp
    have ht:=ih (mark capacity p out)
    change (markList capacity ps (mark capacity p out)).keys.positions.length≤_
    have hl : (p::ps).length=ps.length+1 := rfl
    rw [hl]
    omega

structure Change where
  keys : List Nat
  work : Nat
  deriving Repr

/-- Exact signed before/after neighborhoods plus the inserted or threshold
endpoint itself.  At most nine physical keys are requested. -/
def prepareChange (before after : Tree h) (capacity p : Nat) : Change :=
  let a:=around before capacity p
  let b:=around after capacity p
  ⟨p::(a.keys++b.keys),a.work+b.work+12⟩

theorem prepareChange_bounds (before after : Tree h) (capacity p : Nat) :
    (prepareChange before after capacity p).keys.length≤9 ∧
    (prepareChange before after capacity p).work≤56*h+68 := by
  have ha:=(around before capacity p).length
  have hb:=(around after capacity p).length
  have hwa:=around_work before capacity p
  have hwb:=around_work after capacity p
  simp only [prepareChange,List.length_cons,List.length_append]
  constructor <;> omega

theorem prepareChange_bounded (before after : Tree h) (capacity p : Nat)
    (hbg : before.Good) (hbf : before.Fits 0) (hag : after.Good) (haf : after.Fits 0)
    (hc : capacity=2^h) (hp : p<2^h) :
    ∀x,x∈(prepareChange before after capacity p).keys → x<2^h := by
  intro x hx
  change x∈p::((around before capacity p).keys++(around after capacity p).keys) at hx
  rcases List.mem_cons.mp hx with rfl|hx
  · exact hp
  · rcases List.mem_append.mp hx with hx|hx
    · have hm:=around_mem before capacity p x hbg hbf hc hx
      have hb:=Tree.within before 0 hbf x hm
      omega
    · have hm:=around_mem after capacity p x hag haf hc hx
      have hb:=Tree.within after 0 haf x hm
      omega

def markChange (before after : Tree h) (capacity p : Nat) (out : Marked h) : Marked h :=
  let ready:=prepareChange before after capacity p
  let marked:=markList capacity ready.keys out
  {marked with work:=marked.work+ready.work+3}

theorem markChange_spec (before after : Tree h) (capacity p : Nat) (out : Marked h)
    (hv : out.keys.Valid) (hbg : before.Good) (hbf : before.Fits 0)
    (hag : after.Good) (haf : after.Fits 0) (hc : capacity=2^h) (hp : p<2^h) :
    (markChange before after capacity p out).keys.Valid ∧
    (∀x,x∈(markChange before after capacity p out).keys.tree.entries ↔
      x∈(prepareChange before after capacity p).keys ∨ x∈out.keys.tree.entries) ∧
    (markChange before after capacity p out).requests≤out.requests+9 ∧
    (markChange before after capacity p out).keys.positions.length≤out.keys.positions.length+9 ∧
    (markChange before after capacity p out).work≤out.work+308*h+270 := by
  have hb:=prepareChange_bounded before after capacity p hbg hbf hag haf hc hp
  have hs:=markList_spec capacity (prepareChange before after capacity p).keys out hv hc hb
  have hn:=prepareChange_bounds before after capacity p
  have hcard:=markList_card capacity (prepareChange before after capacity p).keys out
  refine ⟨hs.1,hs.2.1,?_,?_,?_⟩
  · change (markList capacity (prepareChange before after capacity p).keys out).requests≤out.requests+9
    have hr:=hs.2.2.1
    omega
  · change (markList capacity (prepareChange before after capacity p).keys out).keys.positions.length≤_
    omega
  · change (markList capacity (prepareChange before after capacity p).keys out).work+
      (prepareChange before after capacity p).work+3≤out.work+308*h+270
    have hw:=hs.2.2.2
    have hm:=Nat.mul_le_mul_left (28*h+22) hn.1
    simp only [Nat.add_mul,Nat.mul_assoc] at hm hw
    omega

end REWB.MaskedTraversalDirty
