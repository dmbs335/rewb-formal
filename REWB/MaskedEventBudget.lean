import REWB.MaskedReporting

/-! Event creation for destructive bottom-up occurrence-set merging.

    This file counts actual transferred entries and the adjacency records
    emitted by ordered insertion.  It does not claim a fast ordered-set or
    priority-queue implementation.  In particular, the executable list
    implementation below is a reference for the event schedule, not a
    subquadratic all-start matcher.  List-length reads, list/log copying and
    queue maintenance are not bounded by the event-count theorems. -/
namespace REWB.MaskedEventBudget

inductive MergeTree where
  | leaf : Nat → MergeTree
  | node : MergeTree → MergeTree → MergeTree
  deriving Repr

def size : MergeTree → Nat
  | .leaf _ => 1
  | .node a b => size a+size b

def leaves : MergeTree → List Nat
  | .leaf p => [p]
  | .node a b => leaves a++leaves b

def lightVolume : MergeTree → Nat
  | .leaf _ => 0
  | .node a b => lightVolume a+lightVolume b+min (size a) (size b)

theorem size_pos (t : MergeTree) : 0<size t := by
  induction t with
  | leaf _ => exact Nat.zero_lt_one
  | node a b ha hb => simp only [size]; omega

private theorem log2_mono {a n : Nat} (ha : 0<a) (han : a≤n) :
    Nat.log2 a ≤ Nat.log2 n := by
  apply (Nat.le_log2 (by omega : n≠0)).mpr
  exact Nat.le_trans (Nat.log2_self_le (by omega : a≠0)) han

private theorem light_log2 {a b : Nat} (ha : 0<a) (hab : a≤b) :
    Nat.log2 a+1 ≤ Nat.log2 (a+b) := by
  apply (Nat.le_log2 (by omega : a+b≠0)).mpr
  rw [Nat.pow_succ]
  have hh := Nat.mul_le_mul_right 2 (Nat.log2_self_le (by omega : a≠0))
  omega

/-- Every light transfer pays for a doubling of its containing subtree.
    The bound is proved for the concrete recursive merge schedule. -/
theorem lightVolume_bound (t : MergeTree) :
    lightVolume t ≤ size t*Nat.log2 (size t) := by
  induction t with
  | leaf _ => simp [lightVolume,size]
  | node a b ha hb =>
    have hpa := size_pos a
    have hpb := size_pos b
    change lightVolume a+lightVolume b+min (size a) (size b) ≤
      (size a+size b)*Nat.log2 (size a+size b)
    by_cases hab : size a≤size b
    · rw [Nat.min_eq_left hab]
      have hla := light_log2 hpa hab
      have hlb := log2_mono hpb (show size b≤size a+size b by omega)
      have hma := Nat.mul_le_mul_left (size a) hla
      have hmb := Nat.mul_le_mul_left (size b) hlb
      simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul] at hma ⊢
      omega
    · have hba : size b≤size a := by omega
      rw [Nat.min_eq_right hba]
      have hlb := light_log2 hpb hba
      rw [Nat.add_comm (size b) (size a)] at hlb
      have hla := log2_mono hpa (show size a≤size a+size b by omega)
      have hma := Nat.mul_le_mul_left (size a) hla
      have hmb := Nat.mul_le_mul_left (size b) hlb
      simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul] at hmb ⊢
      omega

abbrev Edge := Nat × Nat

def edges : List Nat → List Edge
  | [] => []
  | [_] => []
  | a::b::xs => (a,b)::edges (b::xs)

theorem edges_length (xs : List Nat) : (edges xs).length=xs.length-1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      change (edges (y::ys)).length+1=(ys.length+1+1)-1
      rw [ih]
      simp only [List.length_cons]
      omega

structure Insertion where
  positions : List Nat
  fresh : List Edge
  retired : List Edge
  comparisons : Nat
  deriving Repr

/-- Reference ordered insertion.  Fresh and retired adjacency records are
    materialized at the insertion point, never rebuilt for the whole set.
    Distinct input positions make these ordinary set adjacencies; the edge
    replacement certificate below also holds as a list identity. -/
def insert (p : Nat) : List Nat → Insertion
  | [] => ⟨[p],[],[],0⟩
  | x::xs =>
    if p≤x then ⟨p::x::xs,[(p,x)],[],1⟩
    else match xs with
    | [] => ⟨[x,p],[(x,p)],[],1⟩
    | y::ys =>
      if p≤y then ⟨x::p::y::ys,[(x,p),(p,y)],[(x,y)],2⟩
      else
        let r := insert p (y::ys)
        { r with positions := x::r.positions, comparisons := r.comparisons+2 }

private theorem insert_front (p x : Nat) (xs : List Nat) (hp : p≤x) :
    insert p (x::xs) = ⟨p::x::xs,[(p,x)],[],1⟩ := by
  cases xs <;> simp only [insert,hp,if_true]

private theorem insert_last (p x : Nat) (hp : ¬p≤x) :
    insert p [x] = ⟨[x,p],[(x,p)],[],1⟩ := by
  simp only [insert,hp,if_false]

private theorem insert_middle (p x y : Nat) (ys : List Nat)
    (hp : ¬p≤x) (hy : p≤y) :
    insert p (x::y::ys) = ⟨x::p::y::ys,[(x,p),(p,y)],[(x,y)],2⟩ := by
  simp only [insert,hp,hy,if_false,if_true]

private theorem insert_deep (p x y : Nat) (ys : List Nat)
    (hp : ¬p≤x) (hy : ¬p≤y) :
    insert p (x::y::ys) =
      { insert p (y::ys) with
        positions := x::(insert p (y::ys)).positions,
        comparisons := (insert p (y::ys)).comparisons+2 } := by
  rw [insert]
  simp only [hp,hy,if_false]

theorem insert_length (p : Nat) (xs : List Nat) :
    (insert p xs).positions.length=xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hp : p≤x
    · rw [insert_front p x xs hp]
      rfl
    · cases xs with
      | nil => rw [insert_last p x hp]; rfl
      | cons y ys =>
        by_cases hy : p≤y
        · rw [insert_middle p x y ys hp hy]; rfl
        · rw [insert_deep p x y ys hp hy]
          change (insert p (y::ys)).positions.length+1=(y::ys).length+1+1
          rw [ih]

theorem insert_fresh_bound (p : Nat) (xs : List Nat) :
    (insert p xs).fresh.length ≤ 2 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    by_cases hp : p≤x
    · rw [insert_front p x xs hp]; simp
    · cases xs with
      | nil => rw [insert_last p x hp]; simp
      | cons y ys =>
        by_cases hy : p≤y
        · rw [insert_middle p x y ys hp hy]; simp
        · rw [insert_deep p x y ys hp hy]
          exact ih

theorem insert_retired_bound (p : Nat) (xs : List Nat) :
    (insert p xs).retired.length ≤ 1 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    by_cases hp : p≤x
    · rw [insert_front p x xs hp]; simp
    · cases xs with
      | nil => rw [insert_last p x hp]; simp
      | cons y ys =>
        by_cases hy : p≤y
        · rw [insert_middle p x y ys hp hy]; simp
        · rw [insert_deep p x y ys hp hy]
          exact ih

theorem insert_comparisons (p : Nat) (xs : List Nat) :
    (insert p xs).comparisons ≤ 2*xs.length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    by_cases hp : p≤x
    · rw [insert_front p x xs hp]
      simp only [List.length_cons]
      omega
    · cases xs with
      | nil => rw [insert_last p x hp]; simp
      | cons y ys =>
        by_cases hy : p≤y
        · rw [insert_middle p x y ys hp hy]
          simp only [List.length_cons]
          omega
        · rw [insert_deep p x y ys hp hy]
          simp only [List.length_cons] at ih ⊢
          omega

private theorem insert_head (p x : Nat) (xs : List Nat) (hp : ¬p≤x) :
    ∃ ys, (insert p (x::xs)).positions=x::ys := by
  cases xs with
  | nil => rw [insert_last p x hp]; exact ⟨[p],rfl⟩
  | cons y ys =>
    by_cases hy : p≤y
    · rw [insert_middle p x y ys hp hy]; exact ⟨p::y::ys,rfl⟩
    · rw [insert_deep p x y ys hp hy]
      exact ⟨(insert p (y::ys)).positions,rfl⟩

/-- Exact local repair, with an unchanged prefix and suffix.  Hence the
    generated records are tied to the actual insertion operation rather
    than being an arbitrary externally supplied event count. -/
theorem insert_edge_repair (p : Nat) (xs : List Nat) :
    ∃ pre post : List Edge,
      edges (insert p xs).positions = pre++(insert p xs).fresh++post ∧
      edges xs = pre++(insert p xs).retired++post := by
  induction xs with
  | nil => exact ⟨[],[],rfl,rfl⟩
  | cons x xs ih =>
    by_cases hp : p≤x
    · rw [insert_front p x xs hp]
      exact ⟨[],edges (x::xs),rfl,rfl⟩
    · cases xs with
      | nil =>
        rw [insert_last p x hp]
        exact ⟨[],[],rfl,rfl⟩
      | cons y ys =>
        by_cases hy : p≤y
        · rw [insert_middle p x y ys hp hy]
          exact ⟨[],edges (y::ys),rfl,rfl⟩
        · obtain ⟨pre,post,ha,hb⟩ := ih
          obtain ⟨zs,hhead⟩ := insert_head p y ys hy
          rw [insert_deep p x y ys hp hy]
          refine ⟨(x,y)::pre,post,?_,?_⟩
          · change edges (x::(insert p (y::ys)).positions) =
              ((x,y)::pre)++(insert p (y::ys)).fresh++post
            rw [hhead]
            change (x,y)::edges (y::zs)=(x,y)::(pre++(insert p (y::ys)).fresh++post)
            rw [← hhead,ha]
          · change (x,y)::edges (y::ys)=(x,y)::(pre++(insert p (y::ys)).retired++post)
            rw [hb]

theorem insert_balance (p : Nat) (xs : List Nat) :
    (insert p xs).fresh.length+(edges xs).length =
      (edges (insert p xs).positions).length+(insert p xs).retired.length := by
  obtain ⟨pre,post,ha,hb⟩ := insert_edge_repair p xs
  have hla := congrArg List.length ha
  have hlb := congrArg List.length hb
  simp only [List.length_append] at hla hlb
  omega

theorem insert_mem (p x : Nat) (xs : List Nat) :
    x ∈ (insert p xs).positions ↔ x=p ∨ x∈xs := by
  induction xs with
  | nil => simp [insert]
  | cons a xs ih =>
    by_cases hp : p≤a
    · rw [insert_front p a xs hp]
      simp
    · cases xs with
      | nil =>
        rw [insert_last p a hp]
        simp only [List.mem_cons,List.not_mem_nil,or_false]
        exact or_comm
      | cons b bs =>
        by_cases hb : p≤b
        · rw [insert_middle p a b bs hp hb]
          simp only [List.mem_cons]
          exact or_left_comm
        · rw [insert_deep p a b bs hp hb]
          change x∈a::(insert p (b::bs)).positions ↔ x=p ∨ x∈a::b::bs
          rw [List.mem_cons,ih]
          simp only [List.mem_cons]
          exact or_left_comm

theorem insert_perm (p : Nat) (xs : List Nat) :
    (insert p xs).positions.Perm (p::xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    by_cases hp : p≤x
    · rw [insert_front p x xs hp]
    · cases xs with
      | nil =>
        rw [insert_last p x hp]
        exact List.Perm.swap _ _ _
      | cons y ys =>
        by_cases hy : p≤y
        · rw [insert_middle p x y ys hp hy]
          exact List.Perm.swap _ _ _
        · rw [insert_deep p x y ys hp hy]
          exact (ih.cons x).trans (List.Perm.swap _ _ _)

private theorem insert_positions (p x : Nat) (xs : List Nat) :
    (insert p (x::xs)).positions =
      if p≤x then p::x::xs else x::(insert p xs).positions := by
  by_cases hp : p≤x
  · rw [insert_front p x xs hp,if_pos hp]
  · rw [if_neg hp]
    cases xs with
    | nil => rw [insert_last p x hp]; rfl
    | cons y ys =>
      by_cases hy : p≤y
      · rw [insert_middle p x y ys hp hy,insert_front p y ys hy]
      · rw [insert_deep p x y ys hp hy]

theorem insert_ordered (p : Nat) (xs : List Nat) (hs : xs.Pairwise (·≤·)) :
    (insert p xs).positions.Pairwise (·≤·) := by
  induction xs with
  | nil => simp [insert]
  | cons x xs ih =>
    obtain ⟨hall,ht⟩ := List.pairwise_cons.mp hs
    rw [insert_positions]
    by_cases hp : p≤x
    · rw [if_pos hp,List.pairwise_cons]
      refine ⟨?_,hs⟩
      intro y hy
      rcases List.mem_cons.mp hy with he | hm
      · subst y
        exact hp
      · exact Nat.le_trans hp (hall y hm)
    · rw [if_neg hp,List.pairwise_cons]
      refine ⟨?_,ih ht⟩
      intro y hy
      rcases (insert_mem p y xs).mp hy with he | hm
      · subst y
        omega
      · exact hall y hm

structure Trace where
  positions : List Nat
  transfers : Nat
  fresh : List Edge
  retired : List Edge
  comparisons : Nat
  deriving Repr

/-- Every transferred entry invokes exactly one ordered insertion. -/
def insertMany : List Nat → List Nat → Trace
  | [], dst => ⟨dst,0,[],[],0⟩
  | p::ps, dst =>
    let step := insert p dst
    let rest := insertMany ps step.positions
    ⟨rest.positions,rest.transfers+1,step.fresh++rest.fresh,
      step.retired++rest.retired,step.comparisons+rest.comparisons⟩

theorem insertMany_length (src dst : List Nat) :
    (insertMany src dst).positions.length=src.length+dst.length := by
  induction src generalizing dst with
  | nil => simp only [insertMany,List.length_nil,Nat.zero_add]
  | cons p ps ih =>
    change (insertMany ps (insert p dst).positions).positions.length=_
    rw [ih,insert_length]
    simp only [List.length_cons]
    omega

theorem insertMany_transfers (src dst : List Nat) :
    (insertMany src dst).transfers=src.length := by
  induction src generalizing dst with
  | nil => rfl
  | cons p ps ih =>
    change (insertMany ps (insert p dst).positions).transfers+1=ps.length+1
    rw [ih]

theorem insertMany_perm (src dst : List Nat) :
    (insertMany src dst).positions.Perm (src++dst) := by
  induction src generalizing dst with
  | nil => exact List.Perm.refl _
  | cons p ps ih =>
    change (insertMany ps (insert p dst).positions).positions.Perm (p::(ps++dst))
    exact ((ih (insert p dst).positions).trans
      (List.Perm.append_left ps (insert_perm p dst))).trans List.perm_middle

theorem insertMany_ordered (src dst : List Nat) (hs : dst.Pairwise (·≤·)) :
    (insertMany src dst).positions.Pairwise (·≤·) := by
  induction src generalizing dst with
  | nil => exact hs
  | cons p ps ih => exact ih _ (insert_ordered p dst hs)

theorem insertMany_fresh (src dst : List Nat) :
    (insertMany src dst).fresh.length ≤ 2*src.length := by
  induction src generalizing dst with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
    have hs := insert_fresh_bound p dst
    have hr := ih (insert p dst).positions
    change ((insert p dst).fresh++(insertMany ps (insert p dst).positions).fresh).length ≤ _
    rw [List.length_append]
    simp only [List.length_cons]
    omega

theorem insertMany_retired (src dst : List Nat) :
    (insertMany src dst).retired.length ≤ src.length := by
  induction src generalizing dst with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
    have hs := insert_retired_bound p dst
    have hr := ih (insert p dst).positions
    change ((insert p dst).retired++(insertMany ps (insert p dst).positions).retired).length ≤ _
    rw [List.length_append]
    simp only [List.length_cons]
    omega

theorem insertMany_balance (src dst : List Nat) :
    (insertMany src dst).fresh.length+(edges dst).length =
      (edges (insertMany src dst).positions).length+(insertMany src dst).retired.length := by
  induction src generalizing dst with
  | nil => simp [insertMany]
  | cons p ps ih =>
    have hs := insert_balance p dst
    have hr := ih (insert p dst).positions
    simp only [insertMany,List.length_append]
    omega

/-- The larger child is reused as destination; only entries from the
    smaller child are reinserted.  Prior event logs are retained once.
    The absorbed child's live adjacencies are explicitly retired too. -/
def build : MergeTree → Trace
  | .leaf p => ⟨[p],0,[],[],0⟩
  | .node a b =>
    let x := build a
    let y := build b
    let joined := if x.positions.length≤y.positions.length then
        insertMany x.positions y.positions
      else insertMany y.positions x.positions
    let discarded := if x.positions.length≤y.positions.length then
        edges x.positions else edges y.positions
    ⟨joined.positions,x.transfers+y.transfers+joined.transfers,
      x.fresh++y.fresh++joined.fresh,x.retired++y.retired++discarded++joined.retired,
      x.comparisons+y.comparisons+joined.comparisons⟩

theorem build_length (t : MergeTree) : (build t).positions.length=size t := by
  induction t with
  | leaf _ => rfl
  | node a b ha hb =>
    simp only [build]
    split <;> simp only [insertMany_length,ha,hb,size]
    exact Nat.add_comm _ _

theorem build_perm (t : MergeTree) : (build t).positions.Perm (leaves t) := by
  induction t with
  | leaf _ => exact List.Perm.refl _
  | node a b ha hb =>
    simp only [build]
    split
    · exact (insertMany_perm (build a).positions (build b).positions).trans (ha.append hb)
    · exact ((insertMany_perm (build b).positions (build a).positions).trans
        List.perm_append_comm).trans (ha.append hb)

theorem build_ordered (t : MergeTree) : (build t).positions.Pairwise (·≤·) := by
  induction t with
  | leaf _ => simp [build]
  | node a b ha hb =>
    simp only [build]
    split
    · exact insertMany_ordered _ _ hb
    · exact insertMany_ordered _ _ ha

theorem build_nodup (t : MergeTree) (h : (leaves t).Nodup) :
    (build t).positions.Nodup := (build_perm t).symm.nodup h

theorem build_strict (t : MergeTree) (h : (leaves t).Nodup) :
    (build t).positions.Pairwise (·<·) := by
  apply ((build_ordered t).and (build_nodup t h)).imp
  intro a b hab
  omega

theorem build_transfers (t : MergeTree) : (build t).transfers=lightVolume t := by
  induction t with
  | leaf _ => rfl
  | node a b ha hb =>
    simp only [build]
    split
    next hp =>
      rw [insertMany_transfers,build_length,ha,hb]
      rw [build_length,build_length] at hp
      simp only [lightVolume,Nat.min_eq_left hp]
    next hp =>
      rw [insertMany_transfers,build_length,ha,hb]
      rw [build_length,build_length] at hp
      have hb : size b≤size a := by omega
      simp only [lightVolume,Nat.min_eq_right hb]

theorem build_fresh (t : MergeTree) :
    (build t).fresh.length ≤ 2*lightVolume t := by
  induction t with
  | leaf _ => exact Nat.le_refl _
  | node a b ha hb =>
    simp only [build]
    split
    next hp =>
      have hj := insertMany_fresh (build a).positions (build b).positions
      rw [build_length] at hj
      rw [build_length,build_length] at hp
      simp only [List.length_append,lightVolume,Nat.min_eq_left hp]
      omega
    next hp =>
      have hj := insertMany_fresh (build b).positions (build a).positions
      rw [build_length] at hj
      rw [build_length,build_length] at hp
      have hba : size b≤size a := by omega
      simp only [List.length_append,lightVolume,Nat.min_eq_right hba]
      omega

theorem build_retired (t : MergeTree) :
    (build t).retired.length ≤ 2*lightVolume t := by
  induction t with
  | leaf _ => exact Nat.le_refl _
  | node a b ha hb =>
    simp only [build]
    split
    next hp =>
      have hj := insertMany_retired (build a).positions (build b).positions
      rw [build_length] at hj
      rw [build_length,build_length] at hp
      simp only [List.length_append,edges_length,build_length,lightVolume,Nat.min_eq_left hp]
      omega
    next hp =>
      have hj := insertMany_retired (build b).positions (build a).positions
      rw [build_length] at hj
      rw [build_length,build_length] at hp
      have hba : size b≤size a := by omega
      simp only [List.length_append,edges_length,build_length,lightVolume,Nat.min_eq_right hba]
      omega

theorem build_balance (t : MergeTree) :
    (build t).fresh.length = (edges (build t).positions).length+(build t).retired.length := by
  induction t with
  | leaf _ => rfl
  | node a b ha hb =>
    simp only [build]
    split
    next hp =>
      simp only [hp,if_true,List.length_append]
      have hj := insertMany_balance (build a).positions (build b).positions
      omega
    next hp =>
      simp only [hp,if_false,List.length_append]
      have hj := insertMany_balance (build b).positions (build a).positions
      omega

theorem transfer_bound (t : MergeTree) :
    (build t).transfers ≤ size t*Nat.log2 (size t) := by
  rw [build_transfers]
  exact lightVolume_bound t

theorem generation_bound (t : MergeTree) :
    (build t).fresh.length ≤ 2*(size t*Nat.log2 (size t)) :=
  Nat.le_trans (build_fresh t) (Nat.mul_le_mul_left 2 (lightVolume_bound t))

inductive Kind where
  | density
  | overlap
  deriving DecidableEq, Repr

structure Threshold where
  edge : Edge
  kind : Kind
  level : Nat
  deriving DecidableEq, Repr

/-- When the represented length descends, density 2g≤L changes at 2g-1,
    and overlap g<L changes at g.  Positive gap is a geometry premise;
    every record is nevertheless finite even for malformed input. -/
def thresholds (e : Edge) : List Threshold :=
  [⟨e,.density,2*(e.2-e.1)-1⟩,⟨e,.overlap,e.2-e.1⟩]

theorem density_crossing (g fromLevel toLevel : Nat) (hg : 0<g) :
    (2*g≤fromLevel ∧ ¬2*g≤toLevel) ↔
      toLevel≤2*g-1 ∧ 2*g-1<fromLevel := by omega

theorem overlap_crossing (g fromLevel toLevel : Nat) :
    (g<fromLevel ∧ ¬g<toLevel) ↔ toLevel≤g ∧ g<fromLevel := by omega

theorem threshold_cannot_recross (threshold reached later : Nat)
    (hr : reached≤threshold) (hl : later≤reached) :
    ¬ threshold<later := by omega

def records (t : MergeTree) : List Threshold :=
  (build t).fresh.flatMap thresholds

private theorem threshold_length (es : List Edge) :
    (es.flatMap thresholds).length=2*es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.length_append,thresholds,List.length_cons,
      List.length_nil,ih]
    omega

theorem records_length (t : MergeTree) :
    (records t).length=2*(build t).fresh.length := threshold_length _

theorem records_bound (t : MergeTree) :
    (records t).length ≤ 4*(size t*Nat.log2 (size t)) := by
  rw [records_length]
  have hh := generation_bound t
  omega

/-- A record is consumed at most once when the queue only removes entries.
    Cancelled/stale entries are included in this count.  An implementation
    that re-enqueues old records does not satisfy this invariant. -/
theorem oneShot_bound (t : MergeTree) (processed pending : List Threshold)
    (h : (processed++pending).Perm (records t)) :
    processed.length ≤ 4*(size t*Nat.log2 (size t)) := by
  have hl := h.length_eq
  rw [List.length_append] at hl
  have hb := records_bound t
  omega

/-- On a unary suffix chain, each shorter word adds one occurrence.  This
    deliberately bad schedule rebuilds all current adjacencies at every
    level, instead of preserving their generations through the heavy path. -/
def unaryRebuild : Nat → List Edge
  | 0 => []
  | n+1 => unaryRebuild n ++ edges (List.range (n+1))

theorem unaryRebuild_succ (n : Nat) :
    (unaryRebuild (n+1)).length=(unaryRebuild n).length+n := by
  simp only [unaryRebuild,List.length_append,edges_length,List.length_range]
  omega

/-- Rebuilding the unchanged adjacencies incurs exactly N(N-1)/2 records.
    Thus small-to-large insertion alone cannot justify resetting the event
    queue at every suffix-tree edge. -/
theorem unaryRebuild_quadratic (n : Nat) :
    2*(unaryRebuild n).length=n*(n-1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [unaryRebuild_succ,Nat.mul_add,ih]
    by_cases hn : n=0
    · subst n
      decide
    · have hpos : 1≤n := by omega
      have he : n*(n-1)+n=n*n := by
        calc
          n*(n-1)+n = n*((n-1)+1) := by rw [Nat.mul_add,Nat.mul_one]
          _ = n*n := by rw [Nat.sub_add_cancel hpos]
      simp only [Nat.add_sub_cancel,Nat.add_mul,Nat.one_mul]
      omega

theorem unaryRebuild_100 : (unaryRebuild 100).length=4950 := by
  have hh := unaryRebuild_quadratic 100
  omega

theorem unaryIncremental_length (n : Nat) :
    (edges (List.range n)).length=n-1 := by
  rw [edges_length,List.length_range]

/-- The contrast is executable and kernel checked: 4,950 rebuilt records
    versus 99 persistent adjacency generations on 100 unary suffixes. -/
theorem unary_reset_regression :
    (unaryRebuild 100).length=4950 ∧ (edges (List.range 100)).length=99 :=
  ⟨unaryRebuild_100,unaryIncremental_length 100⟩

def sampleTree : MergeTree :=
  .node (.node (.leaf 2) (.leaf 0)) (.node (.leaf 3) (.leaf 1))

/-- Actual small-to-large build and emitted event trace. -/
theorem sample_execution :
    (build sampleTree).positions=[0,1,2,3] ∧
      (build sampleTree).transfers=4 ∧ (build sampleTree).fresh.length=5 ∧
      (build sampleTree).retired.length=2 ∧ (records sampleTree).length=10 := by decide

end REWB.MaskedEventBudget
