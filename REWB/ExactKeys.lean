import REWB.LongSourceCoverage
import REWB.PeriodicBudgets

/-! Deterministic interning of finite-alphabet words. Child slots are
    materialized lists, never chains of function updates. A shared registry
    assigns one persistent natural-number identifier to each inserted word.
    Identifiers are canonical within that registry, not across independent
    insertion histories. Counters measure slot visits and terminal actions. -/
namespace REWB.ExactKeys

inductive Trie (σ : Nat) where
  | node : Option Nat→List (Trie σ)→Trie σ
  deriving Repr

variable {σ : Nat}
abbrev KeyWord (σ : Nat) := List (Fin σ)

def empty : Trie σ := .node none []
def label : Trie σ→Option Nat | .node r _ => r
def children : Trie σ→List (Trie σ) | .node _ cs => cs

def readSlot : List (Trie σ)→Nat→Trie σ×Nat
  | [],_ => (empty,1)
  | t::_,0 => (t,1)
  | _::ts,i+1 =>
    let r := readSlot ts i
    (r.1,r.2+1)

theorem readSlot_value (ts : List (Trie σ)) (i : Nat) :
    (readSlot ts i).1=ts[i]?.getD empty := by
  induction ts generalizing i with
  | nil => simp [readSlot]
  | cons t ts ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem readSlot_cost (ts : List (Trie σ)) (i : Nat) :
    (readSlot ts i).2≤i+1 := by
  induction ts generalizing i with
  | nil => simp [readSlot]
  | cons t ts ih =>
    cases i with
    | zero => exact Nat.le_refl _
    | succ i =>
      change (readSlot ts i).2+1≤i+1+1
      exact Nat.add_le_add_right (ih i) 1

/-- Materialize exactly k slots, preserving existing slots and filling
    absent ones with the empty trie. Only the first k slots are inspected. -/
def pad : Nat→List (Trie σ)→List (Trie σ)×Nat
  | 0,_ => ([],0)
  | k+1,ts =>
    let r := pad k ts.tail
    (ts.headD empty::r.1,r.2+1)

theorem pad_length (k : Nat) (ts : List (Trie σ)) : (pad k ts).1.length=k := by
  induction k generalizing ts with
  | zero => rfl
  | succ k ih =>
    change (pad k ts.tail).1.length+1=k+1
    rw [ih]

theorem pad_cost (k : Nat) (ts : List (Trie σ)) : (pad k ts).2=k := by
  induction k generalizing ts with
  | zero => rfl
  | succ k ih =>
    change (pad k ts.tail).2+1=k+1
    rw [ih]

theorem pad_read (k i : Nat) (ts : List (Trie σ)) (hi : i<k) :
    (pad k ts).1[i]?.getD empty=ts[i]?.getD empty := by
  induction k generalizing i ts with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => cases ts <;> rfl
    | succ i =>
      change (pad k ts.tail).1[i]?.getD empty=ts[i+1]?.getD empty
      rw [ih i ts.tail (by omega)]
      cases ts <;> rfl

def replaceSlot : List (Trie σ)→Nat→Trie σ→List (Trie σ)×Nat
  | [],_,_ => ([],1)
  | _::ts,0,u => (u::ts,1)
  | t::ts,i+1,u =>
    let r := replaceSlot ts i u
    (t::r.1,r.2+1)

theorem replaceSlot_cost (ts : List (Trie σ)) (i : Nat) (u : Trie σ) :
    (replaceSlot ts i u).2≤i+1 := by
  induction ts generalizing i with
  | nil => simp [replaceSlot]
  | cons t ts ih =>
    cases i with
    | zero => exact Nat.le_refl _
    | succ i =>
      change (replaceSlot ts i u).2+1≤i+1+1
      exact Nat.add_le_add_right (ih i) 1

theorem replaceSlot_read (ts : List (Trie σ)) (i j : Nat) (u : Trie σ)
    (hi : i<ts.length) :
    (replaceSlot ts i u).1[j]?.getD empty=
      if j=i then u else ts[j]?.getD empty := by
  induction ts generalizing i j with
  | nil => simp at hi
  | cons t ts ih =>
    cases i with
    | zero =>
      cases j <;> simp [replaceSlot]
    | succ i =>
      cases j with
      | zero => simp [replaceSlot]
      | succ j =>
        change (replaceSlot ts i u).1[j]?.getD empty=
          if j+1=i+1 then u else ts[j]?.getD empty
        rw [ih i j (by simpa using hi)]
        simp

def child (t : Trie σ) (a : Fin σ) : Trie σ := (children t)[a.val]?.getD empty

def lookup (t : Trie σ) : KeyWord σ→Option Nat
  | [] => label t
  | a::w => lookup (child t a) w

theorem lookup_empty (w : KeyWord σ) : lookup empty w=none := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ih

def withLabel (t : Trie σ) (r : Nat) : Trie σ := .node (some r) (children t)

def withChild (t : Trie σ) (a : Fin σ) (u : Trie σ) : Trie σ :=
  .node (label t) (replaceSlot (pad σ (children t)).1 a.val u).1

theorem child_withChild (t : Trie σ) (a b : Fin σ) (u : Trie σ) :
    child (withChild t a u) b=if b=a then u else child t b := by
  unfold child withChild children
  rw [replaceSlot_read _ a.val b.val u (by rw [pad_length]; exact a.isLt),
    pad_read σ b.val _ b.isLt]
  by_cases h : b=a
  · simp [h]
  · have hv : b.val≠a.val := fun he=>h (Fin.ext he)
    simp [h,hv]

theorem lookup_withChild_cons (t : Trie σ) (a b : Fin σ) (u : Trie σ) (w : KeyWord σ) :
    lookup (withChild t a u) (b::w)=if b=a then lookup u w else lookup t (b::w) := by
  change lookup (child (withChild t a u) b) w=_
  rw [child_withChild]
  by_cases h : b=a <;> simp [h,lookup]

structure Result (σ : Nat) where
  tree : Trie σ
  rank : Nat
  next : Nat
  work : Nat

def intern : KeyWord σ→Trie σ→Nat→Result σ
  | [],t,next =>
    match label t with
    | some r => ⟨t,r,next,1⟩
    | none => ⟨withLabel t next,next,next+1,1⟩
  | a::w,t,next =>
    let slots := pad σ (children t)
    let old := readSlot slots.1 a.val
    let r := intern w old.1 next
    let changed := replaceSlot slots.1 a.val r.tree
    ⟨.node (label t) changed.1,r.rank,r.next,slots.2+old.2+r.work+changed.2+1⟩

theorem intern_cons_tree (a : Fin σ) (w : KeyWord σ) (t : Trie σ) (next : Nat) :
    (intern (a::w) t next).tree=withChild t a (intern w (child t a) next).tree := by
  simp only [intern,readSlot_value,pad_read σ a.val _ a.isLt,child,withChild]

theorem intern_cons_rank (a : Fin σ) (w : KeyWord σ) (t : Trie σ) (next : Nat) :
    (intern (a::w) t next).rank=(intern w (child t a) next).rank := by
  simp only [intern,readSlot_value,pad_read σ a.val _ a.isLt,child]

theorem intern_cons_next (a : Fin σ) (w : KeyWord σ) (t : Trie σ) (next : Nat) :
    (intern (a::w) t next).next=(intern w (child t a) next).next := by
  simp only [intern,readSlot_value,pad_read σ a.val _ a.isLt,child]

/-- Either recover an existing identifier or consume exactly one fresh
    identifier; numeric values never encode the word's characters. -/
theorem intern_rank (w : KeyWord σ) (t : Trie σ) (next : Nat) :
    (lookup t w=some (intern w t next).rank ∧ (intern w t next).next=next) ∨
    (lookup t w=none ∧ (intern w t next).rank=next ∧ (intern w t next).next=next+1) := by
  induction w generalizing t with
  | nil =>
    unfold intern lookup
    cases he : label t with
    | none => exact Or.inr ⟨rfl,rfl,rfl⟩
    | some r => exact Or.inl ⟨rfl,rfl⟩
  | cons a w ih =>
    rw [intern_cons_rank,intern_cons_next]
    exact ih (child t a)

/-- Interning changes the lookup map at only the inserted word. -/
theorem intern_lookup (w : KeyWord σ) (t : Trie σ) (next : Nat) (v : KeyWord σ) :
    lookup (intern w t next).tree v=
      if v=w then some (intern w t next).rank else lookup t v := by
  induction w generalizing t v with
  | nil =>
    cases v with
    | nil =>
      unfold intern
      cases he : label t with
      | none => rfl
      | some r =>
        change label t=some r
        exact he
    | cons a v =>
      unfold intern
      cases he : label t <;> simp [he,lookup,withLabel,child,children]
  | cons a w ih =>
    rw [intern_cons_tree,intern_cons_rank]
    cases v with
    | nil => rfl
    | cons b v =>
      rw [lookup_withChild_cons]
      by_cases h : b=a
      · subst b
        rw [if_pos rfl,ih]
        simp [lookup]
      · simp [h]

theorem intern_cost (w : KeyWord σ) (t : Trie σ) (next : Nat) :
    (intern w t next).work≤(3*σ+1)*w.length+1 := by
  induction w generalizing t with
  | nil =>
    unfold intern
    cases label t <;> simp
  | cons a w ih =>
    let slots := pad σ (children t)
    let old := readSlot slots.1 a.val
    let r := intern w old.1 next
    have hpad : slots.2=σ := pad_cost _ _
    have hread : old.2≤σ := Nat.le_trans (readSlot_cost _ _) (by have h := a.isLt; omega)
    have hset : (replaceSlot slots.1 a.val r.tree).2≤σ :=
      Nat.le_trans (replaceSlot_cost _ _ _) (by have h := a.isLt; omega)
    have hr : r.work≤(3*σ+1)*w.length+1 := ih old.1
    change slots.2+old.2+r.work+(replaceSlot slots.1 a.val r.tree).2+1≤
      (3*σ+1)*(w.length+1)+1
    rw [Nat.mul_succ]
    omega

theorem intern_next_mono (w : KeyWord σ) (t : Trie σ) (next : Nat) :
    next≤(intern w t next).next := by
  rcases intern_rank w t next with h|h <;> omega

theorem intern_next_le (w : KeyWord σ) (t : Trie σ) (next : Nat) :
    (intern w t next).next≤next+1 := by
  rcases intern_rank w t next with h|h <;> omega

theorem intern_existing (w : KeyWord σ) (t : Trie σ) (next r : Nat)
    (hr : lookup t w=some r) :
    (intern w t next).rank=r ∧ (intern w t next).next=next := by
  rcases intern_rank w t next with h|h
  · exact ⟨Option.some.inj (h.1.symm.trans hr),h.2⟩
  · rw [hr] at h
    cases h.1

theorem intern_preserves (w : KeyWord σ) (t : Trie σ) (next : Nat)
    (v : KeyWord σ) (r : Nat) (hr : lookup t v=some r) :
    lookup (intern w t next).tree v=some r := by
  rw [intern_lookup]
  by_cases h : v=w
  · subst v
    rw [if_pos rfl,(intern_existing w t next r hr).1]
  · rw [if_neg h]
    exact hr

structure Registry (σ : Nat) where
  tree : Trie σ
  next : Nat

def Registry.Valid (R : Registry σ) : Prop :=
  (∀ w r,lookup R.tree w=some r→r<R.next) ∧
  (∀ u v r,lookup R.tree u=some r→lookup R.tree v=some r→u=v)

def initial : Registry σ := ⟨empty,0⟩

theorem initial_valid : (initial : Registry σ).Valid := by
  constructor
  · intro w r hr
    change lookup empty w=some r at hr
    rw [lookup_empty] at hr
    cases hr
  · intro u v r hu _
    change lookup empty u=some r at hu
    rw [lookup_empty] at hu
    cases hu

structure Assigned (σ : Nat) where
  registry : Registry σ
  rank : Nat
  work : Nat

def assign (R : Registry σ) (w : KeyWord σ) : Assigned σ :=
  let r := intern w R.tree R.next
  ⟨⟨r.tree,r.next⟩,r.rank,r.work⟩

theorem assign_lookup (R : Registry σ) (w : KeyWord σ) :
    lookup (assign R w).registry.tree w=some (assign R w).rank := by
  change lookup (intern w R.tree R.next).tree w=some (intern w R.tree R.next).rank
  rw [intern_lookup,if_pos rfl]

theorem assign_preserves (R : Registry σ) (w v : KeyWord σ) (r : Nat)
    (hr : lookup R.tree v=some r) :
    lookup (assign R w).registry.tree v=some r :=
  intern_preserves w R.tree R.next v r hr

theorem assign_rank_unique (R : Registry σ) (hR : R.Valid) (w v : KeyWord σ)
    (hv : lookup (assign R w).registry.tree v=some (assign R w).rank) : v=w := by
  by_cases h : v=w
  · exact h
  · change lookup (intern w R.tree R.next).tree v=some (intern w R.tree R.next).rank at hv
    rw [intern_lookup,if_neg h] at hv
    rcases intern_rank w R.tree R.next with old|fresh
    · exact hR.2 v w _ hv old.1
    · have hb := hR.1 v _ hv
      omega

theorem assign_valid (R : Registry σ) (hR : R.Valid) (w : KeyWord σ) :
    (assign R w).registry.Valid := by
  have hm := intern_next_mono w R.tree R.next
  have hr : (assign R w).rank<(assign R w).registry.next := by
    change (intern w R.tree R.next).rank<(intern w R.tree R.next).next
    rcases intern_rank w R.tree R.next with old|fresh
    · have hb := hR.1 w _ old.1
      omega
    · omega
  constructor
  · intro v r hv
    by_cases h : v=w
    · subst v
      have he := (assign_lookup R w).symm.trans hv
      have he' := Option.some.inj he
      omega
    · change lookup (intern w R.tree R.next).tree v=some r at hv
      rw [intern_lookup,if_neg h] at hv
      have hb := hR.1 v r hv
      change r<(intern w R.tree R.next).next
      omega
  · intro u v r hu hv
    by_cases h1 : u=w
    · subst u
      have he := Option.some.inj ((assign_lookup R w).symm.trans hu)
      rw [← he] at hv
      exact (assign_rank_unique R hR w v hv).symm
    · by_cases h2 : v=w
      · subst v
        have he := Option.some.inj ((assign_lookup R w).symm.trans hv)
        rw [← he] at hu
        exact assign_rank_unique R hR w u hu
      · change lookup (intern w R.tree R.next).tree u=some r at hu
        change lookup (intern w R.tree R.next).tree v=some r at hv
        rw [intern_lookup,if_neg h1] at hu
        rw [intern_lookup,if_neg h2] at hv
        exact hR.2 u v r hu hv

theorem rank_eq_iff (R : Registry σ) (hR : R.Valid) (u v : KeyWord σ) (r s : Nat)
    (hu : lookup R.tree u=some r) (hv : lookup R.tree v=some s) :
    r=s ↔ u=v := by
  constructor
  · intro h
    subst s
    exact hR.2 u v r hu hv
  · intro h
    subst v
    exact Option.some.inj (hu.symm.trans hv)

def characters : List (KeyWord σ)→Nat
  | [] => 0
  | w::ws => w.length+characters ws

structure Batch (σ : Nat) where
  registry : Registry σ
  entries : List (KeyWord σ×Nat)
  work : Nat

def internMany (R : Registry σ) : List (KeyWord σ)→Batch σ
  | [] => ⟨R,[],0⟩
  | w::ws =>
    let a := assign R w
    let b := internMany a.registry ws
    ⟨b.registry,(w,a.rank)::b.entries,a.work+b.work⟩

theorem internMany_preserves (R : Registry σ) (ws : List (KeyWord σ))
    (v : KeyWord σ) (r : Nat) (hr : lookup R.tree v=some r) :
    lookup (internMany R ws).registry.tree v=some r := by
  induction ws generalizing R with
  | nil => exact hr
  | cons w ws ih => exact ih (assign R w).registry (assign_preserves R w v r hr)

theorem internMany_valid (R : Registry σ) (hR : R.Valid) (ws : List (KeyWord σ)) :
    (internMany R ws).registry.Valid := by
  induction ws generalizing R with
  | nil => exact hR
  | cons w ws ih => exact ih _ (assign_valid R hR w)

theorem internMany_words (R : Registry σ) (ws : List (KeyWord σ)) :
    (internMany R ws).entries.map Prod.fst=ws := by
  induction ws generalizing R with
  | nil => rfl
  | cons w ws ih =>
    change w::(internMany (assign R w).registry ws).entries.map Prod.fst=w::ws
    rw [ih]

theorem internMany_entries (R : Registry σ) (ws : List (KeyWord σ)) :
    ∀ e,e∈(internMany R ws).entries→lookup (internMany R ws).registry.tree e.1=some e.2 := by
  induction ws generalizing R with
  | nil => intro e he; simp [internMany] at he
  | cons w ws ih =>
    intro e he
    change e∈(w,(assign R w).rank)::(internMany (assign R w).registry ws).entries at he
    rcases List.mem_cons.mp he with he|he
    · subst e
      exact internMany_preserves _ ws w _ (assign_lookup R w)
    · exact ih _ e he

theorem internMany_cost (R : Registry σ) (ws : List (KeyWord σ)) :
    (internMany R ws).work≤(3*σ+1)*characters ws+ws.length := by
  induction ws generalizing R with
  | nil => simp [internMany,characters]
  | cons w ws ih =>
    have ha := intern_cost w R.tree R.next
    have hb := ih (assign R w).registry
    change (intern w R.tree R.next).work+(internMany (assign R w).registry ws).work≤
      (3*σ+1)*(w.length+characters ws)+(ws.length+1)
    rw [Nat.mul_add]
    omega

theorem internMany_next (R : Registry σ) (ws : List (KeyWord σ)) :
    (internMany R ws).registry.next≤R.next+ws.length := by
  induction ws generalizing R with
  | nil => simp [internMany]
  | cons w ws ih =>
    have ha := intern_next_le w R.tree R.next
    have hb := ih (assign R w).registry
    change (internMany (assign R w).registry ws).registry.next≤R.next+(ws.length+1)
    change (internMany (assign R w).registry ws).registry.next≤
      (intern w R.tree R.next).next+ws.length at hb
    omega

/-- Every returned identifier is a word-sized counter bounded by the
    starting counter plus the number of input keys. -/
theorem internMany_rank_bound (R : Registry σ) (hR : R.Valid) (ws : List (KeyWord σ))
    (e : KeyWord σ×Nat) (he : e∈(internMany R ws).entries) : e.2<R.next+ws.length := by
  have h := (internMany_valid R hR ws).1 e.1 e.2 (internMany_entries R ws e he)
  exact Nat.lt_of_lt_of_le h (internMany_next R ws)

theorem internMany_exact (R : Registry σ) (hR : R.Valid) (ws : List (KeyWord σ))
    (e f : KeyWord σ×Nat) (he : e∈(internMany R ws).entries)
    (hf : f∈(internMany R ws).entries) : e.2=f.2 ↔ e.1=f.1 :=
  rank_eq_iff _ (internMany_valid R hR ws) e.1 f.1 e.2 f.2
    (internMany_entries R ws e he) (internMany_entries R ws f hf)

structure Key where
  period : Nat
  wordRank : Nat
  residue : Nat
  deriving DecidableEq, Repr

/-- The product key retains period and residual length explicitly. It
    cannot confuse equal words belonging to different period/residue keys. -/
theorem key_eq_iff (R : Registry σ) (hR : R.Valid) (u v : KeyWord σ)
    (q p r s rho tau : Nat) (hu : lookup R.tree u=some r) (hv : lookup R.tree v=some s) :
    (⟨q,r,rho⟩ : Key)=⟨p,s,tau⟩ ↔ q=p ∧ rho=tau ∧ u=v := by
  rw [Key.mk.injEq,rank_eq_iff R hR u v r s hu hv]
  constructor
  · rintro ⟨h1,h2,h3⟩
    exact ⟨h1,h3,h2⟩
  · rintro ⟨h1,h2,h3⟩
    exact ⟨h1,h3,h2⟩

structure KeyAssigned (σ : Nat) where
  registry : Registry σ
  key : Key
  work : Nat

def internKey (R : Registry σ) (q : Nat) (w : KeyWord σ) (rho : Nat) : KeyAssigned σ :=
  let a := assign R w
  ⟨a.registry,⟨q,a.rank,rho⟩,a.work⟩

theorem internKey_lookup (R : Registry σ) (q : Nat) (w : KeyWord σ) (rho : Nat) :
    lookup (internKey R q w rho).registry.tree w=some (internKey R q w rho).key.wordRank :=
  assign_lookup R w

theorem internKey_cost (R : Registry σ) (q : Nat) (w : KeyWord σ) (rho : Nat) :
    (internKey R q w rho).work≤(3*σ+1)*w.length+1 := intern_cost w R.tree R.next

def rotations (s : Nat→Fin σ) (q : Nat) : List (KeyWord σ) :=
  (List.range q).map (fun a=>Periodic.segment s a q)

theorem rotations_length (s : Nat→Fin σ) (q : Nat) : (rotations s q).length=q := by
  simp [rotations]

theorem rotations_mem (s : Nat→Fin σ) (q a : Nat) (ha : a<q) :
    Periodic.segment s a q∈rotations s q :=
  List.mem_map.mpr ⟨a,List.mem_range.mpr ha,rfl⟩

theorem characters_append (xs ys : List (KeyWord σ)) :
    characters (xs++ys)=characters xs+characters ys := by
  induction xs with
  | nil => simp [characters]
  | cons x xs ih =>
    change x.length+characters (xs++ys)=(x.length+characters xs)+characters ys
    rw [ih,Nat.add_assoc]

theorem characters_map {X : Type} (f : X→KeyWord σ) (xs : List X) (n : Nat)
    (h : ∀ x,x∈xs→(f x).length=n) : characters (xs.map f)=xs.length*n := by
  induction xs with
  | nil => simp [characters]
  | cons x xs ih =>
    change (f x).length+characters (xs.map f)=(xs.length+1)*n
    rw [h x (by simp),ih (fun y hy=>h y (by simp [hy])),Nat.add_mul,Nat.one_mul,Nat.add_comm]

theorem rotations_characters (s : Nat→Fin σ) (q : Nat) :
    characters (rotations s q)=q^2 := by
  unfold rotations
  rw [characters_map _ _ q (fun a _=>Periodic.segment_length s a q),List.length_range]
  simp [Nat.pow_succ]

def runWords (f : Nat→Fin σ) : List RunGeometry.Bounds→List (KeyWord σ)
  | [] => []
  | R::Rs => rotations (Periodic.shift f R.lo) R.period++runWords f Rs

theorem runWords_length (f : Nat→Fin σ) (Rs : List RunGeometry.Bounds) :
    (runWords f Rs).length=RunBudget.phaseWork 0 Rs := by
  induction Rs with
  | nil => rfl
  | cons R Rs ih =>
    simp only [runWords,List.length_append,rotations_length,ih,RunBudget.phaseWork,
      Nat.zero_add,Nat.pow_one]

theorem runWords_characters (f : Nat→Fin σ) (Rs : List RunGeometry.Bounds) :
    characters (runWords f Rs)=RunBudget.phaseWork 1 Rs := by
  induction Rs with
  | nil => rfl
  | cons R Rs ih =>
    rw [runWords,characters_append,rotations_characters,ih]
    rfl

/-- Build the actual common registry for every phase of every supplied
    run. The dictionary workload is controlled by sum(period^2), rather
    than by comparisons between all pairs of source and target runs. -/
def internRuns (R : Registry σ) (f : Nat→Fin σ) (Rs : List RunGeometry.Bounds) : Batch σ :=
  internMany R (runWords f Rs)

theorem internRuns_cost (R : Registry σ) (f : Nat→Fin σ) (Rs : List RunGeometry.Bounds) :
    (internRuns R f Rs).work≤
      (3*σ+1)*RunBudget.phaseWork 1 Rs+RunBudget.phaseWork 0 Rs := by
  have h := internMany_cost R (runWords f Rs)
  rwa [runWords_characters,runWords_length] at h

theorem internRuns_cubic_cost (R : Registry σ) (f : Nat→Fin σ) (n Q : Nat)
    (Rs : List RunGeometry.Bounds) (hd : Rs.Nodup)
    (hv : ∀ r,r∈Rs→r.Valid f n)
    (hc : ∀ r,r∈Rs→r.period≤Q ∧ 3*r.period≤r.hi-r.lo) :
    (internRuns R f Rs).work≤
      ((3*σ+1)*Q+1)*(2*n*DyadicIndex.heightFor n) := by
  have h1 := RunBudget.cubic_phase_bound f n 1 Q Rs hd hv hc
  have h0 := RunBudget.cubic_phase_bound f n 0 Q Rs hd hv hc
  simp only [Nat.pow_one] at h1
  simp only [Nat.pow_zero,Nat.one_mul] at h0
  calc
    _ ≤ (3*σ+1)*RunBudget.phaseWork 1 Rs+RunBudget.phaseWork 0 Rs := internRuns_cost R f Rs
    _ ≤ (3*σ+1)*(Q*(2*n*DyadicIndex.heightFor n))+(2*n*DyadicIndex.heightFor n) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ h1) h0
    _ = _ := by simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]

def phaseWord (f : Nat→Fin σ) (R : RunGeometry.Bounds) (i : Nat) : KeyWord σ :=
  Periodic.segment (Periodic.shift f R.lo) ((i-R.lo)%R.period) R.period

theorem phaseWord_mem (f : Nat→Fin σ) (n : Nat) (R : RunGeometry.Bounds)
    (h : R.Valid f n) (i : Nat) :
    phaseWord f R i∈rotations (Periodic.shift f R.lo) R.period :=
  rotations_mem _ _ _ (Nat.mod_lt _ h.2.2.2.1.1)

theorem runWords_mem (f : Nat→Fin σ) (Rs : List RunGeometry.Bounds)
    (R : RunGeometry.Bounds) (hR : R∈Rs) (w : KeyWord σ)
    (hw : w∈rotations (Periodic.shift f R.lo) R.period) : w∈runWords f Rs := by
  induction Rs with
  | nil => simp at hR
  | cons S Ss ih =>
    rw [runWords,List.mem_append]
    rcases List.mem_cons.mp hR with h|h
    · subst S
      exact Or.inl hw
    · exact Or.inr (ih h)

theorem internMany_covered (R : Registry σ) (ws : List (KeyWord σ))
    (w : KeyWord σ) (hw : w∈ws) :
    ∃ r,lookup (internMany R ws).registry.tree w=some r := by
  rw [← internMany_words R ws] at hw
  obtain ⟨e,he,hew⟩ := List.mem_map.mp hw
  refine ⟨e.2,?_⟩
  rw [← hew]
  exact internMany_entries R ws e he

theorem internRuns_covers (registry : Registry σ) (f : Nat→Fin σ) (n : Nat)
    (Rs : List RunGeometry.Bounds) (R : RunGeometry.Bounds) (hR : R∈Rs)
    (hv : R.Valid f n) (i : Nat) :
    ∃ r,lookup (internRuns registry f Rs).registry.tree (phaseWord f R i)=some r :=
  internMany_covered registry (runWords f Rs) _
    (runWords_mem f Rs R hR _ (phaseWord_mem f n R hv i))

/-- The geometric long-source theorem now yields equality of identifiers
    in the actual shared registry, with no suffix-rank or hashing oracle. -/
theorem intern_long_source (registry : Registry σ) (f : Nat→Fin σ)
    (n i j L : Nat) (T : RunGeometry.Bounds)
    (ht : T.Valid f n) (hj : T.lo≤j) (hjt : j+L≤T.hi)
    (hL : 2*T.period≤L) (hi : i+L≤n)
    (he : Periodic.segment f i L=Periodic.segment f j L)
    (targetRank : Nat) (hkey : lookup registry.tree (phaseWord f T j)=some targetRank) :
    ∃ S : RunGeometry.Bounds,S.Valid f n ∧ S.period=T.period ∧ S.lo≤i ∧ i+L≤S.hi ∧
      (assign registry (phaseWord f S i)).rank=targetRank ∧
      (assign registry (phaseWord f S i)).registry.next=registry.next := by
  obtain ⟨S,hS,hp,hlo,hhi,heq⟩ := LongSourceCoverage.long_source f n i j L T ht hj hjt hL hi he
  have hw : phaseWord f S i=phaseWord f T j := by
    unfold phaseWord
    rw [hp]
    exact heq
  refine ⟨S,hS,hp,hlo,hhi,?_⟩
  rw [hw]
  exact intern_existing _ registry.tree registry.next targetRank hkey

structure PhaseRanks (σ : Nat) where
  registry : Registry σ
  ranks : Array Nat
  work : Nat

/-- Keep identifiers in phase order, so later joins read one array cell
    instead of traversing a q-character key again. -/
def internRotations (R : Registry σ) (s : Nat→Fin σ) (q : Nat) : PhaseRanks σ :=
  let b := internMany R (rotations s q)
  ⟨b.registry,(b.entries.map Prod.snd).toArray,b.work⟩

theorem internRotations_size (R : Registry σ) (s : Nat→Fin σ) (q : Nat) :
    (internRotations R s q).ranks.size=q := by
  have h := congrArg List.length (internMany_words R (rotations s q))
  simp only [List.length_map,rotations_length] at h
  simpa only [internRotations,List.size_toArray,List.length_map] using h

theorem internRotations_get (R : Registry σ) (s : Nat→Fin σ) (q a : Nat) (ha : a<q) :
    ∃ r,(internRotations R s q).ranks[a]?=some r ∧
      lookup (internRotations R s q).registry.tree (Periodic.segment s a q)=some r := by
  have hw := congrArg (fun ws : List (KeyWord σ)=>ws[a]?) (internMany_words R (rotations s q))
  simp only [List.getElem?_map,rotations,List.getElem?_map,List.getElem?_range,ha,
    if_true,Option.map] at hw
  change ((internMany R (rotations s q)).entries[a]?).map Prod.fst=
    some (Periodic.segment s a q) at hw
  cases he : (internMany R (rotations s q)).entries[a]? with
  | none => simp [he] at hw
  | some e =>
    have hew : e.1=Periodic.segment s a q := by simpa only [he,Option.map,Option.some.injEq] using hw
    refine ⟨e.2,?_,?_⟩
    · simp only [internRotations,List.getElem?_toArray,List.getElem?_map,he,Option.map]
    · change lookup (internMany R (rotations s q)).registry.tree (Periodic.segment s a q)=some e.2
      rw [← hew]
      exact internMany_entries R _ e (List.mem_of_getElem? he)

theorem internRotations_cost (R : Registry σ) (s : Nat→Fin σ) (q : Nat) :
    (internRotations R s q).work≤(3*σ+1)*q^2+q := by
  have h := internMany_cost R (rotations s q)
  rwa [rotations_characters,rotations_length] at h

structure RunTables (σ : Nat) where
  registry : Registry σ
  tables : List (RunGeometry.Bounds×Array Nat)
  work : Nat

def buildRunTables (R : Registry σ) (f : Nat→Fin σ) : List RunGeometry.Bounds→RunTables σ
  | [] => ⟨R,[],0⟩
  | run::runs =>
    let a := internRotations R (Periodic.shift f run.lo) run.period
    let b := buildRunTables a.registry f runs
    ⟨b.registry,(run,a.ranks)::b.tables,a.work+b.work⟩

theorem buildRunTables_preserves (R : Registry σ) (f : Nat→Fin σ) (runs : List RunGeometry.Bounds)
    (v : KeyWord σ) (r : Nat) (hr : lookup R.tree v=some r) :
    lookup (buildRunTables R f runs).registry.tree v=some r := by
  induction runs generalizing R with
  | nil => exact hr
  | cons run runs ih =>
    exact ih _ (internMany_preserves R _ v r hr)

theorem buildRunTables_valid (R : Registry σ) (hR : R.Valid) (f : Nat→Fin σ)
    (runs : List RunGeometry.Bounds) : (buildRunTables R f runs).registry.Valid := by
  induction runs generalizing R with
  | nil => exact hR
  | cons run runs ih => exact ih _ (internMany_valid R hR _)

theorem buildRunTables_runs (R : Registry σ) (f : Nat→Fin σ) (runs : List RunGeometry.Bounds) :
    (buildRunTables R f runs).tables.map Prod.fst=runs := by
  induction runs generalizing R with
  | nil => rfl
  | cons run runs ih =>
    change run::(buildRunTables _ f runs).tables.map Prod.fst=run::runs
    rw [ih]

theorem buildRunTables_exact (R : Registry σ) (f : Nat→Fin σ) (runs : List RunGeometry.Bounds) :
    ∀ e,e∈(buildRunTables R f runs).tables→∀ a,a<e.1.period→
      ∃ r,e.2[a]?=some r ∧ lookup (buildRunTables R f runs).registry.tree
        (Periodic.segment (Periodic.shift f e.1.lo) a e.1.period)=some r := by
  induction runs generalizing R with
  | nil => intro e he; simp [buildRunTables] at he
  | cons run runs ih =>
    intro e he a ha
    change e∈(run,(internRotations R (Periodic.shift f run.lo) run.period).ranks)::
      (buildRunTables _ f runs).tables at he
    rcases List.mem_cons.mp he with he|he
    · subst e
      obtain ⟨r,hget,hlookup⟩ := internRotations_get R (Periodic.shift f run.lo) run.period a ha
      exact ⟨r,hget,buildRunTables_preserves _ f runs _ r hlookup⟩
    · exact ih _ e he a ha

theorem buildRunTables_cost (R : Registry σ) (f : Nat→Fin σ) (runs : List RunGeometry.Bounds) :
    (buildRunTables R f runs).work≤
      (3*σ+1)*RunBudget.phaseWork 1 runs+RunBudget.phaseWork 0 runs := by
  induction runs generalizing R with
  | nil => simp [buildRunTables,RunBudget.phaseWork]
  | cons run runs ih =>
    have ha := internRotations_cost R (Periodic.shift f run.lo) run.period
    have hb := ih (internRotations R (Periodic.shift f run.lo) run.period).registry
    change (internRotations R (Periodic.shift f run.lo) run.period).work+
      (buildRunTables _ f runs).work≤_
    simp only [RunBudget.phaseWork,Nat.zero_add,Nat.pow_one,Nat.mul_add,show (1:Nat)+1=2 from rfl]
    omega

theorem buildRunTables_next (R : Registry σ) (f : Nat→Fin σ) (runs : List RunGeometry.Bounds) :
    (buildRunTables R f runs).registry.next≤R.next+RunBudget.phaseWork 0 runs := by
  induction runs generalizing R with
  | nil => simp [buildRunTables,RunBudget.phaseWork]
  | cons run runs ih =>
    have ha := internMany_next R (rotations (Periodic.shift f run.lo) run.period)
    rw [rotations_length] at ha
    have hb := ih (internRotations R (Periodic.shift f run.lo) run.period).registry
    change (internRotations R (Periodic.shift f run.lo) run.period).registry.next≤R.next+run.period at ha
    change (buildRunTables (internRotations R (Periodic.shift f run.lo) run.period).registry f runs).registry.next≤_
    simp only [RunBudget.phaseWork,Nat.zero_add,Nat.pow_one]
    omega

theorem buildRunTables_cubic_cost (R : Registry σ) (f : Nat→Fin σ) (n Q : Nat)
    (runs : List RunGeometry.Bounds) (hd : runs.Nodup)
    (hv : ∀ r,r∈runs→r.Valid f n)
    (hc : ∀ r,r∈runs→r.period≤Q ∧ 3*r.period≤r.hi-r.lo) :
    (buildRunTables R f runs).work≤
      ((3*σ+1)*Q+1)*(2*n*DyadicIndex.heightFor n) := by
  have h1 := RunBudget.cubic_phase_bound f n 1 Q runs hd hv hc
  have h0 := RunBudget.cubic_phase_bound f n 0 Q runs hd hv hc
  simp only [Nat.pow_one] at h1
  simp only [Nat.pow_zero,Nat.one_mul] at h0
  calc
    _ ≤ (3*σ+1)*RunBudget.phaseWork 1 runs+RunBudget.phaseWork 0 runs := buildRunTables_cost R f runs
    _ ≤ (3*σ+1)*(Q*(2*n*DyadicIndex.heightFor n))+(2*n*DyadicIndex.heightFor n) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ h1) h0
    _ = _ := by simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]

def tableKey (run : RunGeometry.Bounds) (ranks : Array Nat) (phase rho : Nat) : Option Key :=
  ranks[phase]?.map (fun rank=>⟨run.period,rank,rho⟩)

/-- Collision-free mixed radix encoding for KeyedJoin's natural-number
    key. The rank radix comes from the final common registry. -/
def keyCode (Q next : Nat) (k : Key) : Nat :=
  (k.period*(next+1)+k.wordRank)*(Q+1)+k.residue

def Key.Bounded (Q next : Nat) (k : Key) : Prop :=
  k.period≤Q ∧ k.wordRank<next+1 ∧ k.residue≤Q

theorem keyCode_eq_iff (Q next : Nat) (a b : Key)
    (ha : a.Bounded Q next) (hb : b.Bounded Q next) :
    keyCode Q next a=keyCode Q next b ↔ a=b := by
  constructor
  · intro he
    have hlast := (PhaseSolver.length_unique (Q+1)
      (a.period*(next+1)+a.wordRank) (b.period*(next+1)+b.wordRank)
      a.residue b.residue (by have h := ha.2.2; omega) (by have h := hb.2.2; omega)).mp he
    have hfirst := (PhaseSolver.length_unique (next+1) a.period b.period a.wordRank b.wordRank
      ha.2.1 hb.2.1).mp hlast.1
    cases a
    cases b
    simp_all
  · intro he
    rw [he]

/-- The integer key has polynomial magnitude in the maximum period and
    the number of interned words; it does not contain a base-σ word code. -/
theorem keyCode_bound (Q next : Nat) (k : Key) (hk : k.Bounded Q next) :
    keyCode Q next k<(Q+1)^2*(next+1) := by
  have hinner : k.period*(next+1)+k.wordRank<(Q+1)*(next+1) := by
    have h1 : k.period*(next+1)+k.wordRank<(k.period+1)*(next+1) := by
      rw [Nat.add_mul,Nat.one_mul]
      exact Nat.add_lt_add_left hk.2.1 _
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ (by have h := hk.1; omega))
  have hstep : keyCode Q next k<
      (k.period*(next+1)+k.wordRank+1)*(Q+1) := by
    unfold keyCode
    rw [Nat.add_mul (k.period*(next+1)+k.wordRank) 1 (Q+1),Nat.one_mul]
    exact Nat.add_lt_add_left (by have h := hk.2.2; omega) _
  have hfinal := Nat.mul_le_mul_right (Q+1) (show k.period*(next+1)+k.wordRank+1≤
    (Q+1)*(next+1) by omega)
  have he : ((Q+1)*(next+1))*(Q+1)=(Q+1)^2*(next+1) := by
    simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
    ac_rfl
  rw [he] at hfinal
  exact Nat.lt_of_lt_of_le hstep hfinal

theorem keyCode_exact (R : Registry σ) (hR : R.Valid) (Q : Nat)
    (u v : KeyWord σ) (a b : Key)
    (ha : a.Bounded Q R.next) (hb : b.Bounded Q R.next)
    (hu : lookup R.tree u=some a.wordRank) (hv : lookup R.tree v=some b.wordRank) :
    keyCode Q R.next a=keyCode Q R.next b ↔
      a.period=b.period ∧ a.residue=b.residue ∧ u=v := by
  rw [keyCode_eq_iff Q R.next a b ha hb]
  exact key_eq_iff R hR u v a.period b.period a.wordRank b.wordRank a.residue b.residue hu hv

theorem buildRunTables_key (R : Registry σ) (hR : R.Valid) (f : Nat→Fin σ)
    (runs : List RunGeometry.Bounds) (Q : Nat) (e : RunGeometry.Bounds×Array Nat)
    (he : e∈(buildRunTables R f runs).tables) (hq : e.1.period≤Q)
    (phase rho : Nat) (hphase : phase<e.1.period) (hrho : rho<e.1.period) :
    ∃ k,tableKey e.1 e.2 phase rho=some k ∧
      k.Bounded Q (buildRunTables R f runs).registry.next ∧
      lookup (buildRunTables R f runs).registry.tree
        (Periodic.segment (Periodic.shift f e.1.lo) phase e.1.period)=some k.wordRank ∧
      k.period=e.1.period ∧ k.residue=rho := by
  obtain ⟨r,hget,hlookup⟩ := buildRunTables_exact R f runs e he phase hphase
  have hb := (buildRunTables_valid R hR f runs).1 _ r hlookup
  refine ⟨⟨e.1.period,r,rho⟩,?_,?_,hlookup,rfl,rfl⟩
  · simp only [tableKey,hget,Option.map]
  · change e.1.period≤Q ∧ r<(buildRunTables R f runs).registry.next+1 ∧ rho≤Q
    exact ⟨hq,by omega,by omega⟩

end REWB.ExactKeys
