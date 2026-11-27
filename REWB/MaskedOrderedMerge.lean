import REWB.MaskedOrderedEvents

/-! Persistent light-side imports. Positions are maintained when a key is
first inserted; the cached tree count drives heavy selection. Event logs
are reverse accumulators threaded through the execution. Each update
prepends at most two fresh and two retired records, so neither heavy
positions nor previous logs are copied or scanned. -/
namespace REWB.MaskedOrdered
open REWB.MaskedEventBudget (Edge)
variable {h : Nat}

structure State (h : Nat) where
  tree : Tree h
  positions : List Nat
  deriving Repr

def State.Valid (s : State h) : Prop :=
  s.tree.Good ∧ s.tree.Fits 0 ∧ s.positions.Perm s.tree.entries

def State.empty (h : Nat) : State h := ⟨.empty,[]⟩

theorem State.empty_valid (h : Nat) : (empty h).Valid := by
  refine ⟨True.intro,?_,List.Perm.refl _⟩
  cases h <;> trivial

theorem State.count_eq (s : State h) (hs : s.Valid) : s.tree.count=s.positions.length :=
  (Tree.count_correct s.tree hs.1).trans hs.2.2.length_eq.symm

theorem State.bounded (s : State h) (hs : s.Valid) (p : Nat) (hp : p∈s.positions) : p<2^h := by
  have hh:=Tree.within s.tree 0 hs.2.1 p (hs.2.2.mem_iff.mp hp)
  omega

def add (s : State h) (capacity p : Nat) : State h×Insertion h :=
  let r:=insert s.tree capacity p
  (⟨r.tree,if r.inserted then p::s.positions else s.positions⟩,r)

theorem add_valid (s : State h) (capacity p : Nat) (hs : s.Valid)
    (hb : capacity=2^h) (hp : p<2^h) : (add s capacity p).1.Valid := by
  refine ⟨insert_good s.tree capacity p hs.1,insert_fits s.tree capacity p hs.2.1 hb hp,?_⟩
  by_cases hmem : p∈s.tree.entries
  · have he:=insert_existing s.tree capacity p hs.2.1 hb hmem
    change (if (insert s.tree capacity p).inserted then p::s.positions else s.positions).Perm
      (insert s.tree capacity p).tree.entries
    rw [he.1,he.2.2.2]
    exact hs.2.2
  · have he:=insert_reference s.tree capacity p hs.1 hs.2.1 hb hp hmem
    change (if (insert s.tree capacity p).inserted then p::s.positions else s.positions).Perm
      (insert s.tree capacity p).tree.entries
    rw [he.1,he.2.2.2]
    exact (hs.2.2.cons p).trans (MaskedEventBudget.insert_perm p s.tree.entries).symm

theorem add_mem (s : State h) (capacity p x : Nat) (hs : s.Valid)
    (hb : capacity=2^h) (hp : p<2^h) :
    x∈(add s capacity p).1.tree.entries ↔ x=p ∨ x∈s.tree.entries :=
  insert_mem s.tree capacity p x hs.2.1 hb hp

theorem add_new_positions (s : State h) (capacity p : Nat) (hs : s.Valid)
    (hb : capacity=2^h) (hnew : p∉s.tree.entries) :
    (add s capacity p).1.positions=p::s.positions := by
  have he:=(insert_new s.tree capacity p hs.2.1 hb hnew).2.2.2
  change (if (insert s.tree capacity p).inserted then p::s.positions else s.positions)=_
  rw [he]
  rfl

structure Ledger where
  fresh : List Edge := []
  retired : List Edge := []
  freshCount : Nat := 0
  retiredCount : Nat := 0
  imports : Nat := 0
  work : Nat := 0
  deriving Repr

def Ledger.Good (a : Ledger) : Prop := a.freshCount=a.fresh.length ∧ a.retiredCount=a.retired.length

theorem Ledger.empty_good : ({} : Ledger).Good := ⟨rfl,rfl⟩

def discarded (p : Nat) (predecessor : Option Nat) : List Edge :=
  match predecessor with
  | none => []
  | some q => [(q,p)]

theorem discarded_length (p : Nat) (a : Option Nat) : (discarded p a).length≤1 := by
  cases a <;> simp [discarded]

/-- The original light tree remains immutable while its positions are
imported. Its predecessor query retires each old light adjacency at its
right endpoint. Destination repair retires at most one additional edge. -/
def importOne (light : Tree h) (capacity p : Nat) (dst : State h) (ledger : Ledger) : State h×Ledger :=
  let old:=Tree.pred light capacity p
  let discardedOld:=discarded p old.1
  let step:=add dst capacity p
  let fresh:=step.2.fresh
  let retired:=step.2.retired
  (step.1,⟨fresh++ledger.fresh,discardedOld++retired++ledger.retired,
    ledger.freshCount+fresh.length,ledger.retiredCount+discardedOld.length+retired.length,
    ledger.imports+1,ledger.work+step.2.work+old.2+15+fresh.length+retired.length+discardedOld.length⟩)

def importBudget (h : Nat) : Nat := 35*h+40

theorem importOne_valid (light : Tree h) (capacity p : Nat) (dst : State h) (ledger : Ledger)
    (hd : dst.Valid) (hb : capacity=2^h) (hp : p<2^h) :
    (importOne light capacity p dst ledger).1.Valid := add_valid dst capacity p hd hb hp

theorem importOne_ledger (light : Tree h) (capacity p : Nat) (dst : State h) (ledger : Ledger)
    (hl : ledger.Good) : (importOne light capacity p dst ledger).2.Good := by
  have h1:=hl.1
  have h2:=hl.2
  simp only [importOne,Ledger.Good,List.length_append]
  constructor <;> omega

theorem importOne_work (light : Tree h) (capacity p : Nat) (dst : State h) (ledger : Ledger) :
    (importOne light capacity p dst ledger).2.work≤ledger.work+importBudget h := by
  have hi:=insert_work dst.tree capacity p
  have hp:=Tree.pred_work light capacity p
  have hf:=insert_fresh_bound dst.tree capacity p
  have hr:=insert_retired_bound dst.tree capacity p
  have hd:=discarded_length p (Tree.pred light capacity p).1
  simp only [importOne,add,importBudget]
  omega

theorem importOne_fresh (light : Tree h) (capacity p : Nat) (dst : State h) (ledger : Ledger) :
    (importOne light capacity p dst ledger).2.freshCount≤ledger.freshCount+2 := by
  have hf:=insert_fresh_bound dst.tree capacity p
  change ledger.freshCount+(insert dst.tree capacity p).fresh.length≤_
  omega

theorem importOne_retired (light : Tree h) (capacity p : Nat) (dst : State h) (ledger : Ledger) :
    (importOne light capacity p dst ledger).2.retiredCount≤ledger.retiredCount+2 := by
  have hr:=insert_retired_bound dst.tree capacity p
  have hd:=discarded_length p (Tree.pred light capacity p).1
  change ledger.retiredCount+(discarded p (Tree.pred light capacity p).1).length+
    (insert dst.tree capacity p).retired.length≤_
  omega

def importLoop (light : Tree h) (capacity : Nat) : List Nat→State h→Ledger→State h×Ledger
  | [],dst,ledger => (dst,{ ledger with work:=ledger.work+1 })
  | p::ps,dst,ledger =>
    let step:=importOne light capacity p dst ledger
    importLoop light capacity ps step.1 step.2

theorem importLoop_valid (light : Tree h) (capacity : Nat) (ps : List Nat) (dst : State h)
    (ledger : Ledger) (hd : dst.Valid) (hb : capacity=2^h) (hp : ∀p,p∈ps→p<2^h) :
    (importLoop light capacity ps dst ledger).1.Valid := by
  induction ps generalizing dst ledger with
  | nil => exact hd
  | cons p ps ih =>
    exact ih _ _ (importOne_valid light capacity p dst ledger hd hb (hp p (by simp)))
      (fun p hp'=>hp p (List.mem_cons_of_mem _ hp'))

theorem importLoop_ledger (light : Tree h) (capacity : Nat) (ps : List Nat) (dst : State h)
    (ledger : Ledger) (hl : ledger.Good) : (importLoop light capacity ps dst ledger).2.Good := by
  induction ps generalizing dst ledger with
  | nil => exact hl
  | cons p ps ih => exact ih _ _ (importOne_ledger light capacity p dst ledger hl)

theorem importLoop_imports (light : Tree h) (capacity : Nat) (ps : List Nat) (dst : State h)
    (ledger : Ledger) : (importLoop light capacity ps dst ledger).2.imports=ledger.imports+ps.length := by
  induction ps generalizing dst ledger with
  | nil => simp [importLoop]
  | cons p ps ih =>
    rw [importLoop,ih]
    change ledger.imports+1+ps.length=ledger.imports+(p::ps).length
    simp only [List.length_cons]
    omega

theorem importLoop_work (light : Tree h) (capacity : Nat) (ps : List Nat) (dst : State h)
    (ledger : Ledger) :
    (importLoop light capacity ps dst ledger).2.work≤ledger.work+ps.length*importBudget h+1 := by
  induction ps generalizing dst ledger with
  | nil => simp [importLoop]
  | cons p ps ih =>
    have hs:=importOne_work light capacity p dst ledger
    have hr:=ih (importOne light capacity p dst ledger).1 (importOne light capacity p dst ledger).2
    simp only [importLoop,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem importLoop_fresh (light : Tree h) (capacity : Nat) (ps : List Nat) (dst : State h)
    (ledger : Ledger) :
    (importLoop light capacity ps dst ledger).2.freshCount≤ledger.freshCount+2*ps.length := by
  induction ps generalizing dst ledger with
  | nil => simp [importLoop]
  | cons p ps ih =>
    have hs:=importOne_fresh light capacity p dst ledger
    have hr:=ih (importOne light capacity p dst ledger).1 (importOne light capacity p dst ledger).2
    simp only [importLoop,List.length_cons]
    omega

theorem importLoop_retired (light : Tree h) (capacity : Nat) (ps : List Nat) (dst : State h)
    (ledger : Ledger) :
    (importLoop light capacity ps dst ledger).2.retiredCount≤ledger.retiredCount+2*ps.length := by
  induction ps generalizing dst ledger with
  | nil => simp [importLoop]
  | cons p ps ih =>
    have hs:=importOne_retired light capacity p dst ledger
    have hr:=ih (importOne light capacity p dst ledger).1 (importOne light capacity p dst ledger).2
    simp only [importLoop,List.length_cons]
    omega

theorem importLoop_mem (light : Tree h) (capacity : Nat) (ps : List Nat) (dst : State h)
    (ledger : Ledger) (hd : dst.Valid) (hb : capacity=2^h) (hp : ∀p,p∈ps→p<2^h) (x : Nat) :
    x∈(importLoop light capacity ps dst ledger).1.tree.entries ↔ x∈ps ∨ x∈dst.tree.entries := by
  induction ps generalizing dst ledger with
  | nil => simp [importLoop]
  | cons p ps ih =>
    have hbound:=hp p (by simp)
    rw [importLoop,ih _ _ (importOne_valid light capacity p dst ledger hd hb hbound)
      (fun p hp'=>hp p (List.mem_cons_of_mem _ hp'))]
    change x∈ps ∨ x∈(add dst capacity p).1.tree.entries ↔ x∈p::ps ∨ x∈dst.tree.entries
    rw [add_mem dst capacity p x hd hb hbound,List.mem_cons]
    constructor
    · rintro (hx|he|hx)
      · exact Or.inl (Or.inr hx)
      · exact Or.inl (Or.inl he)
      · exact Or.inr hx
    · rintro ((he|hx)|hx)
      · exact Or.inr (Or.inl he)
      · exact Or.inl hx
      · exact Or.inr (Or.inr hx)

/-- The branch reads cached cardinalities. Only the selected light
position list is passed to the tail-recursive import loop. -/
def merge (capacity : Nat) (a b : State h) (ledger : Ledger) : State h×Ledger :=
  let ledger':={ ledger with work:=ledger.work+1 }
  if a.tree.count≤b.tree.count then importLoop a.tree capacity a.positions b ledger'
  else importLoop b.tree capacity b.positions a ledger'

theorem merge_valid (capacity : Nat) (a b : State h) (ledger : Ledger)
    (ha : a.Valid) (hb : b.Valid) (hc : capacity=2^h) : (merge capacity a b ledger).1.Valid := by
  simp only [merge]
  split
  · exact importLoop_valid _ _ _ _ _ hb hc (State.bounded a ha)
  · exact importLoop_valid _ _ _ _ _ ha hc (State.bounded b hb)

theorem merge_mem (capacity : Nat) (a b : State h) (ledger : Ledger)
    (ha : a.Valid) (hb : b.Valid) (hc : capacity=2^h) (x : Nat) :
    x∈(merge capacity a b ledger).1.tree.entries ↔ x∈a.tree.entries ∨ x∈b.tree.entries := by
  simp only [merge]
  split
  · rw [importLoop_mem _ _ _ _ _ hb hc (State.bounded a ha),ha.2.2.mem_iff]
  · rw [importLoop_mem _ _ _ _ _ ha hc (State.bounded b hb),hb.2.2.mem_iff,or_comm]

theorem merge_imports (capacity : Nat) (a b : State h) (ledger : Ledger)
    (ha : a.Valid) (hb : b.Valid) :
    (merge capacity a b ledger).2.imports=ledger.imports+min a.tree.count b.tree.count := by
  simp only [merge]
  split
  next hab =>
    rw [importLoop_imports,← State.count_eq a ha,Nat.min_eq_left hab]
  next hab =>
    rw [importLoop_imports,← State.count_eq b hb,Nat.min_eq_right (by omega : b.tree.count≤a.tree.count)]

theorem merge_work (capacity : Nat) (a b : State h) (ledger : Ledger)
    (ha : a.Valid) (hb : b.Valid) :
    (merge capacity a b ledger).2.work≤
      ledger.work+min a.tree.count b.tree.count*importBudget h+2 := by
  simp only [merge]
  split
  next hab =>
    have hh:=importLoop_work a.tree capacity a.positions b { ledger with work:=ledger.work+1 }
    rw [← State.count_eq a ha] at hh
    rw [Nat.min_eq_left hab]
    dsimp only at hh
    omega
  next hab =>
    have hh:=importLoop_work b.tree capacity b.positions a { ledger with work:=ledger.work+1 }
    rw [← State.count_eq b hb] at hh
    rw [Nat.min_eq_right (by omega : b.tree.count≤a.tree.count)]
    dsimp only at hh
    omega

theorem merge_ledger (capacity : Nat) (a b : State h) (ledger : Ledger)
    (hl : ledger.Good) : (merge capacity a b ledger).2.Good := by
  simp only [merge]
  split <;> exact importLoop_ledger _ _ _ _ _ hl

theorem merge_fresh (capacity : Nat) (a b : State h) (ledger : Ledger)
    (ha : a.Valid) (hb : b.Valid) :
    (merge capacity a b ledger).2.freshCount≤
      ledger.freshCount+2*min a.tree.count b.tree.count := by
  simp only [merge]
  split
  next hab =>
    have hh:=importLoop_fresh a.tree capacity a.positions b { ledger with work:=ledger.work+1 }
    rw [← State.count_eq a ha] at hh
    rw [Nat.min_eq_left hab]
    exact hh
  next hab =>
    have hh:=importLoop_fresh b.tree capacity b.positions a { ledger with work:=ledger.work+1 }
    rw [← State.count_eq b hb] at hh
    rw [Nat.min_eq_right (by omega : b.tree.count≤a.tree.count)]
    exact hh

theorem merge_retired (capacity : Nat) (a b : State h) (ledger : Ledger)
    (ha : a.Valid) (hb : b.Valid) :
    (merge capacity a b ledger).2.retiredCount≤
      ledger.retiredCount+2*min a.tree.count b.tree.count := by
  simp only [merge]
  split
  next hab =>
    have hh:=importLoop_retired a.tree capacity a.positions b { ledger with work:=ledger.work+1 }
    rw [← State.count_eq a ha] at hh
    rw [Nat.min_eq_left hab]
    exact hh
  next hab =>
    have hh:=importLoop_retired b.tree capacity b.positions a { ledger with work:=ledger.work+1 }
    rw [← State.count_eq b hb] at hh
    rw [Nat.min_eq_right (by omega : b.tree.count≤a.tree.count)]
    exact hh

end REWB.MaskedOrdered
