import REWB.MaskedOrderedMerge

/-! Actual bottom-up occurrence-set construction. The shared capacity
is computed once; each merge retains the larger cached-count child and
iterates only the smaller child's maintained positions. A single reverse
ledger is threaded through both children and their merge. -/
namespace REWB.MaskedOrdered
open REWB.MaskedEventBudget (MergeTree size leaves lightVolume)
variable {h : Nat}

def execute (capacity : Nat) : MergeTree→Ledger→State h×Ledger
  | .leaf p,ledger =>
    let step:=add (State.empty h) capacity p
    (step.1,{ ledger with work:=ledger.work+step.2.work+2 })
  | .node a b,ledger =>
    let x:=execute capacity a ledger
    let y:=execute capacity b x.2
    merge capacity x.1 y.1 y.2

def Bounded (h : Nat) (t : MergeTree) : Prop := ∀p,p∈leaves t→p<2^h

theorem bounded_left (a b : MergeTree) (hb : Bounded h (.node a b)) : Bounded h a :=
  fun p hp=>hb p (List.mem_append_left _ hp)

theorem bounded_right (a b : MergeTree) (hb : Bounded h (.node a b)) : Bounded h b :=
  fun p hp=>hb p (List.mem_append_right _ hp)

theorem execute_valid (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : capacity=2^h) (hb : Bounded h t) : (execute (h:=h) capacity t ledger).1.Valid := by
  induction t generalizing ledger with
  | leaf p => exact add_valid _ _ _ (State.empty_valid h) hc (hb p (by simp [leaves]))
  | node a b ia ib =>
    exact merge_valid _ _ _ _ (ia _ (bounded_left a b hb))
      (ib _ (bounded_right a b hb)) hc

theorem execute_ledger (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hl : ledger.Good) : (execute (h:=h) capacity t ledger).2.Good := by
  induction t generalizing ledger with
  | leaf p => exact hl
  | node a b ia ib => exact merge_ledger _ _ _ _ (ib _ (ia _ hl))

theorem execute_mem (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : capacity=2^h) (hb : Bounded h t) (x : Nat) :
    x∈(execute (h:=h) capacity t ledger).1.tree.entries ↔ x∈leaves t := by
  induction t generalizing ledger with
  | leaf p =>
    rw [execute,add_mem _ _ _ _ (State.empty_valid h) hc (hb p (by simp [leaves]))]
    simp [leaves,State.empty,Tree.entries]
  | node a b ia ib =>
    have ha:=bounded_left a b hb
    have hb':=bounded_right a b hb
    rw [execute,merge_mem _ _ _ _ (execute_valid _ _ _ hc ha)
      (execute_valid _ _ _ hc hb') hc,ia _ ha,ib _ hb']
    exact List.mem_append.symm

theorem nodup_count_le (xs : List Nat) (hn : xs.Nodup) (x : Nat) : xs.count x≤1 := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    have hh:=List.nodup_cons.mp hn
    by_cases he : p=x
    · subst p
      simp only [List.count_cons_self,List.count_eq_zero_of_not_mem hh.1]
      exact Nat.le_refl _
    · rw [List.count_cons_of_ne he]
      exact ih hh.2

theorem nodup_perm (xs ys : List Nat) (hx : xs.Nodup) (hy : ys.Nodup)
    (hm : ∀x,x∈xs↔x∈ys) : xs.Perm ys := by
  apply List.perm_iff_count.mpr
  intro x
  have hxc:=nodup_count_le xs hx x
  have hyc:=nodup_count_le ys hy x
  by_cases hh : x∈xs
  · have hxp:=List.count_pos_iff.mpr hh
    have hyp:=List.count_pos_iff.mpr ((hm x).mp hh)
    omega
  · rw [List.count_eq_zero_of_not_mem hh,
      List.count_eq_zero_of_not_mem (fun hy=>hh ((hm x).mpr hy))]

theorem leaves_length (t : MergeTree) : (leaves t).length=size t := by
  induction t <;> simp [leaves,size, *]

theorem execute_perm (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : capacity=2^h) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (execute (h:=h) capacity t ledger).1.tree.entries.Perm (leaves t) :=
  nodup_perm _ _ (Tree.nodup _ _ (execute_valid _ _ _ hc hb).2.1) hn
    (execute_mem _ _ _ hc hb)

theorem execute_count (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : capacity=2^h) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (execute (h:=h) capacity t ledger).1.tree.count=size t := by
  rw [Tree.count_correct _ (execute_valid _ _ _ hc hb).1,
    (execute_perm _ _ _ hc hb hn).length_eq,leaves_length]

theorem execute_positions (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : capacity=2^h) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (execute (h:=h) capacity t ledger).1.positions.Perm (leaves t) :=
  (execute_valid _ _ _ hc hb).2.2.trans (execute_perm _ _ _ hc hb hn)

theorem execute_reference (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : capacity=2^h) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (execute (h:=h) capacity t ledger).1.tree.entries=(MaskedEventBudget.build t).positions := by
  apply strict_ext _ _ (Tree.ordered _ _ (execute_valid _ _ _ hc hb).2.1)
    (MaskedEventBudget.build_strict t hn)
  intro x
  rw [execute_mem _ _ _ hc hb,(MaskedEventBudget.build_perm t).mem_iff]

theorem execute_imports (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : capacity=2^h) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (execute (h:=h) capacity t ledger).2.imports=ledger.imports+lightVolume t := by
  induction t generalizing ledger with
  | leaf p => simp [execute,lightVolume]
  | node a b ia ib =>
    have ha:=bounded_left a b hb
    have hb':=bounded_right a b hb
    have hna:=(List.sublist_append_left (leaves a) (leaves b)).nodup hn
    have hnb:=(List.sublist_append_right (leaves a) (leaves b)).nodup hn
    rw [execute,merge_imports _ _ _ _ (execute_valid _ _ _ hc ha)
      (execute_valid _ _ _ hc hb'),execute_count _ _ _ hc ha hna,
      execute_count _ _ _ hc hb' hnb,ib _ hb' hnb,ia _ ha hna]
    simp only [lightVolume]
    omega

def seedBudget (h : Nat) : Nat := 28*h+22

theorem execute_work (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : capacity=2^h) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (execute (h:=h) capacity t ledger).2.work+2≤
      ledger.work+size t*seedBudget h+lightVolume t*importBudget h := by
  induction t generalizing ledger with
  | leaf p =>
    have hh:=insert_work (State.empty h).tree capacity p
    simp only [execute,add,size,lightVolume,seedBudget,Nat.one_mul,Nat.zero_mul,Nat.add_zero]
    omega
  | node a b ia ib =>
    have ha:=bounded_left a b hb
    have hb':=bounded_right a b hb
    have hna:=(List.sublist_append_left (leaves a) (leaves b)).nodup hn
    have hnb:=(List.sublist_append_right (leaves a) (leaves b)).nodup hn
    have hwa:=ia ledger ha hna
    have hwb:=ib (execute (h:=h) capacity a ledger).2 hb' hnb
    have hwm:=merge_work capacity (execute (h:=h) capacity a ledger).1
      (execute (h:=h) capacity b (execute (h:=h) capacity a ledger).2).1
      (execute (h:=h) capacity b (execute (h:=h) capacity a ledger).2).2
      (execute_valid _ _ _ hc ha) (execute_valid _ _ _ hc hb')
    rw [execute_count _ _ _ hc ha hna,execute_count _ _ _ hc hb' hnb] at hwm
    simp only [execute,size,lightVolume,Nat.add_mul]
    omega

theorem execute_fresh (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : capacity=2^h) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (execute (h:=h) capacity t ledger).2.freshCount≤ledger.freshCount+2*lightVolume t := by
  induction t generalizing ledger with
  | leaf p => simp [execute,lightVolume]
  | node a b ia ib =>
    have ha:=bounded_left a b hb
    have hb':=bounded_right a b hb
    have hna:=(List.sublist_append_left (leaves a) (leaves b)).nodup hn
    have hnb:=(List.sublist_append_right (leaves a) (leaves b)).nodup hn
    have hwa:=ia ledger ha hna
    have hwb:=ib (execute (h:=h) capacity a ledger).2 hb' hnb
    have hwm:=merge_fresh capacity (execute (h:=h) capacity a ledger).1
      (execute (h:=h) capacity b (execute (h:=h) capacity a ledger).2).1
      (execute (h:=h) capacity b (execute (h:=h) capacity a ledger).2).2
      (execute_valid _ _ _ hc ha) (execute_valid _ _ _ hc hb')
    rw [execute_count _ _ _ hc ha hna,execute_count _ _ _ hc hb' hnb] at hwm
    simp only [execute,lightVolume]
    omega

theorem execute_retired (capacity : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : capacity=2^h) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (execute (h:=h) capacity t ledger).2.retiredCount≤ledger.retiredCount+2*lightVolume t := by
  induction t generalizing ledger with
  | leaf p => simp [execute,lightVolume]
  | node a b ia ib =>
    have ha:=bounded_left a b hb
    have hb':=bounded_right a b hb
    have hna:=(List.sublist_append_left (leaves a) (leaves b)).nodup hn
    have hnb:=(List.sublist_append_right (leaves a) (leaves b)).nodup hn
    have hwa:=ia ledger ha hna
    have hwb:=ib (execute (h:=h) capacity a ledger).2 hb' hnb
    have hwm:=merge_retired capacity (execute (h:=h) capacity a ledger).1
      (execute (h:=h) capacity b (execute (h:=h) capacity a ledger).2).1
      (execute (h:=h) capacity b (execute (h:=h) capacity a ledger).2).2
      (execute_valid _ _ _ hc ha) (execute_valid _ _ _ hc hb')
    rw [execute_count _ _ _ hc ha hna,execute_count _ _ _ hc hb' hnb] at hwm
    simp only [execute,lightVolume]
    omega

def capacity : Nat→Nat×Nat
  | 0 => (1,1)
  | h+1 => let r:=capacity h; (2*r.1,r.2+1)

theorem capacity_value (h : Nat) : (capacity h).1=2^h := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [capacity,ih,Nat.pow_succ,Nat.mul_comm]

theorem capacity_work (h : Nat) : (capacity h).2=h+1 := by
  induction h <;> simp [capacity, *]

def run (h : Nat) (t : MergeTree) : State h×Ledger :=
  let c:=capacity h
  execute c.1 t {work:=c.2}

theorem run_valid (h : Nat) (t : MergeTree) (hb : Bounded h t) : (run h t).1.Valid :=
  execute_valid _ _ _ (capacity_value h) hb

theorem run_mem (h : Nat) (t : MergeTree) (hb : Bounded h t) (x : Nat) :
    x∈(run h t).1.tree.entries ↔ x∈leaves t := execute_mem _ _ _ (capacity_value h) hb x

theorem run_ledger (h : Nat) (t : MergeTree) : (run h t).2.Good :=
  execute_ledger _ _ _ ⟨rfl,rfl⟩

theorem run_imports (h : Nat) (t : MergeTree) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (run h t).2.imports=lightVolume t := by
  have hh:=execute_imports (capacity h).1 t {work:=(capacity h).2} (capacity_value h) hb hn
  simpa only [Nat.zero_add] using hh

theorem run_work (h : Nat) (t : MergeTree) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (run h t).2.work≤h+1+size t*seedBudget h+
      size t*(size t).log2*importBudget h := by
  have hh:=execute_work (capacity h).1 t {work:=(capacity h).2} (capacity_value h) hb hn
  have hl:=Nat.mul_le_mul_right (importBudget h) (MaskedEventBudget.lightVolume_bound t)
  change (run h t).2.work+2≤_ at hh
  dsimp only at hh
  rw [capacity_work] at hh
  omega

theorem run_events (h : Nat) (t : MergeTree) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (run h t).2.fresh.length≤2*(size t*(size t).log2) ∧
      (run h t).2.retired.length≤2*(size t*(size t).log2) := by
  have hf:=execute_fresh (capacity h).1 t {work:=(capacity h).2} (capacity_value h) hb hn
  have hr:=execute_retired (capacity h).1 t {work:=(capacity h).2} (capacity_value h) hb hn
  have hg:=run_ledger h t
  have hgf:=hg.1
  have hgr:=hg.2
  have hv:=MaskedEventBudget.lightVolume_bound t
  change (run h t).2.freshCount≤0+2*lightVolume t at hf
  change (run h t).2.retiredCount≤0+2*lightVolume t at hr
  omega

theorem run_count (h : Nat) (t : MergeTree) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (run h t).1.tree.count=size t := execute_count _ _ _ (capacity_value h) hb hn

theorem run_work_bound (h : Nat) (t : MergeTree) (hb : Bounded h t) (hn : (leaves t).Nodup) :
    (run h t).2.work≤h+1+40*size t*((size t).log2+1)*(h+1) := by
  have hh:=run_work h t hb hn
  have hs:=Nat.mul_le_mul_left (size t) (show seedBudget h≤40*(h+1) by
    simp only [seedBudget,Nat.mul_add,Nat.mul_one]; omega)
  have hi:=Nat.mul_le_mul_left (size t*(size t).log2) (show importBudget h≤40*(h+1) by
    simp only [importBudget,Nat.mul_add,Nat.mul_one]; omega)
  have he : 40*size t*((size t).log2+1)*(h+1)=
      size t*(40*(h+1))+(size t*(size t).log2)*(40*(h+1)) := by
    simp [Nat.mul_add,Nat.add_mul,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc,Nat.add_comm]
  rw [he]
  omega

end REWB.MaskedOrdered
