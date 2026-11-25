import REWB.MaskedTraversalAggregateReplay

/-! Exact active-slot contents of a persistent aggregate. The list below
is a proof model of this frontier's leaves; the global store may also
contain banks owned by other live frontiers. Runtime operations continue
to read indexed slots and update only the supplied dirty positions.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {h : Nat}

def entryView (entry : Option (Mutable.Store.Entry C E)) :
    View (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount) :=
  match entry with
  | none=>View.one
  | some entry=>entry.bank.view

def Represents (tree : BankTree C E h) (entries : List (Option (Mutable.Store.Entry C E))) : Prop :=
  tree.leaves=entries.map entryView

theorem prepare_represents (C E : DFA α) (h : Nat) :
    Represents (prepare C E h).blank (List.replicate (2^h) none) := by
  simp only [Represents,prepare_cells,List.map_replicate,entryView]

theorem slot_view (st : Mutable.Store.State C E) (p : Nat) :
    entryView (st.slots[p]?.join)=(slot st p).view := by
  cases hs : st.slots[p]? with
  | none => simp only [slot,hs,Option.join,Option.bind,entryView,Table.view_one]
  | some value => cases value <;> simp only [slot,hs,Option.join,Option.bind,id_eq,entryView,Table.view_one]

theorem refresh_represents (st : Mutable.Store.State C E) (p : Nat) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (hr : Represents tree entries) :
    Represents (refresh st p tree).1 (entries.set p (st.slots[p]?.join)) := by
  simp only [Represents,refresh_cells,List.map_set,slot_view]
  rw [hr]

def refreshEntries (st : Mutable.Store.State C E) (positions : List Nat)
    (entries : List (Option (Mutable.Store.Entry C E))) : List (Option (Mutable.Store.Entry C E)) :=
  positions.foldl (fun entries p=>entries.set p (st.slots[p]?.join)) entries

theorem refreshMany_represents (st : Mutable.Store.State C E) (positions : List Nat)
    (tree : BankTree C E h) (entries : List (Option (Mutable.Store.Entry C E)))
    (hr : Represents tree entries) :
    Represents (refreshMany st positions tree).1 (refreshEntries st positions entries) := by
  have go : ∀(ps : List Nat) (acc : BankTree C E h×Nat)
      (es : List (Option (Mutable.Store.Entry C E))),Represents acc.1 es→
      Represents (ps.foldl (fun acc p=>let out:=refresh st p acc.1; (out.1,acc.2+out.2+1)) acc).1
        (refreshEntries st ps es) := by
    intro ps
    induction ps with
    | nil => intro acc es hh; exact hh
    | cons p ps ih =>
      intro acc es hh
      exact ih ((refresh st p acc.1).1,acc.2+(refresh st p acc.1).2+1)
        (es.set p (st.slots[p]?.join)) (refresh_represents st p acc.1 es hh)
  exact go positions (tree,0) entries hr

def parts (gate : Bool) (entries : List (Option (Mutable.Store.Entry C E))) : List Part :=
  entries.filterMap fun entry=>entry.map fun entry=>⟨entry.config,gate⟩

theorem denotes_entries (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool)
    (key : Fin (ReplayMaps.count C.stateCount E.stateCount)) (gate : Bool)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (cell : ∀entry,some entry∈entries→∀i j,
      entry.bank.view (code _ gate key) i j=true ↔
        partStep C E w L source removed target ⟨entry.config,gate⟩ i j) :
    Denotes C E w L source removed target key
      ((entries.map entryView).map (component gate)) (parts gate entries) := by
  induction entries with
  | nil => exact Denotes.nil
  | cons head tail ih =>
    have hh:=ih (fun entry he=>cell entry (List.mem_cons_of_mem head he))
    cases head with
    | none =>
      apply Denotes.skip ?_ hh
      intro i j
      simp only [component,entryView,View.one,FiniteRelation.ident,decide_eq_true_eq]
    | some entry =>
      apply Denotes.cons ?_ hh
      exact cell entry List.mem_cons_self

def regionParts (entries : List (Option (Mutable.Store.Entry C E))) (lo hi : Nat) : List Part :=
  parts false (entries.take lo)++parts true (Spec.slice entries lo hi)++parts false (entries.drop hi)

theorem denotes_region (C E : DFA α) (w : Word α) (L : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool)
    (key : Fin (ReplayMaps.count C.stateCount E.stateCount))
    (tree : BankTree C E h) (entries : List (Option (Mutable.Store.Entry C E)))
    (hr : Represents tree entries) (lo hi : Nat)
    (cell : ∀entry,some entry∈entries→∀gate i j,
      entry.bank.view (code _ gate key) i j=true ↔
        partStep C E w L source removed target ⟨entry.config,gate⟩ i j) :
    Denotes C E w L source removed target key (regionCells tree.leaves lo hi) (regionParts entries lo hi) := by
  rw [hr]
  simp only [regionCells,Spec.slice,List.map_take,List.map_drop,regionParts]
  apply denotes_append
  · apply denotes_append
    · simpa only [List.map_take,List.map_drop] using denotes_entries C E w L source removed target key false (entries.take lo)
        (fun entry he=>cell entry (List.mem_of_mem_take he) false)
    · simpa only [List.map_take,List.map_drop] using denotes_entries C E w L source removed target key true ((entries.drop lo).take (hi-lo))
        (fun entry he=>cell entry (List.mem_of_mem_drop (List.mem_of_mem_take he)) true)
  · simpa only [List.map_take,List.map_drop] using denotes_entries C E w L source removed target key false (entries.drop hi)
      (fun entry he=>cell entry (List.mem_of_mem_drop he) false)

end REWB.MaskedTraversalAggregate.Cells
