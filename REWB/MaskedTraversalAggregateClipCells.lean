import REWB.MaskedTraversalAggregateCells

/-! Exact leaf contents after the actual temporary boundary clips.
The proof model selects the same stored entry and same compiler result;
it is not an executable traversal of the aggregate's slot list.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {h : Nat}

def clippedEntry (env : Clip.Env C E) (st : Mutable.Store.State C E) (first old lo hi : Nat) :
    Option (Mutable.Store.Entry C E) :=
  (st.slots[first]?.join).bind fun entry=>
    let cfg:=Clip.config entry.config old lo hi
    (Clip.compiled env st cfg).1.map fun bank=>⟨cfg,bank⟩

theorem clippedEntry_selected (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (first old lo hi : Nat) (entry : Mutable.Store.Entry C E)
    (he : clippedEntry env st first old lo hi=some entry) :
    ∃before,st.slots[first]?.join=some before ∧
      entry.config=Clip.config before.config old lo hi ∧
      (Clip.compiled env st entry.config).1=some entry.bank := by
  cases hs : st.slots[first]?.join with
  | none => simp only [clippedEntry,hs,Option.bind] at he; cases he
  | some before =>
    cases hb : (Clip.compiled env st (Clip.config before.config old lo hi)).1 with
    | none => simp only [clippedEntry,hs,Option.bind,hb,Option.map] at he; cases he
    | some bank =>
      simp only [clippedEntry,hs,Option.bind,hb,Option.map,Option.some.injEq] at he
      subst entry
      exact ⟨before,rfl,rfl,hb⟩

theorem atLeader_represents (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (first old lo hi : Nat) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (hr : Represents tree entries)
    (ok : (Clip.atLeader env st first old lo hi tree).ready=true) :
    Represents (Clip.atLeader env st first old lo hi tree).tree
      (entries.set first (clippedEntry env st first old lo hi)) := by
  obtain ⟨entry,bank,hs,hb,hcells⟩:=Clip.atLeader_cells env st first old lo hi tree ok
  simp only [Represents,hcells,hr,List.map_set,clippedEntry,hs,Option.bind,hb,Option.map,entryView]
  rw [hr]

def clipEntries (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (keys : List Nat) (old lo hi : Nat) (entries : List (Option (Mutable.Store.Entry C E))) :
    List (Option (Mutable.Store.Entry C E)) :=
  keys.foldl (fun es p=>es.set p (clippedEntry env st p old lo hi)) entries

theorem applyKeys_represents (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (keys : List Nat) (old lo hi : Nat) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (hr : Represents tree entries)
    (ok : (Clip.applyKeys env st keys old lo hi tree).ready=true) :
    Represents (Clip.applyKeys env st keys old lo hi tree).tree
      (clipEntries env st keys old lo hi entries) := by
  have go : ∀(ps : List Nat) (acc : Clip.Update C E h)
      (es : List (Option (Mutable.Store.Entry C E))),
      (acc.ready=true→Represents acc.tree es)→
      (ps.foldl (fun acc first=>let one:=Clip.atLeader env st first old lo hi acc.tree
        ; Clip.Update.mk one.tree (acc.ready && one.ready) (acc.work+one.work+1) (acc.calls+one.calls)) acc).ready=true→
      Represents (ps.foldl (fun acc first=>let one:=Clip.atLeader env st first old lo hi acc.tree
        ; Clip.Update.mk one.tree (acc.ready && one.ready) (acc.work+one.work+1) (acc.calls+one.calls)) acc).tree
        (clipEntries env st ps old lo hi es) := by
    intro ps
    induction ps with
    | nil => intro acc es hh hok; exact hh hok
    | cons p ps ih =>
      intro acc es hh hok
      apply ih (Clip.Update.mk (Clip.atLeader env st p old lo hi acc.tree).tree
        (acc.ready && (Clip.atLeader env st p old lo hi acc.tree).ready)
        (acc.work+(Clip.atLeader env st p old lo hi acc.tree).work+1)
        (acc.calls+(Clip.atLeader env st p old lo hi acc.tree).calls))
        (es.set p (clippedEntry env st p old lo hi)) ?_ hok
      intro hon
      obtain ⟨ha,hb⟩:=Bool.and_eq_true_iff.mp hon
      exact atLeader_represents env st p old lo hi acc.tree es (hh ha) hb
  exact go keys (Clip.Update.mk tree true 0 0) entries (fun _=>hr) ok

theorem window_represents (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (tree : BankTree C E h) (entries : List (Option (Mutable.Store.Entry C E)))
    (hr : Represents tree entries) (ok : (Clip.window env st partition capacity old lo hi tree).update.ready=true) :
    lo<hi ∧ Represents (Clip.window env st partition capacity old lo hi tree).update.tree
      (clipEntries env st (Clip.plan partition.leaders capacity lo hi).keys old lo hi entries) := by
  by_cases hh : lo<hi
  · refine ⟨hh,?_⟩
    simpa only [Clip.window,hh,if_true] using applyKeys_represents env st
      (Clip.plan partition.leaders capacity lo hi).keys old lo hi tree entries hr
      (by simpa only [Clip.window,hh,if_true] using ok)
  · simp only [Clip.window,hh,if_false] at ok
    cases ok

end REWB.MaskedTraversalAggregate.Cells
