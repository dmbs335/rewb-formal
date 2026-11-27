import REWB.MaskedTraversalAggregateEraseCost

/-! Full stored-bank equality under actual common-prefix shortening.
The proof model updates leaf configurations to the current length while
the production tree changes only its shared lazy tag. Historical store
metadata is deliberately separate and is normalized by refreshCurrent.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {h : Nat}

def reindexedEntry (z : ReplayMaps.Value C.stateCount E.stateCount) (fresh : Nat)
    (entry : Option (Mutable.Store.Entry C E)) : Option (Mutable.Store.Entry C E) :=
  entry.map fun entry=>⟨withLength entry.config fresh,(Counted.reindex (bankAction z) entry.bank).1⟩

theorem entryView_reindexed (z : ReplayMaps.Value C.stateCount E.stateCount) (fresh : Nat)
    (entry : Option (Mutable.Store.Entry C E)) :
    entryView (reindexedEntry z fresh entry)=View.reindex (bankAction z).get (entryView entry) := by
  cases entry with
  | none => rfl
  | some entry => exact Counted.reindex_view _ entry.bank

theorem shorten_represents (z : ReplayMaps.Value C.stateCount E.stateCount) (fresh : Nat)
    (tree : BankTree C E h) (entries : List (Option (Mutable.Store.Entry C E)))
    (hr : Represents tree entries) :
    Represents (shorten (bankAction z) tree).1 (entries.map (reindexedEntry z fresh)) := by
  simp only [Represents,shorten_cells,List.map_map,Function.comp_def,entryView_reindexed]
  rw [hr]
  simp only [List.map_map,Function.comp_def]

theorem point_reindex_word (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (w : Word α) (representative s fresh old H next incoming : Nat) (enabled : Bool)
    (idx : Mutable.Index) (target : Array Bool) (window : SourceWindow)
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : s+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old)) :
    (Counted.reindex (bankAction (ReplayMaps.word C E (Spec.slice w (representative+fresh) (representative+old))))
      (Mutable.compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s old H next incoming enabled idx target window).1).1=
      (Mutable.compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s fresh H next incoming enabled idx target window).1 := by
  apply Mutable.table_eq
  have hh:=Mutable.compilePointBank_reindex C E book w representative s fresh old H next incoming
    enabled idx target window hnew hH hrep hstart hcopy
  rw [replay_value C E w representative fresh old hnew hrep] at hh
  exact hh

theorem dense_reindex_word (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (representative s q m fresh old H next incoming : Nat) (enabled : Bool)
    (idx : Mutable.Index) (target : Array Bool) (counts : Array Nat) (window : SourceWindow)
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : s+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old)) :
    (Counted.reindex (bankAction (ReplayMaps.word C E (Spec.slice w (representative+fresh) (representative+old))))
      (Mutable.compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m old H next incoming enabled idx target counts window).1).1=
      (Mutable.compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m fresh H next incoming enabled idx target counts window).1 := by
  apply Mutable.table_eq
  have hh:=Mutable.compileDenseBank_reindex C E book prepared w representative s q m fresh old H next incoming
    enabled idx target counts window hnew hH hrep hstart hcopy
  rw [replay_value C E w representative fresh old hnew hrep] at hh
  exact hh

theorem store_reindex (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (sources : Mutable.Batch.Sources) (target : Array Bool) (cfg : Mutable.Store.Config)
    (representative fresh : Nat) (hnew : fresh≤cfg.length) (hH : cfg.length≤cfg.anchor)
    (hrep : representative+cfg.length≤w.length) (hstart : cfg.descriptor.first+cfg.anchor≤w.length)
    (hcopy : Spec.slice w representative (representative+cfg.length)=
      Spec.slice w cfg.descriptor.first (cfg.descriptor.first+cfg.length)) :
    (Mutable.Store.compile C E book prepared (BoundaryApplication.Range.build C w)
      (BoundaryApplication.Range.build E w) sources target cfg).1.map
      (fun bank=>(Counted.reindex (bankAction (ReplayMaps.word C E
        (Spec.slice w (representative+fresh) (representative+cfg.length)))) bank).1)=
    (Mutable.Store.compile C E book prepared (BoundaryApplication.Range.build C w)
      (BoundaryApplication.Range.build E w) sources target (withLength cfg fresh)).1 := by
  by_cases hm : cfg.descriptor.repetitions=0
  · simp only [Mutable.Store.compile,withLength,hm,if_true,Mutable.Batch.compileSingleton,Option.map,Option.some.injEq]
    exact point_reindex_word C E book w representative cfg.descriptor.first fresh cfg.length cfg.anchor
      (cfg.descriptor.nextAt sources.n) cfg.incoming cfg.incomingEnabled sources.singleton target cfg.window
      hnew hH hrep hstart hcopy
  · simp only [Mutable.Store.compile,withLength,hm,if_false]
    cases hid : cfg.runId with
    | none => simp only [Option.map]
    | some id =>
      simp only
      cases hR : sources.runs[id]? with
      | none => simp only [hR,Option.map]
      | some R =>
        simp only [hR]
        by_cases hcover : R.period=cfg.descriptor.period ∧ R.lo≤cfg.descriptor.first ∧
            cfg.descriptor.last+cfg.anchor≤R.hi+1
        · simp only [hcover,true_and,if_true,Mutable.Batch.compileRun]
          by_cases hK : sources.modulus=prepared.K
          · simp only [hK,if_true,hR]
            cases hidx : sources.indexes[id]? with
            | none => simp only [hidx,Option.map]
            | some idx =>
              simp only [hidx,Option.map,Option.some.injEq]
              exact dense_reindex_word C E book prepared w representative cfg.descriptor.first R.period
                cfg.descriptor.repetitions fresh cfg.length cfg.anchor (cfg.descriptor.nextAt sources.n)
                cfg.incoming cfg.incomingEnabled idx target cfg.targetCounts cfg.window
                hnew hH hrep hstart hcopy
          · simp only [hK,if_false,Option.map]
        · simp only [hcover,if_false,Option.map]

end REWB.MaskedTraversalAggregate.Cells
