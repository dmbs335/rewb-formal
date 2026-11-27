import REWB.MaskedTraversalAggregate
import REWB.MaskedClusterCut

/-! One shared B-prefix/replay cut for the entire aggregate. Closing
the aggregate to waiting/accepting-suffix states is a fixed-pattern table
operation. The cut index is queried once, not once per length or cluster.
All matrices therefore use the same actual copy length.
-/
namespace REWB.MaskedTraversalAggregate
open REWB.MaskedFiniteAction REWB.MaskedCluster
variable {α : Type} {h : Nat}

def close (C E : DFA α)
    (bank : Table (ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)) :
    Table (ReplayMaps.count C.stateCount E.stateCount) 1×Nat :=
  let rows:=Vector.ofFn fun key=>BoundaryIndex.Counted.scan
    (fun q : Fin E.stateCount=>E.final q && bank.view key
      (code _ false (MaskedClusterStage.encode C E .waiting))
      (code _ false (MaskedClusterStage.encode C E (.suffix q)))) (List.ofFn id)
  (⟨Vector.ofFn fun key=>Vector.singleton (Vector.singleton (rows.get key).1)⟩,
    BoundaryIndex.Counted.rowWork rows)

theorem close_correct (C E : DFA α)
    (bank : Table (ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount))
    (key : Fin (ReplayMaps.count C.stateCount E.stateCount)) :
    (close C E bank).1.view key 0 0=true ↔ ∃q : Fin E.stateCount,E.final q=true ∧
      bank.view key (code _ false (MaskedClusterStage.encode C E .waiting))
        (code _ false (MaskedClusterStage.encode C E (.suffix q)))=true := by
  simp only [close,Table.view,BoundaryIndex.Table.get_ofFn]
  change (BoundaryIndex.Counted.scan
    (fun q : Fin E.stateCount=>E.final q && bank.view key
      (code _ false (MaskedClusterStage.encode C E .waiting))
      (code _ false (MaskedClusterStage.encode C E (.suffix q)))) (List.ofFn id)).1=true ↔ _
  simp only [BoundaryIndex.Counted.scan_value,List.any_eq_true,Bool.and_eq_true,List.mem_ofFn]
  constructor
  · rintro ⟨q,_,h⟩
    exact ⟨q,h⟩
  · rintro ⟨q,h⟩
    exact ⟨q,⟨q,rfl⟩,h⟩

/-- Actual finite scan probes plus output cells; map encoding is a
fixed-pattern factor, separate from the text-dependent operation count. -/
theorem close_probes (C E : DFA α)
    (bank : Table (ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)) :
    (close C E bank).2=ReplayMaps.count C.stateCount E.stateCount*(E.stateCount+1) := by
  simp only [close,BoundaryIndex.Counted.rowWork,BoundaryIndex.Table.get_ofFn,
    BoundaryIndex.Counted.scan_steps,List.length_ofFn,BoundaryIndex.Counted.sum_ofFn_const]

structure BandResult where
  answer : Bool
  aggregateWork : Nat
  closureProbes : Nat
  cutProducts : Nat
  cutVisits : Nat
  cutProbes : Nat
  arithmetic : Nat
  deriving Repr

def queryBand (B C E : DFA α) (cut : Cut.Shared B C E) (tree : BankTree C E h)
    (sourceLo sourceHi representative lengthLo lengthHi old : Nat) : BandResult :=
  let product:=region tree sourceLo sourceHi
  let finalBank:=close C E product.1
  let out:=Cut.query B C E cut finalBank.1 representative lengthLo lengthHi old 0 0
  ⟨out.answer,product.2,finalBank.2,out.products,out.visits,out.tupleProbes,out.arithmetic+3⟩

theorem queryBand_correct (B C E : DFA α) (w : Word α) (tree : BankTree C E h)
    (hg : tree.Good) (sourceLo sourceHi representative lengthLo lengthHi old : Nat)
    (hl : lengthLo≤lengthHi) (hh : lengthHi≤old) (hn : representative+old≤w.length) :
    (queryBand B C E (Cut.build B C E w) tree sourceLo sourceHi representative lengthLo lengthHi old).answer=true ↔
      ∃L,lengthLo≤L ∧ L≤lengthHi ∧ B.accepts (Spec.slice w representative (representative+L)) ∧
        ∃q : Fin E.stateCount,E.final q=true ∧
          Chain (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+L) (representative+old))))
            (regionCells tree.leaves sourceLo sourceHi)
            (code _ false (MaskedClusterStage.encode C E .waiting))
            (code _ false (MaskedClusterStage.encode C E (.suffix q))) := by
  rw [queryBand,Cut.query_correct B C E w _ representative lengthLo lengthHi old 0 0 hl hh hn]
  simp only [close_correct,region_chain tree hg]

theorem queryBand_counters (B C E : DFA α) (w : Word α) (tree : BankTree C E h)
    (sourceLo sourceHi representative lengthLo lengthHi old : Nat) :
    let out:=queryBand B C E (Cut.build B C E w) tree sourceLo sourceHi representative lengthLo lengthHi old
    out.closureProbes=ReplayMaps.count C.stateCount E.stateCount*(E.stateCount+1) ∧
    out.cutProducts≤3 ∧ out.cutVisits≤3*(Nat.log2 w.length+2) ∧
    out.cutProbes≤(MaskedCut.DFAIndex.jointEnum B C E).elems.length*(MaskedCut.DFAIndex.jointEnum B C E).elems.length ∧
    out.arithmetic≤11 := by
  have hw:=Cut.query_bounds B C E w (close C E (region tree sourceLo sourceHi).1).1
    representative lengthLo lengthHi old 0 0
  exact ⟨close_probes C E _,hw.1,hw.2.1,hw.2.2.1,Nat.add_le_add_right hw.2.2.2 3⟩

end REWB.MaskedTraversalAggregate
