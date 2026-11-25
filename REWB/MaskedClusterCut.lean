import REWB.MaskedClusterBankCorrect

/-! Select a replay-bank entry and B-prefix acceptance from one actual
    shared text cut. No length or occurrence is enumerated by the query.
    The returned cut matrix is scanned once through its stored cells,
    preserving each joint prefix/suffix pair. In particular, independent
    B-prefix and C/E-suffix witnesses cannot be combined accidentally.

    Counters retain the shared index's summary products/visits and count
    every stored cut-cell probe. Fixed-pattern map encoding/monoid work
    remains a separate factor, as in MaskedCutIndex. Source components
    may already have been projected and multiplied by the caller.
-/
namespace REWB.MaskedCluster.Cut
open REWB.MaskedFiniteAction REWB.MaskedCut.DFAIndex
variable {α : Type} {m : Nat}

structure Shared (B C E : DFA α) where
  tree : MaskedCut.Index.Tree (jointEnum B C E)
  length : Nat
  products : Nat

def build (B C E : DFA α) (w : Word α) : Shared B C E :=
  let out:=MaskedCut.DFAIndex.build B C E w
  ⟨out.1,w.length,out.2⟩

theorem build_products (B C E : DFA α) (w : Word α) :
    (build B C E w).products=(Nat.log2 w.length+1)*w.length :=
  MaskedCut.DFAIndex.build_products B C E w

def acceptCell (B C E : DFA α) (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (i j : Fin m) (cell : MatrixTable.Cell (Joint B C E)) : Bool :=
  cell.2.2 && B.final (cell.1.1.get B.initial) &&
    bank.view (ReplayMaps.encode (cell.2.1.2.1,cell.2.1.2.2)) i j

def scanCells (B C E : DFA α) (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (i j : Fin m) (cuts : MatrixTable.Matrix (jointEnum B C E)) : Bool×Nat :=
  BoundaryIndex.Counted.scan (acceptCell B C E bank i j) cuts.data

theorem scanCells_correct (B C E : DFA α) (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (i j : Fin m) (cuts : MatrixTable.Matrix (jointEnum B C E)) :
    (scanCells B C E bank i j cuts).1=true ↔ ∃ p s,
      MatrixTable.denote cuts p s=true ∧ B.final (p.1.get B.initial)=true ∧
        bank.view (ReplayMaps.encode (s.2.1,s.2.2)) i j=true := by
  simp only [scanCells,BoundaryIndex.Counted.scan_value,List.any_eq_true,acceptCell,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨p,s,bit⟩,hmem,⟨hbit,hB⟩,hbank⟩
    change bit=true at hbit
    subst bit
    exact ⟨p,s,(MatrixTable.read_true cuts.data p s).mpr hmem,hB,hbank⟩
  · rintro ⟨p,s,hcut,hB,hbank⟩
    exact ⟨(p,s,true),(MatrixTable.read_true cuts.data p s).mp hcut,⟨rfl,hB⟩,hbank⟩

theorem scanCells_probes (B C E : DFA α) (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (i j : Fin m) (cuts : MatrixTable.Matrix (jointEnum B C E)) :
    (scanCells B C E bank i j cuts).2=(jointEnum B C E).elems.length*(jointEnum B C E).elems.length := by
  rw [scanCells,BoundaryIndex.Counted.scan_steps,MatrixTable.matrix_size]

structure Result where
  answer : Bool
  products : Nat
  visits : Nat
  tupleProbes : Nat
  arithmetic : Nat

/-- `lo` and `hi` are inclusive copy lengths, bounded by the current old
    length. Empty/reversed or out-of-bounds requests return false. Text
    length is cached in `Shared`; no per-query word-length scan occurs. -/
def query (B C E : DFA α) (idx : Shared B C E)
    (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (representative lo hi old : Nat) (i j : Fin m) : Result :=
  if lo≤hi ∧ hi≤old ∧ representative+old≤idx.length then
    let cuts:=MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) idx.tree
      representative (representative+lo) (representative+hi) (representative+old)
    match cuts.answer with
    | none => ⟨false,cuts.products,cuts.visits,0,8⟩
    | some table =>
      let out:=scanCells B C E bank i j table
      ⟨out.1,cuts.products,cuts.visits,out.2,8⟩
  else ⟨false,0,0,0,4⟩

theorem query_empty (B C E : DFA α) (idx : Shared B C E)
    (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (representative lo hi old : Nat) (i j : Fin m) (h : ¬lo≤hi) :
    (query B C E idx bank representative lo hi old i j).answer=false := by
  simp only [query,h,false_and,if_false]

theorem query_correct (B C E : DFA α) (w : Word α)
    (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (representative lo hi old : Nat) (i j : Fin m)
    (hlo : lo≤hi) (hhi : hi≤old) (hn : representative+old≤w.length) :
    (query B C E (build B C E w) bank representative lo hi old i j).answer=true ↔
      ∃ L,lo≤L ∧ L≤hi ∧ B.accepts (Spec.slice w representative (representative+L)) ∧
        bank.view (ReplayMaps.encode (ReplayMaps.word C E
          (Spec.slice w (representative+L) (representative+old)))) i j=true := by
  have hq (p s : Joint B C E) := MaskedCut.DFAIndex.query_correct B C E w
    representative (representative+lo) (representative+hi) (representative+old) p s
    (by omega) (by omega) (by omega) hn
  cases hc : (MaskedCut.Index.query (jointOps B C E) (jointEnum B C E)
      (MaskedCut.DFAIndex.build B C E w).1 representative (representative+lo)
      (representative+hi) (representative+old)).answer with
  | none =>
    have hh:=(hq (jointWord B C E (Spec.slice w representative (representative+lo)))
      (jointWord B C E (Spec.slice w (representative+lo) (representative+old)))).mpr
      ⟨representative+lo,Nat.le_refl _,by omega,rfl,rfl⟩
    simp only [hc,Option.map] at hh
    cases hh
  | some cuts =>
    simp only [hc,Option.map,Option.some.injEq] at hq
    simp only [query,build,hlo,hhi,hn,true_and,if_true,hc]
    rw [scanCells_correct]
    constructor
    · rintro ⟨p,s,hcut,hB,hbank⟩
      obtain ⟨pos,hl,hh,hp,hs⟩:=(hq p s).mp hcut
      have he : representative+(pos-representative)=pos := by omega
      refine ⟨pos-representative,by omega,by omega,?_,?_⟩
      · rw [←hp] at hB
        simpa only [he,jointWord,Maps.wordMap_get,DFA.accepts] using hB
      · rw [←hs] at hbank
        simpa only [he,jointWord,ReplayMaps.word] using hbank
    · rintro ⟨L,hl,hh,hB,hbank⟩
      refine ⟨jointWord B C E (Spec.slice w representative (representative+L)),
        jointWord B C E (Spec.slice w (representative+L) (representative+old)),?_,?_,?_⟩
      · exact (hq _ _).mpr ⟨representative+L,by omega,by omega,rfl,rfl⟩
      · simpa only [jointWord,Maps.wordMap_get,DFA.accepts] using hB
      · simpa only [jointWord,ReplayMaps.word] using hbank

theorem query_bounds (B C E : DFA α) (w : Word α)
    (bank : Table (ReplayMaps.count C.stateCount E.stateCount) m)
    (representative lo hi old : Nat) (i j : Fin m) :
    (query B C E (build B C E w) bank representative lo hi old i j).products≤3 ∧
    (query B C E (build B C E w) bank representative lo hi old i j).visits≤3*(Nat.log2 w.length+2) ∧
    (query B C E (build B C E w) bank representative lo hi old i j).tupleProbes≤
      (jointEnum B C E).elems.length*(jointEnum B C E).elems.length ∧
    (query B C E (build B C E w) bank representative lo hi old i j).arithmetic≤8 := by
  by_cases h : lo≤hi ∧ hi≤old ∧ representative+old≤w.length
  · have hh:=MaskedCut.Index.query_bounds (jointOps B C E) (jointEnum B C E) (letters B C E w)
      representative (representative+lo) (representative+hi) (representative+old)
      (by omega) (by omega) (by omega) (by simpa only [letters_length] using h.2.2)
    simp only [letters_length] at hh
    cases hc : (MaskedCut.Index.query (jointOps B C E) (jointEnum B C E)
      (MaskedCut.DFAIndex.build B C E w).1 representative (representative+lo)
      (representative+hi) (representative+old)).answer <;>
      simp only [query,build,h,true_and,if_true,hc,scanCells_probes] <;> exact ⟨hh.1,hh.2,by omega,by decide⟩
  · simp only [query,build,h,if_false]
    exact ⟨by decide,Nat.zero_le _,Nat.zero_le _,by decide⟩

end REWB.MaskedCluster.Cut
