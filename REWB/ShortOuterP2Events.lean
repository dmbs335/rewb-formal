import REWB.ShortOuterPrepared

/-! Actual local P2 events.  The join positions are offsets in one short
outer window; exact word-key labels retain their global dictionary IDs.
Every event predicate uses already materialized regular/ready rows. -/
namespace REWB.ShortOuter.P2
open REWB.TimedJoin
variable {σ : Nat}

def sourceOne (P : SevenDFA (Fin σ)) (idx : Prepared P) (p i a : Nat) : List TimedEntry×Nat :=
  Collect.emit (decide (i≤a ∧ p+a≤idx.band.keys.length) &&
    Regular.accepts P.B idx.b p i && Regular.accepts P.C idx.c (p+i) (a-i))
    (Join.entry a (Keys.get idx.band.keys (p+i) (a-i))) 28

def sourceRow (P : SevenDFA (Fin σ)) (idx : Prepared P) (p i : Nat) : List TimedEntry×Nat :=
  Collect.run idx.band.keys.width (sourceOne P idx p i)

def sources (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) : List TimedEntry×Nat :=
  Collect.run idx.band.keys.width (sourceRow P idx p)

def targetOne (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j t : Nat) : List TimedEntry×Nat :=
  let rq:=Ready.query idx.ready p t
  Collect.emit (decide (j≤t ∧ p+t≤idx.band.keys.length) && rq.1)
    (Join.entry j (Keys.get idx.band.keys (p+j) (t-j))) (rq.2+24)

def targetRow (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j : Nat) : List TimedEntry×Nat :=
  Collect.run idx.band.keys.width (targetOne P idx p j)

def targets (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) : List TimedEntry×Nat :=
  Collect.run idx.band.keys.width (targetRow P idx p)

theorem sources_mem (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) (e : TimedEntry) :
    e∈(sources P idx p).1 ↔ ∃i,i<idx.band.keys.width ∧ ∃a,a<idx.band.keys.width ∧
      i≤a ∧ p+a≤idx.band.keys.length ∧ Regular.accepts P.B idx.b p i=true ∧
      Regular.accepts P.C idx.c (p+i) (a-i)=true ∧
      Join.entry a (Keys.get idx.band.keys (p+i) (a-i))=e := by
  simp only [sources,sourceRow,Collect.mem,sourceOne,Collect.emit_mem,
    Bool.and_eq_true,decide_eq_true_eq,and_assoc]

theorem targets_mem (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) (e : TimedEntry) :
    e∈(targets P idx p).1 ↔ ∃j,j<idx.band.keys.width ∧ ∃t,t<idx.band.keys.width ∧
      j≤t ∧ p+t≤idx.band.keys.length ∧ Ready.get idx.ready p t=true ∧
      Join.entry j (Keys.get idx.band.keys (p+j) (t-j))=e := by
  simp only [targets,targetRow,Collect.mem,targetOne,Collect.emit_mem,
    Bool.and_eq_true,decide_eq_true_eq,and_assoc,Ready.get]

theorem sources_plain (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) : Join.Plain (sources P idx p).1 := by
  intro e he
  obtain ⟨i,_,a,_,_,_,_,_,rfl⟩:=(sources_mem P idx p e).mp he
  rfl

theorem targets_plain (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) : Join.Plain (targets P idx p).1 := by
  intro e he
  obtain ⟨j,_,t,_,_,_,_,rfl⟩:=(targets_mem P idx p e).mp he
  rfl

theorem sources_bounded (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) :
    ∀e,e∈(sources P idx p).1→e.pos≤idx.band.keys.width := by
  intro e he
  obtain ⟨i,_,a,ha,_,_,_,_,rfl⟩:=(sources_mem P idx p e).mp he
  exact Nat.le_of_lt ha

theorem targets_bounded (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) :
    ∀e,e∈(targets P idx p).1→e.pos≤idx.band.keys.width := by
  intro e he
  obtain ⟨j,hj,t,_,_,_,_,rfl⟩:=(targets_mem P idx p e).mp he
  exact Nat.le_of_lt hj

theorem sourceRow_length (P : SevenDFA (Fin σ)) (idx : Prepared P) (p i : Nat) :
    (sourceRow P idx p i).1.length≤idx.band.keys.width := by
  simpa only [sourceRow,Nat.mul_one] using Collect.length idx.band.keys.width
    (sourceOne P idx p i) 1 (by intro a _; exact Collect.emit_length _ _ _)

theorem sources_length (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) :
    (sources P idx p).1.length≤idx.band.keys.width*idx.band.keys.width :=
  Collect.length _ _ _ (by intro i _; exact sourceRow_length P idx p i)

theorem sourceRow_work (P : SevenDFA (Fin σ)) (idx : Prepared P) (p i : Nat) :
    (sourceRow P idx p i).2≤idx.band.keys.width*34+4 :=
  Collect.work _ _ 29 1 (by intro a _; exact Nat.le_refl _)
    (by intro a _; exact Collect.emit_length _ _ _)

theorem sources_work (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) :
    (sources P idx p).2≤idx.band.keys.width*(idx.band.keys.width*34+4+idx.band.keys.width+4)+4 :=
  Collect.work _ _ _ _ (by intro i _; exact sourceRow_work P idx p i)
    (by intro i _; exact sourceRow_length P idx p i)

theorem targetOne_length (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j t : Nat) :
    (targetOne P idx p j t).1.length≤1 := Collect.emit_length _ _ _

theorem targetOne_work (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j t : Nat) :
    (targetOne P idx p j t).2≤32 := by
  have h:=Ready.query_work idx.ready p t
  change (Ready.query idx.ready p t).2+24+1≤32
  omega

theorem targetRow_length (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j : Nat) :
    (targetRow P idx p j).1.length≤idx.band.keys.width := by
  simpa only [targetRow,Nat.mul_one] using Collect.length idx.band.keys.width
    (targetOne P idx p j) 1 (by intro t _; exact targetOne_length P idx p j t)

theorem targets_length (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) :
    (targets P idx p).1.length≤idx.band.keys.width*idx.band.keys.width :=
  Collect.length _ _ _ (by intro j _; exact targetRow_length P idx p j)

theorem targetRow_work (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j : Nat) :
    (targetRow P idx p j).2≤idx.band.keys.width*37+4 :=
  Collect.work _ _ 32 1 (by intro t _; exact targetOne_work P idx p j t)
    (by intro t _; exact targetOne_length P idx p j t)

theorem targets_work (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) :
    (targets P idx p).2≤idx.band.keys.width*(idx.band.keys.width*37+4+idx.band.keys.width+4)+4 :=
  Collect.work _ _ _ _ (by intro j _; exact targetRow_work P idx p j)
    (by intro j _; exact targetRow_length P idx p j)

end REWB.ShortOuter.P2
