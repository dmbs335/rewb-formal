import REWB.ShortOuterPrepared

/-! Actual P1 event generation.  Source starts range over the whole text;
only the copied word length is short.  Target endpoint pairs range over
one short outer window and test precomputed DFA/outer-feasibility rows. -/
namespace REWB.ShortOuter.P1
open REWB.TimedJoin
variable {σ : Nat}

def sourceOne (P : SevenDFA (Fin σ)) (idx : Prepared P) (i len : Nat) : List TimedEntry×Nat :=
  Collect.emit (decide (i+len≤idx.band.keys.length) && prefixOK P idx i)
    (Join.entry (i+len) (Keys.get idx.band.keys i len)) 12

def sourceRow (P : SevenDFA (Fin σ)) (idx : Prepared P) (i : Nat) : List TimedEntry×Nat :=
  Collect.run idx.band.keys.width (sourceOne P idx i)

def sources (P : SevenDFA (Fin σ)) (idx : Prepared P) : List TimedEntry×Nat :=
  Collect.run (idx.band.keys.length+1) (sourceRow P idx)

def targetOne (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j t : Nat) : List TimedEntry×Nat :=
  let rq:=Ready.query idx.ready p t
  Collect.emit (decide (j≤t ∧ p+t≤idx.band.keys.length) &&
    Regular.accepts P.D idx.d p j && Regular.accepts P.B idx.b (p+j) (t-j) && rq.1)
    (Join.entry p (Keys.get idx.band.keys (p+j) (t-j))) (rq.2+32)

def targetRow (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j : Nat) : List TimedEntry×Nat :=
  Collect.run idx.band.keys.width (targetOne P idx p j)

def targetBlock (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) : List TimedEntry×Nat :=
  Collect.run idx.band.keys.width (targetRow P idx p)

def targets (P : SevenDFA (Fin σ)) (idx : Prepared P) : List TimedEntry×Nat :=
  Collect.run (idx.band.keys.length+1) (targetBlock P idx)

theorem sources_mem (P : SevenDFA (Fin σ)) (idx : Prepared P) (e : TimedEntry) :
    e∈(sources P idx).1 ↔ ∃i,i≤idx.band.keys.length ∧ ∃len,len<idx.band.keys.width ∧
      i+len≤idx.band.keys.length ∧ prefixOK P idx i=true ∧
      Join.entry (i+len) (Keys.get idx.band.keys i len)=e := by
  simp only [sources,sourceRow,Collect.mem,sourceOne,Collect.emit_mem,
    Bool.and_eq_true,decide_eq_true_eq,Nat.lt_succ_iff,and_assoc]

theorem targets_mem (P : SevenDFA (Fin σ)) (idx : Prepared P) (e : TimedEntry) :
    e∈(targets P idx).1 ↔ ∃p,p≤idx.band.keys.length ∧ ∃j,j<idx.band.keys.width ∧
      ∃t,t<idx.band.keys.width ∧ j≤t ∧ p+t≤idx.band.keys.length ∧
      Regular.accepts P.D idx.d p j=true ∧ Regular.accepts P.B idx.b (p+j) (t-j)=true ∧
      Ready.get idx.ready p t=true ∧ Join.entry p (Keys.get idx.band.keys (p+j) (t-j))=e := by
  simp only [targets,targetBlock,targetRow,Collect.mem,targetOne,Collect.emit_mem,
    Bool.and_eq_true,decide_eq_true_eq,Nat.lt_succ_iff,and_assoc,Ready.get]

theorem sources_plain (P : SevenDFA (Fin σ)) (idx : Prepared P) : Join.Plain (sources P idx).1 := by
  intro e he
  obtain ⟨i,_,len,_,_,_,rfl⟩:=(sources_mem P idx e).mp he
  rfl

theorem targets_plain (P : SevenDFA (Fin σ)) (idx : Prepared P) : Join.Plain (targets P idx).1 := by
  intro e he
  obtain ⟨p,_,j,_,t,_,_,_,_,_,_,rfl⟩:=(targets_mem P idx e).mp he
  rfl

theorem sources_bounded (P : SevenDFA (Fin σ)) (idx : Prepared P) :
    ∀e,e∈(sources P idx).1→e.pos≤idx.band.keys.length := by
  intro e he
  obtain ⟨i,_,len,_,hb,_,rfl⟩:=(sources_mem P idx e).mp he
  exact hb

theorem targets_bounded (P : SevenDFA (Fin σ)) (idx : Prepared P) :
    ∀e,e∈(targets P idx).1→e.pos≤idx.band.keys.length := by
  intro e he
  obtain ⟨p,hp,j,_,t,_,_,_,_,_,_,rfl⟩:=(targets_mem P idx e).mp he
  exact hp

theorem sourceRow_length (P : SevenDFA (Fin σ)) (idx : Prepared P) (i : Nat) :
    (sourceRow P idx i).1.length≤idx.band.keys.width := by
  simpa only [sourceRow,Nat.mul_one] using Collect.length idx.band.keys.width
    (sourceOne P idx i) 1 (by intro j _; exact Collect.emit_length _ _ _)

theorem sources_length (P : SevenDFA (Fin σ)) (idx : Prepared P) :
    (sources P idx).1.length≤(idx.band.keys.length+1)*idx.band.keys.width :=
  Collect.length _ _ _ (by intro i _; exact sourceRow_length P idx i)

theorem sourceRow_work (P : SevenDFA (Fin σ)) (idx : Prepared P) (i : Nat) :
    (sourceRow P idx i).2≤idx.band.keys.width*18+4 :=
  Collect.work _ _ 13 1 (by intro j _; exact Nat.le_refl _)
    (by intro j _; exact Collect.emit_length _ _ _)

theorem sources_work (P : SevenDFA (Fin σ)) (idx : Prepared P) :
    (sources P idx).2≤(idx.band.keys.length+1)*(idx.band.keys.width*18+4+idx.band.keys.width+4)+4 :=
  Collect.work _ _ _ _ (by intro i _; exact sourceRow_work P idx i)
    (by intro i _; exact sourceRow_length P idx i)

theorem targetOne_length (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j t : Nat) :
    (targetOne P idx p j t).1.length≤1 := Collect.emit_length _ _ _

theorem targetOne_work (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j t : Nat) :
    (targetOne P idx p j t).2≤40 := by
  have h:=Ready.query_work idx.ready p t
  change (Ready.query idx.ready p t).2+32+1≤40
  omega

theorem targetRow_length (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j : Nat) :
    (targetRow P idx p j).1.length≤idx.band.keys.width := by
  simpa only [targetRow,Nat.mul_one] using Collect.length idx.band.keys.width
    (targetOne P idx p j) 1 (by intro t _; exact targetOne_length P idx p j t)

theorem targetBlock_length (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) :
    (targetBlock P idx p).1.length≤idx.band.keys.width*idx.band.keys.width :=
  Collect.length _ _ _ (by intro j _; exact targetRow_length P idx p j)

theorem targets_length (P : SevenDFA (Fin σ)) (idx : Prepared P) :
    (targets P idx).1.length≤(idx.band.keys.length+1)*(idx.band.keys.width*idx.band.keys.width) :=
  Collect.length _ _ _ (by intro p _; exact targetBlock_length P idx p)

theorem targetRow_work (P : SevenDFA (Fin σ)) (idx : Prepared P) (p j : Nat) :
    (targetRow P idx p j).2≤idx.band.keys.width*45+4 :=
  Collect.work _ _ 40 1 (by intro t _; exact targetOne_work P idx p j t)
    (by intro t _; exact targetOne_length P idx p j t)

theorem targetBlock_work (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) :
    (targetBlock P idx p).2≤idx.band.keys.width*(idx.band.keys.width*45+4+idx.band.keys.width+4)+4 :=
  Collect.work _ _ _ _ (by intro j _; exact targetRow_work P idx p j)
    (by intro j _; exact targetRow_length P idx p j)

theorem targets_work (P : SevenDFA (Fin σ)) (idx : Prepared P) :
    (targets P idx).2≤(idx.band.keys.length+1)*
      (idx.band.keys.width*(idx.band.keys.width*45+4+idx.band.keys.width+4)+4+
        idx.band.keys.width*idx.band.keys.width+4)+4 :=
  Collect.work _ _ _ _ (by intro p _; exact targetBlock_work P idx p)
    (by intro p _; exact targetBlock_length P idx p)

end REWB.ShortOuter.P1
