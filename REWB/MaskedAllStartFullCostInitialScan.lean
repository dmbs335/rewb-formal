import REWB.PeriodicConstructionMaskedPhase
import REWB.MaskedTraversalInitialCost

/-! Execute the measured periodic query inside the actual source scan.
The first projection preserves the complete old state; the second counts
the query construction and concrete scan/record operations. No caller
supplies a semantic answer or a numeric cost at the public entry point. -/
namespace REWB.MaskedAllStart.FullCost.Initial
open REWB.MaskedPeriodic REWB.MaskedPeriodic.Batch REWB.PeriodicConstruction
open REWB.MaskedCut REWB.MaskedCut.DFAIndex
variable {α : Type}

def scan (ask : Nat→Result IndexedAnswer) (source : Array Bool) : Nat→Nat→Batch.State→Result Batch.State
  | 0,_,out=>(out,1)
  | len+1,s,out=>
    if MaskedProgression.readMask source s then
      let ⟨answer,work⟩:=ask s
      let ⟨next,rest⟩:=scan ask source len (s+1) (record s answer out)
      (next,rest+work+16)
    else
      let ⟨next,rest⟩:=scan ask source len (s+1) {out with scanWork:=out.scanWork+3}
      (next,rest+8)

theorem scan_value (ask : Nat→Result IndexedAnswer) (source : Array Bool)
    (len s : Nat) (out : Batch.State) :
    (scan ask source len s out).1=Batch.scan (fun i=>(ask i).1) source len s out := by
  induction len generalizing s out with
  | zero=>rfl
  | succ len ih=>
    rw [scan,Batch.scan]
    split
    · cases ha : ask s with
      | mk answer work=>simp only [ha,ih]
    · exact ih _ _

theorem scan_work (ask : Nat→Result IndexedAnswer) (source : Array Bool)
    (len s limit : Nat) (out : Batch.State) (hb : ∀i,(ask i).2≤limit) :
    (scan ask source len s out).2≤(limit+16)*len+1 := by
  induction len generalizing s out with
  | zero=>simp only [scan,Nat.mul_zero,Nat.zero_add,Nat.le_refl]
  | succ len ih=>
    rw [scan]
    split
    · cases ha : ask s with
      | mk answer work=>
        have h:=ih (s+1) (record s answer out)
        have hw:=hb s
        rw [ha] at hw
        dsimp only at hw ⊢
        rw [Nat.mul_succ]
        omega
    · have h:=ih (s+1) {out with scanWork:=out.scanWork+3}
      dsimp only
      rw [Nat.mul_succ]
      omega

def one (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (n : Nat) (source target : Array Bool)
    (R : RunGeometry.Bounds) (out : Batch.State) : Result Batch.State :=
  let counts:=MaskedProgression.build target R.lo (span R) (prepared.K*R.period)
  let tail:=Text.prepareTail B C E idx R.hi n
  let prep:=counts.slots+counts.arithmetic+tail.products+tail.visits+5
  let ⟨next,work⟩:=scan
    (fun s=>PeriodicConstruction.Masked.query B C E prepared idx tail.map
      s R.hi R.period counts.counts R.lo)
    source (span R) R.lo {out with preparationWork:=out.preparationWork+prep}
  (next,work+prep+8)

theorem one_value (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (n : Nat) (source target : Array Bool)
    (R : RunGeometry.Bounds) (out : Batch.State) :
    (one B C E prepared idx n source target R out).1=
      Batch.one B C E prepared idx n source target R out := by
  simp only [one,scan_value,PeriodicConstruction.Masked.query_value,Batch.one,Nat.add_assoc]

def oneLimit (B C E : DFA α) (K n : Nat) : Nat :=
  queryLimit B C E n+PeriodicConstruction.Masked.queryExtra B.stateCount C.stateCount E.stateCount K+
    preparationLimit n+25

theorem one_work (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (w : Word α) (source target : Array Bool) (R : RunGeometry.Bounds)
    (hn : R.hi≤w.length) (out : Batch.State) :
    (one B C E prepared (DFAIndex.build B C E w).1 w.length source target R out).2≤
      oneLimit B C E prepared.K w.length*span R := by
  let counts:=MaskedProgression.build target R.lo (span R) (prepared.K*R.period)
  let tail:=Text.prepareTail B C E (DFAIndex.build B C E w).1 R.hi w.length
  let ask:=fun s=>PeriodicConstruction.Masked.query B C E prepared
    (DFAIndex.build B C E w).1 tail.map s R.hi R.period counts.counts R.lo
  let prep:=counts.slots+counts.arithmetic+tail.products+tail.visits+5
  have hb : ∀i,(ask i).2≤queryLimit B C E w.length+
      PeriodicConstruction.Masked.queryExtra B.stateCount C.stateCount E.stateCount prepared.K := by
    intro i
    have hc:=PeriodicConstruction.Masked.query_extra B C E prepared
      (DFAIndex.build B C E w).1 tail.map i R.hi R.period counts.counts R.lo
    have hq:=Batch.query_work B C E prepared w tail.map i R.hi R.period counts.counts R.lo hn
    exact Nat.le_trans hc (Nat.add_le_add_right hq _)
  have hs:=scan_work ask source (span R) R.lo _
    {out with preparationWork:=out.preparationWork+prep} hb
  have hp:=MaskedProgression.build_work target R.lo (span R) (prepared.K*R.period)
  have ht:=Text.prepareTail_bounds B C E w R.hi hn
  have hspan : 1≤span R := Nat.succ_le_succ (Nat.zero_le _)
  have hprep:=Nat.mul_le_mul_left (w.length.log2+8) hspan
  have hconstant:=Nat.mul_le_mul_left 9 hspan
  change counts.slots+counts.arithmetic≤13*span R at hp
  change tail.products≤1 ∧ tail.visits≤w.length.log2+2 at ht
  change (scan ask source (span R) R.lo
    {out with preparationWork:=out.preparationWork+prep}).2+prep+8≤_
  unfold oneLimit preparationLimit
  dsimp only [prep] at hs ⊢
  simp only [Nat.mul_one,Nat.add_mul] at hs hprep hconstant ⊢
  omega

end REWB.MaskedAllStart.FullCost.Initial
