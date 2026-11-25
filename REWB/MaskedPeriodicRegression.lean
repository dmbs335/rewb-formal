import REWB.MaskedPeriodicPhase

/-! Small kernel regressions and a direct finite audit reference.
    Exponent/cut enumeration occurs only in the reference below, never
    in the indexed production query.
-/
namespace REWB.MaskedPeriodic.Regression
open REWB.MaskedFiniteAction.Maps REWB.MaskedCut.DFAIndex REWB.Periodic

def universal : DFA Bool := ⟨1,0,fun _ _=>0,fun _=>true⟩
def odd : DFA Bool := ⟨2,0,fun state letter=>
  if letter then (if state=0 then 1 else 0) else state,fun state=>decide (state=1)⟩
def even : DFA Bool := ⟨2,0,fun state letter=>
  if letter then (if state=0 then 1 else 0) else state,fun state=>decide (state=0)⟩

def unitData : Data 1 1 1 := fromTuple universal universal universal
  (jointWord universal universal universal [true])
  (wordTuple universal universal universal [] [] []) (wordMap universal [])

def point (branch : Branch) (N k : Nat) : Bool :=
  AffineProjection.decideFormula (projection unitData branch N).1 [(k:Int)]

set_option maxRecDepth 4096 in
theorem projected_boundary_cases :
    point .zero 6 2=true ∧ point .zero 6 4=true ∧ point .zero 6 5=false ∧
    point .interior 6 3=true ∧ point .interior 6 4=false ∧
    point .ending 6 4=true ∧ point .ending 6 3=false := by decide

def oneIndex := (build universal universal universal [true,true]).1

theorem positive_cut_empty :
    (interiorTuples universal universal universal oneIndex 0 1).values=[] ∧
    (endingTuples universal universal universal oneIndex 0 0 1).values=[] := by constructor <;> rfl

theorem geometry_endpoints :
    Physical 3 1 1 7 3 4 ∧ ¬Physical 3 0 1 7 3 4 ∧
    ¬Physical 3 1 1 6 3 3 ∧ Physical 3 0 0 6 3 3 := by unfold Physical; decide

def accept (d : DFA Bool) (w : Word Bool) : Bool := d.final (d.run d.initial w)

/-- Direct version of the three audited word-factor cases. The loop
    bounds are finite test bounds, not a purported fast compiler. -/
def directPhase (b c e : DFA Bool) (V tail : Word Bool) (eta N : Nat)
    (mask : Array Bool) (base len s : Nat) : Bool :=
  (List.range V.length).any fun rho=>
    (List.range (N+1)).any fun a=>
      (List.range (N+1)).any fun k=>
        let carry := if rho=0 then 0 else 1
        let gap := if rho=0 then repeatWord V (k-a) else V.drop rho++repeatWord V (k-a-1)
        let suffix := if rho=0 then repeatWord V (N-k-a)++V.take eta++tail
          else if k+a=N then (V.drop rho).take (eta-rho)++tail
          else V.drop rho++repeatWord V (N-k-a-1)++V.take eta++tail
        decide (2≤a ∧ a+carry≤k ∧ k+a≤N ∧ (k+a=N → rho≤eta) ∧
          base≤s+k*V.length ∧ s+k*V.length<base+len) &&
          MaskedProgression.readMask mask (s+k*V.length) &&
          accept b (repeatWord V a++V.take rho) && accept c gap && accept e suffix

def irregularMask : Array Bool := Array.ofFn fun i : Fin 40=>
  decide (i.val=3 ∨ i.val=7 ∨ i.val=8 ∨ i.val=16 ∨ i.val=19 ∨ i.val=27 ∨ i.val=31 ∨ i.val=38)

end REWB.MaskedPeriodic.Regression
