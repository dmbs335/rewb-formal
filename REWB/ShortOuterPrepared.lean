import REWB.ShortOuterCollect
import REWB.ShortOuterJoin

/-! One concrete short-outer preparation shared by the two nested forms.
All text-length dependent scans happen here or in the bounded event
builders.  Later prefix and bounded-factor predicates are array reads. -/
namespace REWB.ShortOuter
open REWB.Periodic
variable {σ : Nat}

structure Prepared (P : SevenDFA (Fin σ)) where
  band : Band.Index σ
  ready : Ready.Index
  pref : Array (Fin P.A.stateCount)
  b : Regular.Index P.B
  c : Regular.Index P.C
  d : Regular.Index P.D
  work : Nat

def prepare (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit : Nat) : Prepared P :=
  let band:=Band.build P.G P.H text fallback limit
  let ready:=Ready.build P.F text fallback band
  let pref:=Regular.row P.A (ArrayText.read text fallback) 0 text.size
  let b:=Regular.build P.B text fallback band.keys.width
  let c:=Regular.build P.C text fallback band.keys.width
  let d:=Regular.build P.D text fallback band.keys.width
  ⟨band,ready,pref.1,b,c,d,band.work+ready.work+pref.2+b.work+c.work+d.work+8⟩

def prefixOK (P : SevenDFA (Fin σ)) (idx : Prepared P) (p : Nat) : Bool :=
  P.A.final ((idx.pref[p]?).getD P.A.initial)

@[simp] theorem prepare_length (P : SevenDFA (Fin σ)) (text : Array (Fin σ))
    (fallback : Fin σ) (limit : Nat) : (prepare P text fallback limit).band.keys.length=text.size := rfl

@[simp] theorem prepare_width (P : SevenDFA (Fin σ)) (text : Array (Fin σ))
    (fallback : Fin σ) (limit : Nat) :
    (prepare P text fallback limit).band.keys.width=min limit (text.size+1) := rfl

theorem prefix_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p : Nat) (hp : p≤text.size) :
    prefixOK P (prepare P text fallback limit) p=true ↔
      P.A.accepts (segment (ArrayText.read text fallback) 0 p) := by
  simp only [prefixOK,prepare,Regular.row_get P.A _ 0 text.size p hp,Option.getD_some,DFA.accepts]

def prepareBudget (P : SevenDFA (Fin σ)) (n limit : Nat) : Nat :=
  let b:=min limit (n+1)
  Band.budget σ P.G.stateCount P.H.stateCount n b+
    (n+1)*(b*(6*P.F.stateCount+21)+3*P.F.stateCount+33)+4+
    (6*n+6)+3*((n+1)*(6*b+10)+4)+8

theorem prepare_work (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit : Nat) : (prepare P text fallback limit).work≤prepareBudget P text.size limit := by
  have hb:=Band.build_work P.G P.H text fallback limit
  simp only [prepare,Ready.build_work,Regular.row_work,Regular.build_work,
    Band.build_keys,Keys.build_width,prepareBudget]
  omega

end REWB.ShortOuter
