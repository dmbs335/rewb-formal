import REWB.CountedJoin
import REWB.P1ShortSources

/-! The existing concrete dyadic join specialized to literal true events.
The scalar charge retains the actual scan, filter/sort, event, text and
node counters.  Fixed-size cut-vector materialization and the constant
`K=1`, `N=0`, `[[]]` formula conversions are charged per visited text/event
cell; power construction is covered by height times visited nodes. -/
namespace REWB.ShortOuter.Join
open REWB.TimedJoin
variable {α : Type}

abbrev entry := P1ShortSources.trueEntry

def Plain (es : List TimedEntry) : Prop := ∀e,e∈es→e.entry.formula=[[]]

theorem plain_good (es : List TimedEntry) (hp : Plain es) : Good 1 es := by
  intro e he
  rw [hp e he]
  exact P1ShortSources.trueEntry_good 0 0 1

theorem plain_weight (es : List TimedEntry) (hp : Plain es) : TimedJoin.weight es=es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [TimedJoin.weight,List.length_cons,hp e (by simp),List.length_singleton,List.length_nil]
    rw [ih (by intro x hx; exact hp x (by simp [hx]))]
    omega

def Match (d : DFA α) (w : Word α) (es fs : List TimedEntry) : Prop :=
  ∃e,e∈es ∧ ∃f,f∈fs ∧ e.pos≤f.pos ∧ f.pos≤w.length ∧
    e.entry.key=f.entry.key ∧ d.accepts (Spec.slice w e.pos f.pos)

def coefficient (k : Nat) := 32*k+64

structure Result where
  value : Bool
  measured : CountedJoin.Result
  work : Nat
  deriving Repr

def run (d : DFA α) (w : Word α) (es fs : List TimedEntry) : Result :=
  let n:=w.length
  let h:=DyadicIndex.heightFor n
  let out:=CountedJoin.solve d 1 0 h w es fs
  ⟨out.value.answer,out,
    out.sortSteps+coefficient d.stateCount*(out.value.tests+out.value.eventVisits+
      out.value.textVisits+(h+1)*out.value.nodes)+n+h+3⟩

theorem run_correct (d : DFA α) (w : Word α) (es fs : List TimedEntry)
    (hs : Plain es) (ht : Plain fs)
    (he : ∀e,e∈es→e.pos≤w.length) (hf : ∀f,f∈fs→f.pos≤w.length) :
    (run d w es fs).value=true ↔ Match d w es fs := by
  change (CountedJoin.run d 1 0 w es fs).value.answer=true ↔ _
  rw [CountedJoin.run_correct d 1 0 w es fs (by decide) (plain_good es hs) (plain_good fs ht) he hf]
  constructor
  · rintro ⟨e,hem,f,hfm,hef,hfn,hkey,hd,_⟩
    exact ⟨e,hem,f,hfm,hef,hfn,hkey,hd⟩
  · rintro ⟨e,hem,f,hfm,hef,hfn,hkey,hd⟩
    refine ⟨e,hem,f,hfm,hef,hfn,hkey,hd,0,Nat.le_refl _,?_,?_⟩
    · rw [hs e hem]
      exact P1ShortSources.trueEntry_satisfies 0 0 [0]
    · rw [ht f hfm]
      exact P1ShortSources.trueEntry_satisfies 0 0 [0]

def budget (k n e f : Nat) : Nat :=
  let h:=DyadicIndex.heightFor n
  let z:=e+k*f
  (h+1)*(10*z*(z.log2+1)+coefficient k*(z+e+f+n+2^(h+1)))+n+h+3

theorem run_work (d : DFA α) (w : Word α) (es fs : List TimedEntry)
    (hs : Plain es) (ht : Plain fs) :
    (run d w es fs).work≤budget d.stateCount w.length es.length fs.length := by
  let h:=DyadicIndex.heightFor w.length
  let z:=es.length+d.stateCount*fs.length
  have hw : CountedJoin.weight d 1 es fs=z := by
    simp only [CountedJoin.weight,plain_weight es hs,plain_weight fs ht,Nat.one_mul,z]
  have hsrt:=CountedJoin.solve_steps d 1 0 h w es fs
  rw [hw] at hsrt
  have hv:=OfflineJoin.solve_cost d 1 0 h w es fs
  rw [←CountedJoin.solve_value d 1 0 h w es fs] at hv
  simp only [plain_weight es hs,plain_weight fs ht,Nat.one_mul] at hv
  have htests : (CountedJoin.solve d 1 0 h w es fs).value.tests≤(h+1)*z := hv.1
  have hev := hv.2.1
  have htext := hv.2.2.1
  have hnodes := hv.2.2.2
  have hn : (h+1)*(CountedJoin.solve d 1 0 h w es fs).value.nodes≤(h+1)*2^(h+1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hall := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add htests hev) htext) hn
  have hm:=Nat.mul_le_mul_left (coefficient d.stateCount) hall
  change (CountedJoin.solve d 1 0 h w es fs).sortSteps+
      coefficient d.stateCount*((CountedJoin.solve d 1 0 h w es fs).value.tests+
      (CountedJoin.solve d 1 0 h w es fs).value.eventVisits+
      (CountedJoin.solve d 1 0 h w es fs).value.textVisits+
      (h+1)*(CountedJoin.solve d 1 0 h w es fs).value.nodes)+w.length+h+3≤_
  change _≤(h+1)*(10*z*(z.log2+1)+coefficient d.stateCount*
    (z+es.length+fs.length+w.length+2^(h+1)))+w.length+h+3
  have hsum : coefficient d.stateCount*((h+1)*z+(h+1)*(es.length+fs.length)+
      (h+1)*w.length+(h+1)*2^(h+1))=
      (h+1)*(coefficient d.stateCount*(z+es.length+fs.length+w.length+2^(h+1))) := by
    simp only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.add_assoc]
  rw [hsum] at hm
  have htotal:=Nat.add_le_add hsrt hm
  rw [←Nat.mul_add] at htotal
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right htotal w.length) h) 3

end REWB.ShortOuter.Join
