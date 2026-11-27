import REWB.MaskedOrderedOwnerQuery
import REWB.RunDedup

/-! One tail-recursive pass over the emitted event array. Successful
extensions are consed into a list, then the existing exact binary-key
registry removes duplicates in logarithmic work per candidate. -/
namespace REWB.MaskedOrdered.Owner
open REWB.RunGeometry (Bounds)
variable {h σ : Nat}

def accept (x : Option Bounds) (acc : List Bounds) : List Bounds :=
  match x with
  | none => acc
  | some R => R::acc

theorem accept_mem (x : Option Bounds) (acc : List Bounds) (R : Bounds) :
    R∈accept x acc ↔ x=some R ∨ R∈acc := by
  cases x <;> simp [accept,eq_comm]

theorem accept_length (x : Option Bounds) (acc : List Bounds) :
    (accept x acc).length≤acc.length+1 := by cases x <;> simp [accept]

def collect.go (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) :
    Nat→Nat→List Bounds→Nat→List Bounds×Nat
  | 0,_,acc,work => (acc,work+1)
  | remaining+1,start,acc,work =>
    match events[start]? with
    | none => (acc,work+2)
    | some e =>
      let r:=probe forward backward n cap nodes e
      go forward backward n cap nodes events remaining (start+1)
        (accept r.1 acc) (work+r.2+5)

def collect (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) : List Bounds×Nat :=
  collect.go forward backward n cap nodes events events.size 0 [] 0

theorem collect.go_work (f : Nat→Fin σ) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) (remaining start : Nat)
    (acc : List Bounds) (work : Nat) :
    (go (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) n cap nodes events
      remaining start acc work).2≤work+remaining*(probeBudget h n+5)+1 := by
  induction remaining generalizing start acc work with
  | zero => simp [go]
  | succ remaining ih =>
    cases he : events[start]? with
    | none => simp only [go,he,Nat.add_mul,Nat.one_mul]; omega
    | some e =>
      have hp:=probe_work f n cap nodes e
      have hh:=ih (start+1)
        (accept (probe (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) n cap nodes e).1 acc)
        (work+(probe (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) n cap nodes e).2+5)
      simp only [go,he,Nat.add_mul,Nat.one_mul]
      omega

theorem collect.go_length (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) (remaining start : Nat)
    (acc : List Bounds) (work : Nat) :
    (go forward backward n cap nodes events remaining start acc work).1.length≤acc.length+remaining := by
  induction remaining generalizing start acc work with
  | zero => exact Nat.le_refl _
  | succ remaining ih =>
    cases he : events[start]? with
    | none => simp only [go,he]; omega
    | some e =>
      have ha:=accept_length (probe forward backward n cap nodes e).1 acc
      have hh:=ih (start+1) (accept (probe forward backward n cap nodes e).1 acc)
        (work+(probe forward backward n cap nodes e).2+5)
      simp only [go,he]
      omega

theorem collect.go_mem (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) (remaining start : Nat)
    (acc : List Bounds) (work : Nat) (hb : start+remaining≤events.size) (R : Bounds) :
    R∈(go forward backward n cap nodes events remaining start acc work).1 ↔
      R∈acc ∨ ∃i,start≤i ∧ i<start+remaining ∧
        ∃e,events[i]?=some e ∧ (probe forward backward n cap nodes e).1=some R := by
  induction remaining generalizing start acc work with
  | zero =>
    simp only [go,Nat.add_zero]
    constructor
    · exact Or.inl
    · rintro (hr|⟨i,hlo,hhi,_⟩)
      · exact hr
      · omega
  | succ remaining ih =>
    have hi : start<events.size := by omega
    rw [go,Array.getElem?_eq_getElem hi,ih (start+1) _ _ (by omega),accept_mem]
    constructor
    · rintro ((hr|hr)|⟨i,hlo,hhi,e,he,hr⟩)
      · exact Or.inr ⟨start,Nat.le_refl _,by omega,events[start],Array.getElem?_eq_getElem hi,hr⟩
      · exact Or.inl hr
      · exact Or.inr ⟨i,by omega,by omega,e,he,hr⟩
    · rintro (hr|⟨i,hlo,hhi,e,he,hr⟩)
      · exact Or.inl (Or.inr hr)
      · by_cases heq : i=start
        · subst i
          have hev : e=events[start] := by
            rw [Array.getElem?_eq_getElem hi] at he
            exact (Option.some.inj he).symm
          subst e
          exact Or.inl (Or.inl hr)
        · exact Or.inr ⟨i,by omega,by omega,e,he,hr⟩

theorem collect_mem (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) (R : Bounds) :
    R∈(collect forward backward n cap nodes events).1 ↔
      ∃e,e∈events.toList ∧ (probe forward backward n cap nodes e).1=some R := by
  rw [collect,collect.go_mem _ _ _ _ _ _ _ _ _ _ (by omega)]
  simp only [List.not_mem_nil,false_or,Nat.zero_add]
  constructor
  · rintro ⟨i,_,_,e,he,hr⟩
    exact ⟨e,by simpa only [Array.mem_toList] using Array.mem_of_getElem? he,hr⟩
  · rintro ⟨e,he,hr⟩
    have he' : e∈events := by simpa only [Array.mem_toList] using he
    obtain ⟨i,hi⟩:=Array.getElem?_of_mem he'
    exact ⟨i,Nat.zero_le _,(Array.getElem?_eq_some_iff.mp hi).1,e,hi,hr⟩

theorem collect_work (f : Nat→Fin σ) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) :
    (collect (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) n cap nodes events).2≤
      events.size*(probeBudget h n+5)+1 := by
  simpa only [collect,Nat.zero_add] using
    collect.go_work f n cap nodes events events.size 0 [] 0

theorem collect_length (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) :
    (collect forward backward n cap nodes events).1.length≤events.size := by
  simpa only [collect,List.length_nil,Nat.zero_add] using
    collect.go_length forward backward n cap nodes events events.size 0 [] 0

structure Batch where
  runs : List Bounds
  work : Nat
  deriving Repr

def batch (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) : Batch :=
  let found:=collect forward backward n cap nodes events
  let unique:=RunDedup.run n found.1
  ⟨unique.runs,found.2+unique.work+4⟩

theorem batch_nodup (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) :
    (batch forward backward n cap nodes events).runs.Nodup := RunDedup.run_nodup _ _

theorem batch_mem (forward backward : RankIndex.Index) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event)
    (hb : ∀e,e∈events.toList→∀R,(probe forward backward n cap nodes e).1=some R→RunDedup.Bounded n R)
    (R : Bounds) : R∈(batch forward backward n cap nodes events).runs ↔
      ∃e,e∈events.toList ∧ (probe forward backward n cap nodes e).1=some R := by
  rw [batch,RunDedup.run_mem]
  · exact collect_mem _ _ _ _ _ _ R
  · intro R hr
    obtain ⟨e,he,hr⟩:=(collect_mem _ _ _ _ _ _ R).mp hr
    exact hb e he R hr

theorem batch_work (f : Nat→Fin σ) (n cap : Nat)
    (nodes : Array (Record h)) (events : Array Event) :
    (batch (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) n cap nodes events).work≤
      events.size*(probeBudget h n+26*((n+1).log2+1)+10)+5 := by
  have hc:=collect_work f n cap nodes events
  have hd:=RunDedup.run_work n
    (collect (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) n cap nodes events).1
  have hl:=Nat.mul_le_mul_left (26*((n+1).log2+1)+5)
    (collect_length (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n) n cap nodes events)
  simp only [batch,Nat.mul_add,Nat.add_mul,Nat.mul_comm] at hc hd hl ⊢
  omega

end REWB.MaskedOrdered.Owner
