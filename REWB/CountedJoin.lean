import REWB.CountedSort
import REWB.OfflineJoin

/-! The actual offline join with measured filtering and stable sorting.
    The existing semantic result and scan/event/text counters are retained
    exactly. The additional sorting counter bounds all data-dependent list
    traversals of sorting, not merely the interval scan after sorting.
    Formula-to-window conversion and cut-vector construction are separate. -/
namespace REWB.CountedJoin
open REWB.ExponentIntervals REWB.TimedJoin
variable {α : Type}

theorem log2_mono {m n : Nat} (h : m≤n) : m.log2≤n.log2 := by
  by_cases hm : m=0
  · simp [hm]
  · have hn : n≠0 := by omega
    exact (Nat.le_log2 hn).mpr (Nat.le_trans (Nat.log2_self_le hm) h)

def filter (p : α→Bool) : List α→List α×Nat
  | [] => ([],0)
  | x::xs =>
    let r:=filter p xs
    (if p x then x::r.1 else r.1,r.2+2)

theorem filter_value (p : α→Bool) (xs : List α) : (filter p xs).1=xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [filter,List.filter_cons,ih]

theorem filter_steps (p : α→Bool) (xs : List α) : (filter p xs).2=2*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [filter,ih,List.length_cons,Nat.mul_add,Nat.mul_one]

def filterTR.go (p : α→Bool) : List α→List α→Nat→List α×Nat
  | [],acc,c => (acc.reverse,c)
  | x::xs,acc,c => go p xs (if p x then x::acc else acc) (c+2)

theorem filterTR.go_eq (p : α→Bool) (xs acc : List α) (c : Nat) :
    go p xs acc c=(acc.reverse++(filter p xs).1,c+(filter p xs).2) := by
  induction xs generalizing acc c with
  | nil => simp [go,filter]
  | cons x xs ih =>
    simp only [go,filter]
    split <;> rw [ih]
    · simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1
      omega
    · congr 1
      omega

def filterTR (p : α→Bool) (xs : List α) : List α×Nat := filterTR.go p xs [] 0

@[csimp] theorem filter_eq_filterTR : @filter=@filterTR := by
  funext α p xs
  simp only [filterTR,filterTR.go_eq,List.reverse_nil,List.nil_append,Nat.zero_add]

def prepare (xs : List Window) : List Window×Nat :=
  let a:=filter (fun I=>decide (I.lo≤I.hi)) xs
  let b:=CountedSort.sort IntervalSweep.ordered a.1
  (b.1,a.2+b.2)

theorem prepare_value (xs : List Window) : (prepare xs).1=IntervalSweep.prepare xs := by
  simp only [prepare,CountedSort.sort_value,filter_value,IntervalSweep.prepare]

theorem prepare_steps_bound (xs : List Window) (B : Nat) (hB : xs.length≤B) :
    (prepare xs).2≤10*xs.length*(B.log2+1) := by
  let p:=fun I : Window=>decide (I.lo≤I.hi)
  have hs:=CountedSort.sort_steps IntervalSweep.ordered (filter p xs).1
  rw [filter_value] at hs
  have hn : (xs.filter p).length≤xs.length := List.length_filter_le _ _
  have hl:=log2_mono (Nat.le_trans hn hB)
  have hh:=Nat.mul_le_mul (Nat.mul_le_mul_left 8 hn) (Nat.add_le_add_right hl 1)
  have hm:=Nat.mul_le_mul_left xs.length (show 1≤B.log2+1 by omega)
  simp only [Nat.mul_one] at hm
  change (filter p xs).2+(CountedSort.sort IntervalSweep.ordered (filter p xs).1).2≤_
  rw [filter_steps,filter_value]
  have he : 10*xs.length*(B.log2+1)=
      8*xs.length*(B.log2+1)+2*(xs.length*(B.log2+1)) := by
    rw [← Nat.mul_assoc,← Nat.add_mul,← Nat.add_mul]
  rw [he]
  omega

theorem prepare_steps (xs : List Window) :
    (prepare xs).2≤10*xs.length*(xs.length.log2+1) :=
  prepare_steps_bound xs xs.length (Nat.le_refl _)

structure BatchResult where
  value : Bool×Nat
  sortSteps : Nat
  deriving Repr

def batch (xs ys : List Window) : BatchResult :=
  let a:=prepare xs
  let b:=prepare ys
  ⟨IntervalSweep.scan (a.1.length+b.1.length) a.1 b.1,a.2+b.2⟩

theorem batch_value (xs ys : List Window) : (batch xs ys).value=IntervalSweep.batch xs ys := by
  simp only [batch,prepare_value,IntervalSweep.batch]

theorem batch_steps_bound (xs ys : List Window) (B : Nat) (hB : xs.length+ys.length≤B) :
    (batch xs ys).sortSteps≤10*(xs.length+ys.length)*(B.log2+1) := by
  have h:=Nat.add_le_add (prepare_steps_bound xs B (by omega)) (prepare_steps_bound ys B (by omega))
  change (prepare xs).2+(prepare ys).2≤_
  calc
    _ ≤ 10*xs.length*(B.log2+1)+10*ys.length*(B.log2+1) := h
    _ = _ := by rw [← Nat.add_mul,← Nat.mul_add]

def keyed (K N : Nat) (es fs : List KeyedJoin.Entry) : BatchResult :=
  batch (KeyedJoin.prepare K N es) (KeyedJoin.prepare K N fs)

theorem keyed_value (K N : Nat) (es fs : List KeyedJoin.Entry) :
    (keyed K N es fs).value=KeyedJoin.batch K N es fs := batch_value _ _

theorem keyed_steps_bound (K N : Nat) (es fs : List KeyedJoin.Entry) (B : Nat)
    (hB : K*(KeyedJoin.weight es+KeyedJoin.weight fs)≤B) :
    (keyed K N es fs).sortSteps≤10*(K*(KeyedJoin.weight es+KeyedJoin.weight fs))*(B.log2+1) := by
  have h:=batch_steps_bound (KeyedJoin.prepare K N es) (KeyedJoin.prepare K N fs) B
    (by simpa only [KeyedJoin.prepare_length,← Nat.mul_add] using hB)
  simpa only [keyed,KeyedJoin.prepare_length,← Nat.mul_add] using h

def cross (d : DFA α) (left right : Word α) (K N : Nat) (es fs : List TimedEntry) : BatchResult :=
  let I:=DFACut.build d left right
  keyed K N (sources d I es) (targets d I fs)

theorem cross_value (d : DFA α) (left right : Word α) (K N : Nat) (es fs : List TimedEntry) :
    (cross d left right K N es fs).value=TimedJoin.cross d left right K N es fs := keyed_value _ _ _ _

def weight (d : DFA α) (K : Nat) (es fs : List TimedEntry) : Nat :=
  K*(TimedJoin.weight es+d.stateCount*TimedJoin.weight fs)

theorem cross_steps_bound (d : DFA α) (left right : Word α) (K N : Nat)
    (es fs : List TimedEntry) (B : Nat) (hB : weight d K es fs≤B) :
    (cross d left right K N es fs).sortSteps≤10*weight d K es fs*(B.log2+1) := by
  let I:=DFACut.build d left right
  have hw : K*(KeyedJoin.weight (sources d I es)+KeyedJoin.weight (targets d I fs))≤weight d K es fs := by
    rw [sources_weight]
    exact Nat.mul_le_mul_left K (Nat.add_le_add_left (targets_weight d I fs) _)
  have h:=keyed_steps_bound K N (sources d I es) (targets d I fs) B (Nat.le_trans hw hB)
  exact Nat.le_trans h (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10 hw))

structure Result where
  value : OfflineJoin.Result
  sortSteps : Nat
  deriving Repr

def solve (d : DFA α) (K N : Nat) : Nat→Word α→List TimedEntry→List TimedEntry→Result
  | 0,w,es,fs =>
    let z:=cross d [] w K N es fs
    ⟨⟨z.value.1,z.value.2,es.length+fs.length,w.length,1⟩,z.sortSteps⟩
  | h+1,w,es,fs =>
    let l:=w.take (2^h)
    let r:=w.drop (2^h)
    let c:=l.length
    let esL:=before c es
    let esR:=after c es
    let fsL:=before c fs
    let fsR:=after c fs
    let a:=solve d K N h l esL fsL
    let b:=solve d K N h r (OfflineJoin.shiftAll c esR) (OfflineJoin.shiftAll c fsR)
    let z:=cross d l r K N esL fsR
    ⟨⟨a.value.answer || b.value.answer || z.value.1,a.value.tests+b.value.tests+z.value.2,
      es.length+fs.length+a.value.eventVisits+b.value.eventVisits,
      w.length+a.value.textVisits+b.value.textVisits,
      1+a.value.nodes+b.value.nodes⟩,
      a.sortSteps+b.sortSteps+z.sortSteps⟩

theorem solve_value (d : DFA α) (K N h : Nat) (w : Word α) (es fs : List TimedEntry) :
    (solve d K N h w es fs).value=OfflineJoin.solve d K N h w es fs := by
  induction h generalizing w es fs with
  | zero => simp only [solve,cross_value,OfflineJoin.solve]
  | succ h ih => simp only [solve,ih,cross_value,OfflineJoin.solve]

theorem split_weight (d : DFA α) (K c : Nat) (es fs : List TimedEntry) :
    weight d K (before c es) (before c fs)+weight d K (after c es) (after c fs)=weight d K es fs := by
  unfold weight
  rw [← Nat.mul_add]
  have he:=OfflineJoin.split_weight c es
  have hf:=OfflineJoin.split_weight c fs
  have hh : TimedJoin.weight (before c es)+d.stateCount*TimedJoin.weight (before c fs)+
      (TimedJoin.weight (after c es)+d.stateCount*TimedJoin.weight (after c fs))=
      TimedJoin.weight es+d.stateCount*TimedJoin.weight fs := by
    rw [← he,← hf,Nat.mul_add]
    omega
  rw [hh]

theorem shift_weight (d : DFA α) (K c : Nat) (es fs : List TimedEntry) :
    weight d K (OfflineJoin.shiftAll c es) (OfflineJoin.shiftAll c fs)=weight d K es fs := by
  simp only [weight,OfflineJoin.shift_weight]

theorem cross_weight (d : DFA α) (K c : Nat) (es fs : List TimedEntry) :
    weight d K (before c es) (after c fs)≤weight d K es fs := by
  have he:=OfflineJoin.split_weight c es
  have hf:=OfflineJoin.split_weight c fs
  exact Nat.mul_le_mul_left K (Nat.add_le_add (by omega) (Nat.mul_le_mul_left d.stateCount (by omega)))

theorem solve_steps_bound (d : DFA α) (K N h : Nat) (w : Word α)
    (es fs : List TimedEntry) (B : Nat) (hB : weight d K es fs≤B) :
    (solve d K N h w es fs).sortSteps≤(h+1)*(10*weight d K es fs*(B.log2+1)) := by
  induction h generalizing w es fs with
  | zero =>
    simpa only [solve,Nat.zero_add,Nat.one_mul] using cross_steps_bound d [] w K N es fs B hB
  | succ h ih =>
    let l:=w.take (2^h)
    let r:=w.drop (2^h)
    let c:=l.length
    let el:=before c es
    let er:=after c es
    let fl:=before c fs
    let fr:=after c fs
    have hw : weight d K el fl+weight d K er fr=weight d K es fs := split_weight d K c es fs
    have hwr : weight d K (OfflineJoin.shiftAll c er) (OfflineJoin.shiftAll c fr)=weight d K er fr :=
      shift_weight d K c er fr
    have ha:=ih l el fl (by omega)
    have hb:=ih r (OfflineJoin.shiftAll c er) (OfflineJoin.shiftAll c fr) (by rw [hwr]; omega)
    rw [hwr] at hb
    have hz:=cross_steps_bound d l r K N el fr B
      (Nat.le_trans (cross_weight d K c es fs) hB)
    have hz': (cross d l r K N el fr).sortSteps≤10*weight d K es fs*(B.log2+1) :=
      Nat.le_trans hz (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10 (cross_weight d K c es fs)))
    have hsums : (h+1)*(10*weight d K el fl*(B.log2+1))+
        (h+1)*(10*weight d K er fr*(B.log2+1))=
        (h+1)*(10*weight d K es fs*(B.log2+1)) := by
      rw [← Nat.mul_add,← Nat.add_mul,← Nat.mul_add,hw]
    have hh:=Nat.add_le_add ha hb
    rw [hsums] at hh
    change (solve d K N h l el fl).sortSteps+
      (solve d K N h r (OfflineJoin.shiftAll c er) (OfflineJoin.shiftAll c fr)).sortSteps+
      (cross d l r K N el fr).sortSteps≤_
    rw [Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add hh hz'

theorem solve_steps (d : DFA α) (K N h : Nat) (w : Word α) (es fs : List TimedEntry) :
    (solve d K N h w es fs).sortSteps≤
      (h+1)*(10*weight d K es fs*((weight d K es fs).log2+1)) :=
  solve_steps_bound d K N h w es fs _ (Nat.le_refl _)

def run (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry) : Result :=
  solve d K N (DyadicIndex.heightFor w.length) w es fs

theorem run_value (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry) :
    (run d K N w es fs).value=OfflineJoin.run d K N w es fs := solve_value _ _ _ _ _ _ _

theorem run_steps (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry) :
    (run d K N w es fs).sortSteps≤
      (DyadicIndex.heightFor w.length+1)*(10*weight d K es fs*((weight d K es fs).log2+1)) :=
  solve_steps d K N _ w es fs

theorem run_steps_bound (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry)
    (B : Nat) (hB : weight d K es fs≤B) :
    (run d K N w es fs).sortSteps≤
      (DyadicIndex.heightFor w.length+1)*(10*weight d K es fs*(B.log2+1)) :=
  solve_steps_bound d K N _ w es fs B hB

theorem run_correct (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry)
    (hK : 0<K) (hs : Good K es) (ht : Good K fs)
    (he : ∀ e,e∈es→e.pos≤w.length) (hf : ∀ f,f∈fs→f.pos≤w.length) :
    (run d K N w es fs).value.answer=true ↔ Match d w N es fs := by
  rw [run_value]
  exact OfflineJoin.run_correct d K N w es fs hK hs ht he hf

end REWB.CountedJoin
