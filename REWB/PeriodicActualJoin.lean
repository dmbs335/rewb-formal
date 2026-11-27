import REWB.PeriodicActualJoinSplit

/-! Actual recursive chronological join with all cut/window/list
construction installed. Existing answers and four original counters are
preserved exactly. Additional work is charged to the actual event visits,
text visits and nodes of that same execution, with fixed formula bounds. -/
namespace REWB.PeriodicActual.Join
open REWB.PeriodicConstruction REWB.TimedJoin
variable {α : Type}

def solve (d : DFA α) (K N : Nat) : Nat→Word α→List TimedEntry→List TimedEntry→Result CountedJoin.Result
  | 0,w,es,fs=>
    let ⟨z,work⟩:=cross d [] w K N es fs
    (⟨⟨z.value.1,z.value.2,es.length+fs.length,w.length,1⟩,z.sortSteps⟩,
      work+3*(es.length+fs.length+w.length)+20)
  | h+1,w,es,fs=>
    let ⟨split,splitWork⟩:=frame h w es fs
    let ⟨a,awork⟩:=solve d K N h split.left split.sourceLeft split.targetLeft
    let ⟨b,bwork⟩:=solve d K N h split.right split.sourceRight split.targetRight
    let ⟨z,zwork⟩:=cross d split.left split.right K N split.sourceLeft split.crossTargets
    (⟨⟨a.value.answer || b.value.answer || z.value.1,a.value.tests+b.value.tests+z.value.2,
       es.length+fs.length+a.value.eventVisits+b.value.eventVisits,
       w.length+a.value.textVisits+b.value.textVisits,
       1+a.value.nodes+b.value.nodes⟩,a.sortSteps+b.sortSteps+z.sortSteps⟩,
      awork+bwork+zwork+splitWork+40)

theorem solve_value (d : DFA α) (K N h : Nat) (w : Word α) (es fs : List TimedEntry) :
    (solve d K N h w es fs).1=CountedJoin.solve d K N h w es fs := by
  induction h generalizing w es fs with
  | zero=>simp only [solve,cross_value,CountedJoin.solve]
  | succ h ih=>simp only [solve,frame_value,ih,cross_value,CountedJoin.solve]

def volume (h : Nat) (out : CountedJoin.Result) : Nat :=
  out.value.eventVisits+out.value.textVisits+(h+1)*out.value.nodes

def coefficient (states K bound : Nat) : Nat := crossCoefficient states K bound+140

theorem solve_work (d : DFA α) (K N h : Nat) (w : Word α) (es fs : List TimedEntry)
    (bound : Nat) (he : bounded es bound) (hf : bounded fs bound) :
    (solve d K N h w es fs).2≤
      coefficient d.stateCount K bound*volume h (CountedJoin.solve d K N h w es fs) := by
  induction h generalizing w es fs with
  | zero=>
    have hz:=cross_work d [] w K N es fs bound he hf
    simp only [List.length_nil,Nat.add_zero] at hz
    change (cross d [] w K N es fs).2+3*(es.length+fs.length+w.length)+20≤_
    simp only [CountedJoin.solve,volume,coefficient,Nat.zero_add,Nat.one_mul,Nat.add_mul]
    omega
  | succ h ih=>
    let l:=w.take (2^h)
    let r:=w.drop (2^h)
    let c:=l.length
    let el:=before c es
    let fl:=before c fs
    let er:=OfflineJoin.shiftAll c (after c es)
    let fr:=OfflineJoin.shiftAll c (after c fs)
    let a:=CountedJoin.solve d K N h l el fl
    let b:=CountedJoin.solve d K N h r er fr
    let localVolume:=es.length+fs.length+w.length+h+2
    let factor:=coefficient d.stateCount K bound
    have hel:=bounded_before c es bound he
    have hfl:=bounded_before c fs bound hf
    have her:=bounded_shift c (after c es) bound (bounded_after c es bound he)
    have hfr:=bounded_shift c (after c fs) bound (bounded_after c fs bound hf)
    have ha:=ih l el fl hel hfl
    have hb:=ih r er fr her hfr
    have hz:=cross_work d l r K N el (after c fs) bound hel (bounded_after c fs bound hf)
    have hlen : l.length+r.length=w.length := by
      dsimp only [l,r]
      rw [List.length_take,List.length_drop]
      omega
    have helen : el.length≤es.length := List.length_filter_le _ _
    have hflen : (after c fs).length≤fs.length := List.length_filter_le _ _
    have hvol : el.length+(after c fs).length+l.length+r.length+1≤localVolume := by
      dsimp only [localVolume]
      omega
    have hz':=Nat.le_trans hz (Nat.mul_le_mul_left _ hvol)
    have hframe:=frame_work h w es fs
    have hpositive : 2≤localVolume := by dsimp only [localVolume]; omega
    have hforty:=Nat.mul_le_mul_left 20 hpositive
    have hlocal : (cross d l r K N el (after c fs)).2+(frame h w es fs).2+40≤factor*localVolume := by
      change (frame h w es fs).2≤100*localVolume at hframe
      dsimp only [factor,coefficient]
      rw [Nat.add_mul]
      omega
    have hsum:=Nat.add_le_add (Nat.add_le_add ha hb) hlocal
    change _≤factor*volume h a+factor*volume h b+factor*localVolume at hsum
    rw [←Nat.mul_add,←Nat.mul_add] at hsum
    have hv : volume h a+volume h b+localVolume≤
        volume (h+1) (CountedJoin.solve d K N (h+1) w es fs) := by
      change a.value.eventVisits+a.value.textVisits+(h+1)*a.value.nodes+
        (b.value.eventVisits+b.value.textVisits+(h+1)*b.value.nodes)+localVolume≤
        (es.length+fs.length+a.value.eventVisits+b.value.eventVisits)+
          (w.length+a.value.textVisits+b.value.textVisits)+(h+1+1)*(1+a.value.nodes+b.value.nodes)
      dsimp only [localVolume]
      simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
      omega
    have hh:=Nat.le_trans hsum (Nat.mul_le_mul_left factor hv)
    rw [solve]
    simp only [frame_value]
    change (solve d K N h l el fl).2+(solve d K N h r er fr).2+
      (cross d l r K N el (after c fs)).2+(frame h w es fs).2+40≤_
    dsimp only [factor] at hh
    omega

def run (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry) : Result CountedJoin.Result :=
  let height:=DyadicIndex.heightFor w.length
  let ⟨out,work⟩:=solve d K N height w es fs
  (out,work+w.length+4*(height+1)+4)

theorem run_value (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry) :
    (run d K N w es fs).1=CountedJoin.run d K N w es fs := by
  simp only [run,solve_value,CountedJoin.run]

theorem run_work (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry)
    (bound : Nat) (he : bounded es bound) (hf : bounded fs bound) :
    (run d K N w es fs).2≤
      coefficient d.stateCount K bound*volume (DyadicIndex.heightFor w.length) (CountedJoin.run d K N w es fs)+
        w.length+4*(DyadicIndex.heightFor w.length+1)+4 := by
  simpa only [run,CountedJoin.run] using Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (solve_work d K N (DyadicIndex.heightFor w.length) w es fs bound he hf) w.length)
      (4*(DyadicIndex.heightFor w.length+1))) 4

end REWB.PeriodicActual.Join
