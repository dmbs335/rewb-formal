import REWB.PeriodicActualJoinCross

/-! Executed recursive join partition. Text splitting, filtering,
coordinate translation, length reads and the dyadic power are charged.
The measured frame is exactly the frame consumed by CountedJoin.solve. -/
namespace REWB.PeriodicActual.Join
open REWB.PeriodicConstruction REWB.TimedJoin
variable {α : Type}

def power : Nat→Result Nat
  | 0=>(1,1)
  | n+1=>let ⟨v,w⟩:=power n; (v*2,w+2)

theorem power_value (n : Nat) : (power n).1=2^n := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [power,ih,Nat.pow_succ]

theorem power_work (n : Nat) : (power n).2=2*n+1 := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [power,ih,Nat.mul_succ]

def splitWord : Nat→Word α→Result (Word α×Word α)
  | 0,w=>(([],w),1)
  | _+1,[]=>(([],[]),1)
  | k+1,c::cs=>let ⟨⟨left,right⟩,work⟩:=splitWord k cs; ((c::left,right),work+4)

theorem splitWord_value (k : Nat) (w : Word α) :
    (splitWord k w).1=(w.take k,w.drop k) := by
  induction k generalizing w with
  | zero=>rfl
  | succ k ih=>cases w <;> simp only [splitWord,ih,List.take_succ_cons,List.drop_succ_cons,
      List.take_nil,List.drop_nil]

theorem splitWord_work (k : Nat) (w : Word α) : (splitWord k w).2≤4*w.length+1 := by
  induction k generalizing w with
  | zero=>simp only [splitWord]; omega
  | succ k ih=>
    cases w with
    | nil=>simp only [splitWord,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.le_refl]
    | cons c cs=>
      have h:=ih cs
      simp only [splitWord,List.length_cons,Nat.mul_succ]
      omega

def shifted (c : Nat) (es : List TimedEntry) : Result (List TimedEntry) :=
  CountedProjection.map (fun e=>(OfflineJoin.shift c e,3)) es

theorem shifted_value (c : Nat) (es : List TimedEntry) :
    (shifted c es).1=OfflineJoin.shiftAll c es := by
  simp only [shifted,CountedProjection.map_value,OfflineJoin.shiftAll]

theorem shifted_work (c : Nat) (es : List TimedEntry) :
    (shifted c es).2=4*es.length+1 := by
  simp only [shifted,CountedProjection.map_plain_steps,Nat.reduceAdd,Nat.mul_comm]

structure Frame (α : Type) where
  left : Word α
  right : Word α
  sourceLeft : List TimedEntry
  targetLeft : List TimedEntry
  sourceRight : List TimedEntry
  targetRight : List TimedEntry
  crossTargets : List TimedEntry

def frame (h : Nat) (w : Word α) (es fs : List TimedEntry) : Result (Frame α) :=
  let ⟨width,pwork⟩:=power h
  let ⟨⟨left,right⟩,splitWork⟩:=splitWord width w
  let c:=left.length
  let el:=CountedJoin.filter (fun e : TimedEntry=>decide (e.pos<c)) es
  let er:=CountedJoin.filter (fun e : TimedEntry=>decide (c≤e.pos)) es
  let fl:=CountedJoin.filter (fun e : TimedEntry=>decide (e.pos<c)) fs
  let fr:=CountedJoin.filter (fun e : TimedEntry=>decide (c≤e.pos)) fs
  let ers:=shifted c er.1
  let frs:=shifted c fr.1
  (⟨left,right,el.1,fl.1,ers.1,frs.1,fr.1⟩,
    pwork+splitWork+3*(el.2+er.2+fl.2+fr.2)+ers.2+frs.2+
      3*(w.length+es.length+fs.length)+c+40)

theorem frame_value (h : Nat) (w : Word α) (es fs : List TimedEntry) :
    (frame h w es fs).1=
      let l:=w.take (2^h)
      let r:=w.drop (2^h)
      let c:=l.length
      ⟨l,r,before c es,before c fs,OfflineJoin.shiftAll c (after c es),
        OfflineJoin.shiftAll c (after c fs),after c fs⟩ := by
  simp only [frame,power_value,splitWord_value,CountedJoin.filter_value,shifted_value,before,after]

theorem frame_work (h : Nat) (w : Word α) (es fs : List TimedEntry) :
    (frame h w es fs).2≤100*(es.length+fs.length+w.length+h+2) := by
  have hs:=splitWord_work (power h).1 w
  have he:=List.length_filter_le (fun e : TimedEntry=>decide ((w.take (2^h)).length≤e.pos)) es
  have hf:=List.length_filter_le (fun e : TimedEntry=>decide ((w.take (2^h)).length≤e.pos)) fs
  have hl : (w.take (2^h)).length≤w.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  unfold frame
  simp only [power_work,power_value,splitWord_value,CountedJoin.filter_steps,CountedJoin.filter_value,
    shifted_work]
  rw [power_value] at hs
  simp only [Nat.mul_add,Nat.mul_succ,Nat.add_mul] at hs ⊢
  omega

theorem bounded_before (c : Nat) (es : List TimedEntry) (bound : Nat) (h : bounded es bound) :
    bounded (before c es) bound := fun e he=>h e (List.mem_filter.mp he).1

theorem bounded_after (c : Nat) (es : List TimedEntry) (bound : Nat) (h : bounded es bound) :
    bounded (after c es) bound := fun e he=>h e (List.mem_filter.mp he).1

theorem bounded_shift (c : Nat) (es : List TimedEntry) (bound : Nat) (h : bounded es bound) :
    bounded (OfflineJoin.shiftAll c es) bound := by
  intro e he
  obtain ⟨f,hf,rfl⟩:=List.mem_map.mp he
  exact h f hf

end REWB.PeriodicActual.Join
