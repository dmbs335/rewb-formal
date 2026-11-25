import REWB.BoundaryRangeFarIndexRegression

open REWB REWB.BoundaryRange REWB.BoundaryRange.Regression

def binary (n code : Nat) : Word (Fin 2) :=
  (List.range n).map (fun i=>(⟨(code/2^i)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2))

def accepts (d : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := d.final (d.run d.initial w)

def brute (A B C K D E : DFA (Fin 2)) (w : Word (Fin 2)) (left g right : Nat) : Bool := Id.run do
  for a in [0:g+1] do
    for p in [g:right+1] do
      if accepts C (Spec.slice w a p) && accepts K (Spec.slice w left p) then
        for j in [p:right+1] do
          if accepts D (Spec.slice w p j) then
            for L in [0:min a (right-j)+1] do
              if (Spec.slice w (a-L) a==Spec.slice w j (j+L)) &&
                accepts A (Spec.slice w 0 (a-L)) && accepts B (Spec.slice w (a-L) a) &&
                accepts E (Spec.slice w (j+L) right) then return true
  return false

def main : IO Unit := do
  let begin ← IO.monoMsNow
  let patterns : List (DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)) :=
    [(all,all,all,all,all,all),(all,all,all,reset,all,reset),
      (all,all,reset,all,all,all),(all,all,all,all,reset,all),
      (reset,reset,all,all,all,reset)]
  let mut builds:=0
  let mut queries:=0
  let mut accepted:=0
  let mut maxQuery:=0
  for (A,B,C,K,D,E) in patterns do
    for n in [0:3] do
      for code in [0:2^n] do
        let w:=binary n code
        for g in List.ofFn (fun g : Fin (w.length+1)=>g) do
          let hg : g.val≤w.length:=by have hh:=g.isLt; omega
          let idx:=FarLeft.build A B C K D E w 0 g.val hg
          unless idx.work≤FarLeft.buildBudget A B C K D E n do
            throw (IO.userError s!"far-left build bound failed n={n}")
          builds:=builds+1
          for left in [0:g.val+1] do
            for right in [0:n+1] do
              let answer:=FarLeft.query K E idx left right
              let want:=brute A B C K D E w left g right
              unless answer.1==want do
                throw (IO.userError s!"far-left mismatch n={n}, code={code}, left={left}, g={g.val}, right={right}")
              unless answer.2≤FarLeft.queryBudget C K E n do
                throw (IO.userError "far-left query bound failed")
              queries:=queries+1
              if answer.1 then accepted:=accepted+1
              maxQuery:=max maxQuery answer.2
          unless !(FarLeft.query K E idx (g.val+1) n).1 && !(FarLeft.query K E idx 0 (n+1)).1 do
            throw (IO.userError "far-left outside-query guard failed")
  let finish ← IO.monoMsNow
  IO.println s!"far-left eager variant tables: builds={builds}, queries={queries}, accepted={accepted}, maxQueryWork={maxQuery}, mismatches=0 ({finish-begin} ms)"
  let w : Word (Fin 2):=List.replicate 128 0
  have hw : w.length=128:=List.length_replicate
  let idx:=FarLeft.build all all all all all all w 0 64 (by rw [hw]; decide)
  for left in [0:65] do
    for right in [0:129] do
      let answer:=FarLeft.query all all idx left right
      unless answer.1==decide (64≤right) do
        throw (IO.userError "deep far-left endpoint mismatch")
  IO.println s!"far-left n=128, stored K rows={idx.rows.cells.size}, buildWork={idx.work}, queries=8385, queryWork={(FarLeft.query all all idx 64 128).2}; factory used only in preparation"
