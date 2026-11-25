import REWB.ShortOuterP1Sound
import REWB.ShortOuterJoinCost

/-! Closed concrete P1 short-outer solver.  Preparation, all event/list
construction and the full executed plain-join ledger are included.
For b=min(L,n+1), its budget is O_P((n+1)(b+1)^2 polylog(n+1)). -/
namespace REWB.ShortOuter.P1
variable {σ : Nat}

structure Result where
  answer : Bool
  work : Nat
  deriving Repr

def solve (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) : Result :=
  let idx:=prepare P text fallback limit
  let es:=sources P idx
  let fs:=targets P idx
  let out:=Join.run P.C text.toList es.1 fs.1
  ⟨out.value,idx.work+es.2+fs.2+out.work+text.size+5⟩

theorem solve_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (solve P text fallback limit).answer=true ↔
      ResidualDispatch.ShortP1 P (ArrayText.read text fallback) text.size limit := by
  change (Join.run P.C text.toList (sources P (prepare P text fallback limit)).1
    (targets P (prepare P text fallback limit)).1).value=true ↔ _
  rw [Join.run_correct P.C text.toList _ _ (sources_plain P _) (targets_plain P _)
    (by simpa only [Array.length_toList] using sources_bounded P (prepare P text fallback limit))
    (by simpa only [Array.length_toList] using targets_bounded P (prepare P text fallback limit))]
  exact match_iff P text fallback limit

def sourceBudget (n b : Nat) : Nat := (n+1)*(b*18+4+b+4)+4
def targetBudget (n b : Nat) : Nat := (n+1)*(b*(b*45+4+b+4)+4+b*b+4)+4

def budget (P : SevenDFA (Fin σ)) (n limit : Nat) : Nat :=
  let b:=min limit (n+1)
  prepareBudget P n limit+sourceBudget n b+targetBudget n b+
    Join.ceiling P.C.stateCount n ((n+1)*b) ((n+1)*(b*b))+n+5

theorem solve_work (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (solve P text fallback limit).work≤budget P text.size limit := by
  let idx:=prepare P text fallback limit
  have hp:=prepare_work P text fallback limit
  have hs:=sources_work P idx
  have ht:=targets_work P idx
  have hj:=Join.run_work_max P.C text.toList (sources P idx).1 (targets P idx).1
    (sources_plain P idx) (targets_plain P idx)
    ((text.size+1)*min limit (text.size+1))
    ((text.size+1)*(min limit (text.size+1)*min limit (text.size+1)))
    (sources_length P idx) (targets_length P idx)
  change idx.work≤prepareBudget P text.size limit at hp
  change (sources P idx).2≤sourceBudget text.size (min limit (text.size+1)) at hs
  change (targets P idx).2≤targetBudget text.size (min limit (text.size+1)) at ht
  rw [Array.length_toList] at hj
  change idx.work+(sources P idx).2+(targets P idx).2+
    (Join.run P.C text.toList (sources P idx).1 (targets P idx).1).work+text.size+5≤_
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp hs) ht) hj) text.size) 5

theorem solve_sound (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat)
    (ha : (solve P text fallback limit).answer=true) : MatchesWithin P.nested1 text.toList 2 := by
  have h:=ResidualDispatch.short_p1_sound P (ArrayText.read text fallback) text.size limit
    ((solve_correct P text fallback limit).mp ha)
  rwa [full_read] at h

theorem solve_zero_limit (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (solve P text fallback 0).answer=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨v,hv⟩:=(solve_correct P text fallback 0).mp h
  omega

end REWB.ShortOuter.P1
