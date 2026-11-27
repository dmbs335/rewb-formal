import REWB.ShortOuterP2Sound
import REWB.ShortOuterJoinCost

/-! Closed concrete P2 short-outer solver.  Each outer start runs its
actual D join on a word of width b=min(L,n+1), while all rows and exact
keys are shared.  Every block, even a rejected prefix, is measured. -/
namespace REWB.ShortOuter.P2
open REWB.Periodic
variable {σ : Nat}

def block (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (idx : Prepared P) (p : Nat) : Bool×Nat :=
  if prefixOK P idx p then
    let word:=segment (ArrayText.read text fallback) p idx.band.keys.width
    let es:=sources P idx p
    let fs:=targets P idx p
    let out:=Join.run P.D word es.1 fs.1
    (out.value,es.2+fs.2+out.work+3*idx.band.keys.width+8)
  else (false,5)

theorem block_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p : Nat) (hp : p≤text.size) :
    (block P text fallback (prepare P text fallback limit) p).1=true ↔ At P text fallback limit p := by
  rw [←match_iff P text fallback limit p hp]
  by_cases ha : prefixOK P (prepare P text fallback limit) p=true
  · simp only [block,if_pos ha,ha,true_and]
    exact Join.run_correct P.D _ _ _ (sources_plain P _ p) (targets_plain P _ p)
      (by simpa only [segment_length] using sources_bounded P (prepare P text fallback limit) p)
      (by simpa only [segment_length] using targets_bounded P (prepare P text fallback limit) p)
  · simp only [block,if_neg ha,ha,false_and,Bool.false_eq_true,if_false]

def sourceBudget (b : Nat) : Nat := b*(b*34+4+b+4)+4
def targetBudget (b : Nat) : Nat := b*(b*37+4+b+4)+4

def blockBudget (P : SevenDFA (Fin σ)) (b : Nat) : Nat :=
  sourceBudget b+targetBudget b+Join.ceiling P.D.stateCount b (b*b) (b*b)+3*b+8

theorem block_work (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (idx : Prepared P) (p : Nat) : (block P text fallback idx p).2≤blockBudget P idx.band.keys.width := by
  by_cases ha : prefixOK P idx p=true
  · have hs:=sources_work P idx p
    have ht:=targets_work P idx p
    have hj:=Join.run_work_max P.D (segment (ArrayText.read text fallback) p idx.band.keys.width)
      (sources P idx p).1 (targets P idx p).1 (sources_plain P idx p) (targets_plain P idx p)
      (idx.band.keys.width*idx.band.keys.width) (idx.band.keys.width*idx.band.keys.width)
      (sources_length P idx p) (targets_length P idx p)
    rw [segment_length] at hj
    simp only [block,if_pos ha]
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add hs ht) hj) (3*idx.band.keys.width)) 8
  · simp only [block,if_neg ha,blockBudget]
    omega

structure Result where
  answer : Bool
  work : Nat
  deriving Repr

def solve (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) : Result :=
  let idx:=prepare P text fallback limit
  let ps:=CountedProjection.range (text.size+1)
  let rows:=CountedProjection.map (block P text fallback idx) ps.1
  ⟨rows.1.any id,idx.work+ps.2+rows.2+2*rows.1.length+5⟩

theorem solve_value (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (solve P text fallback limit).answer=true ↔
      ∃p,p≤text.size ∧ (block P text fallback (prepare P text fallback limit) p).1=true := by
  simp only [solve,CountedProjection.map_value,CountedProjection.range_value,List.any_map,
    List.any_eq_true,List.mem_range,Nat.lt_succ_iff,Function.comp_apply,id_eq]

theorem solve_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (solve P text fallback limit).answer=true ↔
      ResidualDispatch.ShortP2 P (ArrayText.read text fallback) text.size limit := by
  rw [solve_value]
  constructor
  · rintro ⟨p,hp,ha⟩
    obtain ⟨x,_,hx,hs⟩:=(block_correct P text fallback limit p hp).mp ha
    exact ⟨x,hx,hs⟩
  · rintro ⟨x,hx,hs⟩
    have hp : x.p≤text.size := by
      obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,_⟩:=hx
      omega
    exact ⟨x.p,hp,(block_correct P text fallback limit x.p hp).mpr ⟨x,rfl,hx,hs⟩⟩

def budget (P : SevenDFA (Fin σ)) (n limit : Nat) : Nat :=
  prepareBudget P n limit+(n+1)*(blockBudget P (min limit (n+1))+5)+7

theorem solve_work (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    (solve P text fallback limit).work≤budget P text.size limit := by
  let idx:=prepare P text fallback limit
  have hp:=prepare_work P text fallback limit
  have hm:=Collect.map_work (block P text fallback idx) (CountedProjection.range (text.size+1)).1
    (blockBudget P (min limit (text.size+1))) (by intro p _; exact block_work P text fallback idx p)
  have hlen : (CountedProjection.range (text.size+1)).1.length=text.size+1 := by
    rw [CountedProjection.range_value,List.length_range]
  rw [hlen] at hm
  have hr : (CountedProjection.range (text.size+1)).2=2*(text.size+1)+1 :=
    CountedProjection.rangeFrom_steps 0 _
  change idx.work+(CountedProjection.range (text.size+1)).2+
    (CountedProjection.map (block P text fallback idx) _).2+
    2*(CountedProjection.map (block P text fallback idx) _).1.length+5≤_
  rw [hr,CountedProjection.map_value,List.length_map,hlen]
  change idx.work≤prepareBudget P text.size limit at hp
  simp only [budget,Nat.mul_add,Nat.mul_one] at hm ⊢
  omega

theorem solve_sound (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat)
    (ha : (solve P text fallback limit).answer=true) : MatchesWithin P.nested2 text.toList 2 := by
  have h:=ResidualDispatch.short_p2_sound P (ArrayText.read text fallback) text.size limit
    ((solve_correct P text fallback limit).mp ha)
  rwa [full_read] at h

theorem solve_zero_limit (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (solve P text fallback 0).answer=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨x,_,hs⟩:=(solve_correct P text fallback 0).mp h
  omega

end REWB.ShortOuter.P2
