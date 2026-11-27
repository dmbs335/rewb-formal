import REWB.MaskedOrderedMembership

/-! The constant-size edge repair determined by exact strict neighbors
agrees with the existing ordered-list insertion reference for fresh keys.
All lists in these proofs are specifications; the fast operation uses
only the cached-tree neighbor queries and these at-most-three records. -/
namespace REWB.MaskedOrdered
open Tree
open REWB.MaskedEventBudget (Edge)

def freshEdges (p : Nat) : Option Nat→Option Nat→List Edge
  | none,none => []
  | some a,none => [(a,p)]
  | none,some b => [(p,b)]
  | some a,some b => [(a,p),(p,b)]

def retiredEdges : Option Nat→Option Nat→List Edge
  | some a,some b => [(a,b)]
  | _,_ => []

theorem freshEdges_length (p : Nat) (a b : Option Nat) : (freshEdges p a b).length≤2 := by
  cases a <;> cases b <;> simp [freshEdges]

theorem retiredEdges_length (a b : Option Nat) : (retiredEdges a b).length≤1 := by
  cases a <;> cases b <;> simp [retiredEdges]

theorem pred_unique (xs : List Nat) (p : Nat) (a b : Option Nat)
    (ha : PredSpec xs p a) (hb : PredSpec xs p b) : a=b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hh:=ha b hb.1
      have hl:=hb.2.1
      omega
  | some a =>
    cases b with
    | none =>
      have hh:=hb a ha.1
      have hl:=ha.2.1
      omega
    | some b =>
      have hab:=hb.2.2 a ha.1 ha.2.1
      have hba:=ha.2.2 b hb.1 hb.2.1
      exact congrArg some (by omega : a=b)

theorem succ_unique (xs : List Nat) (p : Nat) (a b : Option Nat)
    (ha : SuccSpec xs p a) (hb : SuccSpec xs p b) : a=b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hh:=ha b hb.1
      have hl:=hb.2.1
      omega
  | some a =>
    cases b with
    | none =>
      have hh:=hb a ha.1
      have hl:=ha.2.1
      omega
    | some b =>
      have hab:=ha.2.2 b hb.1 hb.2.1
      have hba:=hb.2.2 a ha.1 ha.2.1
      exact congrArg some (by omega : a=b)

theorem strict_ext (xs ys : List Nat) (hx : xs.Pairwise (·<·)) (hy : ys.Pairwise (·<·))
    (hm : ∀p,p∈xs ↔ p∈ys) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have hh:=(hm y).mpr (by simp)
      simp at hh
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hh:=(hm x).mp (by simp)
      simp at hh
    | cons y ys =>
      have hxmin:=head_spec (x::xs) hx
      have hymin:=head_spec (y::ys) hy
      have hxy:=hxmin.2 y ((hm y).mpr (by simp))
      have hyx:=hymin.2 x ((hm x).mp (by simp))
      have he : x=y := by omega
      subst y
      have hx' : x∉xs := fun hh=>Nat.lt_irrefl x ((List.pairwise_cons.mp hx).1 x hh)
      have hy' : x∉ys := fun hh=>Nat.lt_irrefl x ((List.pairwise_cons.mp hy).1 x hh)
      have htail : xs=ys := by
        apply ih ys (List.pairwise_cons.mp hx).2 (List.pairwise_cons.mp hy).2
        intro p
        by_cases hp : p=x
        · simp only [hp,hx',hy']
        · simpa only [List.mem_cons,hp,false_or] using hm p
      rw [htail]

theorem reference_strict (p : Nat) (xs : List Nat) (hs : xs.Pairwise (·<·)) (hp : p∉xs) :
    (MaskedEventBudget.insert p xs).positions.Pairwise (·<·) := by
  have hle:=MaskedEventBudget.insert_ordered p xs (hs.imp (fun h=>Nat.le_of_lt h))
  have hnd : xs.Nodup := hs.imp (fun h=>Nat.ne_of_lt h)
  have hn:=(MaskedEventBudget.insert_perm p xs).symm.nodup (List.nodup_cons.mpr ⟨hp,hnd⟩)
  exact (hle.and hn).imp (fun h=>by omega)

theorem tree_insert_reference {h : Nat} (t : Tree h) (capacity p : Nat)
    (_hg : Good t) (hf : Fits t 0) (hb : capacity=2^h) (hp : p<2^h) (hnew : p∉t.entries) :
    (Tree.insert t capacity p).1.entries=(MaskedEventBudget.insert p t.entries).positions := by
  apply strict_ext _ _ (ordered _ 0 (insert_fits t capacity p hf hb hp))
    (reference_strict p _ (ordered t 0 hf) hnew)
  intro x
  rw [Tree.insert_mem t capacity p x hf hb hp,MaskedEventBudget.insert_mem]

theorem tree_insert_new_count {h : Nat} (t : Tree h) (capacity p : Nat)
    (hg : Good t) (hf : Fits t 0) (hb : capacity=2^h) (hp : p<2^h) (hnew : p∉t.entries) :
    (Tree.insert t capacity p).1.count=t.count+1 := by
  rw [count_correct _ (insert_good t capacity p hg),tree_insert_reference t capacity p hg hf hb hp hnew,
    MaskedEventBudget.insert_length, count_correct t hg]

theorem reference_edges (p : Nat) (xs : List Nat) (a b : Option Nat)
    (hs : xs.Pairwise (·<·)) (hp : p∉xs) (ha : PredSpec xs p a) (hb : SuccSpec xs p b) :
    (MaskedEventBudget.insert p xs).fresh=freshEdges p a b ∧
      (MaskedEventBudget.insert p xs).retired=retiredEdges a b := by
  induction xs with
  | nil =>
    have heA:=pred_unique [] p a none ha (by simp [PredSpec])
    have heB:=succ_unique [] p b none hb (by simp [SuccSpec])
    rw [heA,heB]
    exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    have hpx : p≠x := by intro he; exact hp (by simp [he])
    have hxs:=head_spec (x::xs) hs
    have htail:=(List.pairwise_cons.mp hs).2
    by_cases hfront : p≤x
    · have hpred : PredSpec (x::xs) p none := by
        intro r hr
        have hh:=hxs.2 r hr
        omega
      have hsucc : SuccSpec (x::xs) p (some x) :=
        ⟨by simp,by omega,fun r hr _=>hxs.2 r hr⟩
      have heA:=pred_unique _ p a none ha hpred
      have heB:=succ_unique _ p b (some x) hb hsucc
      rw [heA,heB]
      cases xs <;> simp [MaskedEventBudget.insert,hfront,freshEdges,retiredEdges]
    · have hxp : x<p := by omega
      cases xs with
      | nil =>
        have hpred : PredSpec [x] p (some x) :=
          ⟨by simp,hxp,fun r hr _=>by have he:=List.mem_singleton.mp hr; omega⟩
        have hsucc : SuccSpec [x] p none := by
          intro r hr
          simp only [List.mem_singleton] at hr
          omega
        have heA:=pred_unique _ p a (some x) ha hpred
        have heB:=succ_unique _ p b none hb hsucc
        rw [heA,heB]
        simp [MaskedEventBudget.insert,hfront,freshEdges,retiredEdges]
      | cons y ys =>
        have hxy : x<y := (List.pairwise_cons.mp hs).1 y (by simp)
        have hpy : p≠y := by intro he; exact hp (by simp [he])
        have hymin:=head_spec (y::ys) htail
        by_cases hmiddle : p≤y
        · have hpred : PredSpec (x::y::ys) p (some x) := by
            refine ⟨by simp,hxp,?_⟩
            intro r hr hrp
            rcases List.mem_cons.mp hr with he|hr
            · omega
            · have hh:=hymin.2 r hr
              omega
          have hsucc : SuccSpec (x::y::ys) p (some y) := by
            refine ⟨by simp,by omega,?_⟩
            intro r hr hpr
            rcases List.mem_cons.mp hr with he|hr
            · omega
            · exact hymin.2 r hr
          have heA:=pred_unique _ p a (some x) ha hpred
          have heB:=succ_unique _ p b (some y) hb hsucc
          rw [heA,heB]
          simp [MaskedEventBudget.insert,hfront,hmiddle,freshEdges,retiredEdges]
        · have hyp : y<p := by omega
          have hpred : PredSpec (y::ys) p a := by
            cases a with
            | none =>
              have hh:=ha y (by simp)
              omega
            | some q =>
              refine ⟨?_,ha.2.1,fun r hr hrp=>ha.2.2 r (List.mem_cons_of_mem _ hr) hrp⟩
              rcases List.mem_cons.mp ha.1 with he|hr
              · have hh:=ha.2.2 y (by simp) hyp
                omega
              · exact hr
          have hsucc : SuccSpec (y::ys) p b := by
            cases b with
            | none => exact fun r hr=>hb r (List.mem_cons_of_mem _ hr)
            | some q =>
              refine ⟨?_,hb.2.1,fun r hr hpr=>hb.2.2 r (List.mem_cons_of_mem _ hr) hpr⟩
              rcases List.mem_cons.mp hb.1 with he|hr
              · have hh:=hb.2.1
                omega
              · exact hr
          have hpn : p∉y::ys := fun h=>hp (List.mem_cons_of_mem _ h)
          have hh:=ih htail hpn hpred hsucc
          simpa only [MaskedEventBudget.insert,hfront,hmiddle,if_false] using hh

end REWB.MaskedOrdered
