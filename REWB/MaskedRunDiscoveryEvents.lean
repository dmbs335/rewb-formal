import REWB.MaskedRunDiscoveryCoverage

/-! A pair's first binary coexistence creates a concrete adjacency
generation in the existing insertion trace. This statement makes no
least-period claim at that binary node: equal-depth refinements can be
incomplete. Discovery is justified only after the containing prefix
class has completed, using the separate completeness certificate. -/
namespace REWB.MaskedRunDiscovery
open REWB.MaskedEventBudget

theorem edge_members (xs : List Nat) (i j : Nat) (h : (i,j)∈edges xs) :
    i∈xs ∧ j∈xs := by
  induction xs with
  | nil => simp [edges] at h
  | cons x xs ih =>
    cases xs with
    | nil => simp [edges] at h
    | cons y ys =>
      simp only [edges,List.mem_cons] at h
      rcases h with he|ht
      · have hi:=congrArg Prod.fst he
        have hj:=congrArg Prod.snd he
        dsimp only at hi hj
        simp only [hi,hj,List.mem_cons,true_or,or_true]
        exact ⟨True.intro,True.intro⟩
      · have hh:=ih ht
        exact ⟨List.mem_cons_of_mem _ hh.1,List.mem_cons_of_mem _ hh.2⟩

theorem adjacent_edge (xs : List Nat) (i j : Nat)
    (hs : xs.Pairwise (·<·)) (ha : Adjacent xs i j) : (i,j)∈edges xs := by
  induction xs with
  | nil => have hh:=ha.1; simp at hh
  | cons x xs ih =>
    obtain ⟨hall,ht⟩:=List.pairwise_cons.mp hs
    have hij:=ha.2.2.1
    by_cases he : x=i
    · subst x
      have hj : j∈xs := (List.mem_cons.mp ha.2.1).resolve_left (by omega)
      cases xs with
      | nil => simp at hj
      | cons y ys =>
        have hy : i<y := hall y (by simp)
        rcases List.mem_cons.mp hj with hyj|hjy
        · subst j
          simp [edges]
        · have hyj : y<j := (List.pairwise_cons.mp ht).1 j hjy
          exact False.elim (ha.2.2.2 y (by simp) hy hyj)
    · have hi : i∈xs := (List.mem_cons.mp ha.1).resolve_left (by omega)
      have hxi:=hall i hi
      have hj : j∈xs := (List.mem_cons.mp ha.2.1).resolve_left (by omega)
      have htail : Adjacent xs i j :=
        ⟨hi,hj,hij,fun k hk hik hkj=>ha.2.2.2 k (List.mem_cons_of_mem _ hk) hik hkj⟩
      have hh:=ih ht htail
      cases xs with
      | nil => simp at hi
      | cons y ys => exact List.mem_cons_of_mem _ hh

theorem insert_new_edge (p : Nat) (xs : List Nat) (e : Edge)
    (ha : e∈edges (insert p xs).positions) (hn : e∉edges xs) :
    e∈(insert p xs).fresh := by
  obtain ⟨pre,post,hafter,hbefore⟩:=insert_edge_repair p xs
  by_cases hf : e∈(insert p xs).fresh
  · exact hf
  · apply False.elim
    apply hn
    rw [hafter] at ha
    rw [hbefore]
    simp only [List.mem_append,hf,false_or,or_false] at ha
    rcases ha with hh|hh <;> simp [hh]

theorem insertMany_new_edge (src dst : List Nat) (e : Edge)
    (ha : e∈edges (insertMany src dst).positions) (hn : e∉edges dst) :
    e∈(insertMany src dst).fresh := by
  induction src generalizing dst with
  | nil => exact False.elim (hn ha)
  | cons p ps ih =>
    by_cases hs : e∈edges (insert p dst).positions
    · have hf:=insert_new_edge p dst e hs hn
      change e∈(insert p dst).fresh++(insertMany ps (insert p dst).positions).fresh
      exact List.mem_append_left _ hf
    · have hf:=ih (insert p dst).positions ha hs
      change e∈(insert p dst).fresh++(insertMany ps (insert p dst).positions).fresh
      exact List.mem_append_right _ hf

/-- This names the existing call at a `build` node; it is definitionally
the same child-size choice and the same `insertMany` execution. -/
def joined (a b : MergeTree) : Trace :=
  if (build a).positions.length≤(build b).positions.length then
    insertMany (build a).positions (build b).positions
  else insertMany (build b).positions (build a).positions

theorem build_joined_positions (a b : MergeTree) :
    (build (.node a b)).positions=(joined a b).positions := rfl

theorem build_joined_fresh (a b : MergeTree) :
    (build (.node a b)).fresh=(build a).fresh++(build b).fresh++(joined a b).fresh := rfl

def Coexists (t : MergeTree) (i j : Nat) : Prop := i∈leaves t ∧ j∈leaves t

theorem build_adjacent (t : MergeTree) (i j : Nat) (ha : Adjacent (leaves t) i j) :
    Adjacent (build t).positions i j :=
  ⟨(build_perm t).mem_iff.mpr ha.1,(build_perm t).mem_iff.mpr ha.2.1,ha.2.2.1,
    fun k hk hik hkj=>ha.2.2.2 k ((build_perm t).mem_iff.mp hk) hik hkj⟩

theorem first_join_live_fresh (a b : MergeTree) (i j : Nat)
    (hn : (leaves (.node a b)).Nodup) (ha : Adjacent (leaves (.node a b)) i j)
    (hna : ¬Coexists a i j) (hnb : ¬Coexists b i j) :
    (i,j)∈(joined a b).fresh ∧ (i,j)∈edges (build (.node a b)).positions := by
  have hedge:=adjacent_edge _ i j (build_strict (.node a b) hn)
    (build_adjacent (.node a b) i j ha)
  refine ⟨?_,hedge⟩
  have hafter : (i,j)∈edges (joined a b).positions := by
    simpa only [build_joined_positions] using hedge
  by_cases hsize : (build a).positions.length≤(build b).positions.length
  · simp only [joined,hsize,if_true] at hafter ⊢
    apply insertMany_new_edge _ _ _ hafter
    intro he
    have hh:=edge_members _ i j he
    exact hnb ⟨(build_perm b).mem_iff.mp hh.1,(build_perm b).mem_iff.mp hh.2⟩
  · simp only [joined,hsize,if_false] at hafter ⊢
    apply insertMany_new_edge _ _ _ hafter
    intro he
    have hh:=edge_members _ i j he
    exact hna ⟨(build_perm a).mem_iff.mp hh.1,(build_perm a).mem_iff.mp hh.2⟩

inductive Subtree : MergeTree→MergeTree→Prop where
  | refl (t : MergeTree) : Subtree t t
  | left {s a b : MergeTree} : Subtree s a→Subtree s (.node a b)
  | right {s a b : MergeTree} : Subtree s b→Subtree s (.node a b)

theorem subtree_leaves {s t : MergeTree} (h : Subtree s t) :
    ∀k,k∈leaves s→k∈leaves t := by
  induction h with
  | refl => exact fun _ h=>h
  | left h ih => exact fun k hk=>List.mem_append_left _ (ih k hk)
  | right h ih => exact fun k hk=>List.mem_append_right _ (ih k hk)

theorem subtree_nodup {s t : MergeTree} (h : Subtree s t) :
    (leaves t).Nodup→(leaves s).Nodup := by
  induction h with
  | refl => exact id
  | left h ih => exact fun hn=>ih ((List.sublist_append_left _ _).nodup hn)
  | right h ih => exact fun hn=>ih ((List.sublist_append_right _ _).nodup hn)

/-- The first binary coexistence exists even before deciding which
equal-depth ancestors complete the entire prefix class. -/
theorem first_coexistence (t : MergeTree) (i j : Nat) (hne : i≠j)
    (hi : i∈leaves t) (hj : j∈leaves t) :
    ∃ a b,Subtree (.node a b) t ∧ Coexists (.node a b) i j ∧
      ¬Coexists a i j ∧ ¬Coexists b i j := by
  induction t with
  | leaf p =>
    simp only [leaves,List.mem_singleton] at hi hj
    exact False.elim (hne (hi.trans hj.symm))
  | node a b iha ihb =>
    by_cases ha : Coexists a i j
    · obtain ⟨x,y,hs,hco,hx,hy⟩:=iha ha.1 ha.2
      exact ⟨x,y,.left hs,hco,hx,hy⟩
    · by_cases hb : Coexists b i j
      · obtain ⟨x,y,hs,hco,hx,hy⟩:=ihb hb.1 hb.2
        exact ⟨x,y,.right hs,hco,hx,hy⟩
      · exact ⟨a,b,.refl _,⟨hi,hj⟩,ha,hb⟩

theorem subtree_fresh {s t : MergeTree} (h : Subtree s t) :
    ∀e,e∈(build s).fresh→e∈(build t).fresh := by
  induction h with
  | refl => exact fun _ h=>h
  | left h ih =>
    intro e he
    rw [build_joined_fresh]
    have hh:=ih e he
    simp only [List.mem_append,hh,true_or]
  | right h ih =>
    intro e he
    rw [build_joined_fresh]
    have hh:=ih e he
    simp only [List.mem_append,hh,true_or,or_true]

theorem first_live_generation (t : MergeTree) (later : List Nat) (i j : Nat)
    (hn : (leaves t).Nodup) (ha : Adjacent later i j)
    (hsub : ∀k,k∈leaves t→k∈later) (hi : i∈leaves t) (hj : j∈leaves t) :
    (i,j)∈(build t).fresh ∧ (i,j)∈edges (build t).positions ∧
      ∃ a b,Subtree (.node a b) t ∧ ¬Coexists a i j ∧ ¬Coexists b i j ∧
        (i,j)∈(joined a b).fresh ∧ (i,j)∈edges (build (.node a b)).positions := by
  have hij:=ha.2.2.1
  obtain ⟨a,b,hs,hco,hna,hnb⟩:=first_coexistence t i j (by omega) hi hj
  have hsmall:=adjacent_subset (leaves (.node a b)) later i j ha
    (fun k hk=>hsub k (subtree_leaves hs k hk)) hco.1 hco.2
  have hg:=first_join_live_fresh a b i j (subtree_nodup hs hn) hsmall hna hnb
  have hnode : (i,j)∈(build (.node a b)).fresh := by
    rw [build_joined_fresh]
    simp only [List.mem_append,hg.1,or_true]
  have hlive:=adjacent_edge _ i j (build_strict t hn)
    (build_adjacent t i j (adjacent_subset _ later i j ha hsub hi hj))
  exact ⟨subtree_fresh hs _ hnode,hlive,a,b,hs,hna,hnb,hg.1,hg.2⟩

/-- The same generation is present in the actual completed merge trace,
and discovery is justified at the full prefix class, even when generation
first occurred at an incomplete equal-depth binary refinement below it. -/
theorem completed_class_generated {σ : Nat} (f : Nat→Fin σ) (n base H L : Nat)
    (t : MergeTree) (later : List Nat) (i j : Nat) (parentDepth : Option Nat)
    (hgate : classBoundary parentDepth H=true)
    (hfull : Complete f n base H (leaves t)) (hn : (leaves t).Nodup)
    (ha : Adjacent later i j) (hsub : ∀k,k∈leaves t→k∈later)
    (hi : i∈leaves t) (hj : j∈leaves t) (hLH : L≤H) (hdense : 2*(j-i)≤L) :
    ∃R,(discoverClass (LCEIndex.prepare f n) (LCEIndex.prepareReverse f n)
          n i j H parentDepth).1=some R ∧
      R.Valid f n ∧ R.period=j-i ∧ R.lo≤i ∧ j+H≤R.hi ∧ 3*R.period≤R.hi-R.lo ∧
      (i,j)∈(build t).fresh ∧ (i,j)∈edges (build t).positions := by
  obtain ⟨R,hr,hvalid,hperiod,hlo,hhi,hcubic⟩:=completed_class_discovery f n base H L
    (leaves t) later i j parentDepth hgate hfull ha hsub hi hj hLH hdense
  have hg:=first_live_generation t later i j hn ha hsub hi hj
  exact ⟨R,hr,hvalid,hperiod,hlo,hhi,hcubic,hg.1,hg.2.1⟩

end REWB.MaskedRunDiscovery
