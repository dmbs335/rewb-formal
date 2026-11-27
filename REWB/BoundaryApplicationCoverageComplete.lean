import REWB.BoundaryApplicationCoverageRoute

/-! End-to-end correctness of the actual fixed-end heavy index. The
caller supplies only the text, the fixed split, and the query endpoints.
The compressed trie, persistent colors, subset versions, source slots,
and head jumps are all the outputs of the measured executable builders.
No supplied occurrence class, source path, or coverage oracle remains. -/
namespace REWB.BoundaryApplication.Coverage
open REWB.BoundaryIndex
open REWB.Spec (slice)
variable {σ : Nat}

theorem trie_targets_iff (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (source : Fin (w.length+1)) (right : Nat) :
    Targets A B D E w g source right (FixedEnd.trie w fallback g hg).tree ↔
      Predicate A B D E w g source right := by
  constructor
  · rintro ⟨a,_,target,_,hp⟩
    exact ⟨target,hp⟩
  · rintro ⟨target,hr,hE,L,hcut⟩
    have ht : g≤target.val := Nat.le_trans (Nat.le_add_right g L) hcut.2.1
    obtain ⟨a,ha,hrec⟩:=FixedEnd.trie_target w fallback g hg target ht
    exact ⟨a,ha,target,hrec,hr,hE,L,hcut⟩

/-- The complete executable query is true exactly when a target endpoint
and accepted repeated word exist. All cut intervals are closed, so the
empty repeated word and the right-endpoint epsilon suffix are included. -/
theorem query_correct (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (source : Fin (w.length+1)) (hs : source.val≤g)
    (right : Nat) (hr : right≤w.length) :
    (HeavyIndex.query A B D E w (HeavyIndex.build A B D E w fallback g hg) source right).value=true ↔
      Predicate A B D E w g source right := by
  obtain ⟨es,hroute,hquery⟩:=HeavyIndex.query_route_iff A B D E w fallback g hg source hs right hr
  have hcoverage:=route_iff A B D E w fallback g (HeavyIndex.base (Subset.count A) E w).1
    (MergeBuild.prepare_blank _ _) (HeavyIndex.base D.stateCount E w).1
    (MergeBuild.prepare_good _ _) (MergeBuild.prepare_blank _ _)
    (FixedEnd.trie w fallback g hg).tree (FixedEnd.trie_good w fallback g hg)
    (FixedEnd.trie_nonempty w fallback g hg) (FixedEnd.trie_valid w fallback g hg)
    (Heavy.blank (HeavyIndex.base (Subset.count A) E w).1) source right es hroute
  rw [hquery]
  change Hits A D E w source right es ↔ _
  rw [hcoverage]
  have hb:=incoming_blank A E w (HeavyIndex.base (Subset.count A) E w).1 (MergeBuild.prepare_blank _ _)
    (FixedEnd.trie w fallback g hg).tree.depth source right
  simp only [hb,false_or]
  exact trie_targets_iff A B D E w fallback g hg source right

/-- Expanded mathematical specification, with only natural-number cut
positions and ordinary DFA acceptance. This is the brute fixed-end
existence predicate, independent of every index representation. -/
theorem query_iff_cuts (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (source : Fin (w.length+1)) (hs : source.val≤g)
    (right : Nat) (hr : right≤w.length) :
    (HeavyIndex.query A B D E w (HeavyIndex.build A B D E w fallback g hg) source right).value=true ↔
      ∃target L,target≤right ∧ L≤source.val ∧ g+L≤target ∧
        slice w (source.val-L) source.val=slice w (target-L) target ∧
        A.accepts (slice w 0 (source.val-L)) ∧ B.accepts (slice w (source.val-L) source.val) ∧
        D.accepts (slice w g (target-L)) ∧ E.accepts (slice w target right) := by
  rw [query_correct A B D E w fallback g hg source hs right hr]
  constructor
  · rintro ⟨target,ht,hE,L,hL,hgL,he,hA,hB,hD⟩
    exact ⟨target.val,L,ht,hL,hgL,he,hA,hB,hD,hE⟩
  · rintro ⟨target,L,ht,hL,hgL,he,hA,hB,hD,hE⟩
    exact ⟨⟨target,by omega⟩,ht,hE,L,hL,hgL,he,hA,hB,hD⟩

end REWB.BoundaryApplication.Coverage
