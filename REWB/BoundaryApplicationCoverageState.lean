import REWB.BoundaryApplicationCoverage
import REWB.BoundaryApplicationLocate

/-! Semantic invariants for the two actual endpoint versions used on a
heavy route. Incoming subset hits are transported through a materialized
A edge; normal node hits and imported light hits denote exact accepted
source/target cuts. -/
namespace REWB.BoundaryApplication.Coverage
open REWB.BoundaryIndex
open REWB.BoundaryIndex.Merge
open REWB.Spec (slice)
variable {σ : Nat}

abbrev snapshot (D E : DFA (Fin σ)) (w : Word (Fin σ))
    (base : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length)) (t : TrieFor w) :=
  Versions.execute base (compile D E w (Range.build D w) t).1

abbrev saved (A B D E : DFA (Fin σ)) (w : Word (Fin σ))
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (t : TrieFor w) (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :=
  (Heavy.go A B D E w (RTable.prepare A B D w) (Range.build A w) base t
    (snapshot D E w normalBase t) incoming).saved

def Incoming (A E : DFA (Fin σ)) (w : Word (Fin σ)) (depth : Nat)
    (s : Merge.State (Subset.count A) E.stateCount (height w.length))
    (source : Fin (w.length+1)) (right : Nat) : Prop :=
  ∃i : Position (height w.length),i.val≤right ∧ ∃q,
    Subset.Selected A s.tree i (alpha A w source.val depth) q ∧
      E.final (E.run q (slice w i.val right))=true

def Targets (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (source : Fin (w.length+1)) (right : Nat) (t : TrieFor w) : Prop :=
  ∃a,a∈t.leaves ∧ ∃target,a.record=.target target ∧ Pair A B D E w g source target right

def Within (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (source : Fin (w.length+1)) (right depth : Nat) (t : TrieFor w) : Prop :=
  ∃a,a∈t.leaves ∧ ∃target,a.record=.target target ∧ target.val≤right ∧
    E.accepts (slice w target.val right) ∧ ∃L,L≤depth ∧ Cut A B D w g source target L

theorem within_targets (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (source : Fin (w.length+1)) (right depth : Nat) (t : TrieFor w) :
    Within A B D E w g source right depth t → Targets A B D E w g source right t := by
  rintro ⟨a,ha,target,ht,hr,hE,L,_,hcut⟩
  exact ⟨a,ha,target,ht,hr,hE,L,hcut⟩

theorem targets_node (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (source : Fin (w.length+1)) (right : Nat) (stem : KeyFor w) (d : Nat) (l r : TrieFor w) :
    Targets A B D E w g source right (.node stem d l r) ↔
      Targets A B D E w g source right l ∨ Targets A B D E w g source right r := by
  constructor
  · rintro ⟨a,ha,target,ht,hpair⟩
    rcases List.mem_append.mp ha with ha|ha
    · exact Or.inl ⟨a,ha,target,ht,hpair⟩
    · exact Or.inr ⟨a,ha,target,ht,hpair⟩
  · rintro (⟨a,ha,target,ht,hpair⟩|⟨a,ha,target,ht,hpair⟩)
    · exact ⟨a,List.mem_append_left _ ha,target,ht,hpair⟩
    · exact ⟨a,List.mem_append_right _ ha,target,ht,hpair⟩

theorem within_node (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (source : Fin (w.length+1)) (right depth : Nat) (stem : KeyFor w) (d : Nat) (l r : TrieFor w) :
    Within A B D E w g source right depth (.node stem d l r) ↔
      Within A B D E w g source right depth l ∨ Within A B D E w g source right depth r := by
  constructor
  · rintro ⟨a,ha,target,ht,hpair⟩
    rcases List.mem_append.mp ha with ha|ha
    · exact Or.inl ⟨a,ha,target,ht,hpair⟩
    · exact Or.inr ⟨a,ha,target,ht,hpair⟩
  · rintro (⟨a,ha,target,ht,hpair⟩|⟨a,ha,target,ht,hpair⟩)
    · exact ⟨a,List.mem_append_left _ ha,target,ht,hpair⟩
    · exact ⟨a,List.mem_append_right _ ha,target,ht,hpair⟩

theorem incoming_blank (A E : DFA (Fin σ)) (w : Word (Fin σ))
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (hb : MergeSchedule.Blank base) (depth : Nat) (source : Fin (w.length+1)) (right : Nat) :
    ¬Incoming A E w depth (Heavy.blank base) source right := by
  rintro ⟨i,_,q,⟨c,_,hactive⟩,_⟩
  change (point base i).active c q=true at hactive
  rw [hb i c q] at hactive
  cases hactive

theorem incoming_advance (A E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g parent : Nat) (child : TrieFor w) (a : KeyFor w) (source : Fin (w.length+1))
    (hg : child.Good (reverseText w fallback)) (ha : a∈child.leaves)
    (hv : ValidKey g (originalKey w a)) (hs : a.record=.source source) (hd : parent≤child.depth)
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) (right : Nat) :
    Incoming A E w child.depth (Heavy.advance A E w (Range.build A w) parent child incoming).1 source right ↔
      Incoming A E w parent incoming source right := by
  unfold Incoming
  simp only [Heavy.advance_selected,source_edge A w fallback g parent child a source hg ha hv hs hd]

theorem snapshot_active (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (base : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hbg : Tree.Good base) (hbb : MergeSchedule.Blank base)
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g (originalKey w a))
    (i : Position (height w.length)) (c : Fin D.stateCount) (q : Fin E.stateCount) :
    (point (Versions.root (snapshot D E w base t)).state.tree i).active c q=true ↔
      Target D E w g t i c q := by
  rw [Versions.execute_root,Mixed.execute_active base hbg hbb]
  exact compile_active D E w fallback g t hg hn hv i c q

theorem snapshot_positions (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (base : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hbg : Tree.Good base) (hbb : MergeSchedule.Blank base)
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g (originalKey w a)) (i : Position (height w.length)) :
    i∈(Versions.root (snapshot D E w base t)).state.positions ↔
      ∃a,a∈t.leaves ∧ ∃target,a.record=.target target ∧ i=position target := by
  have hs : Valid (Versions.root (snapshot D E w base t)).state := by
    rw [Versions.execute_root]
    exact Mixed.execute_valid base hbg hbb _
  rw [hs.2.2 i]
  constructor
  · rintro ⟨c,q,ha⟩
    obtain ⟨a,ha,target,ht,hi,_,_⟩:=(snapshot_active D E w fallback g base hbg hbb t hg hn hv i c q).mp ha
    exact ⟨a,ha,target,ht,hi⟩
  · rintro ⟨a,ha,target,ht,hi⟩
    exact ⟨color D w g target t.depth,E.initial,
      (snapshot_active D E w fallback g base hbg hbb t hg hn hv _ _ _).mpr ⟨a,ha,target,ht,hi,rfl,rfl⟩⟩

def NormalHit (A B D E : DFA (Fin σ)) (w : Word (Fin σ))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (t : TrieFor w) (source : Fin (w.length+1)) (right : Nat) : Prop :=
  ∃i : Position (height w.length),i.val≤right ∧ ∃delta q,
    Colors.select A (alpha A w source.val t.depth) ((RTable.node A B D w (RTable.prepare A B D w) t).map.get delta)=true ∧
    (point (Versions.root (snapshot D E w normalBase t)).state.tree i).active delta q=true ∧
    E.final (E.run q (slice w i.val right))=true

theorem normal_hit_iff (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hng : Tree.Good normalBase) (hnb : MergeSchedule.Blank normalBase)
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g (originalKey w a))
    (a : KeyFor w) (source : Fin (w.length+1)) (ha : a∈t.leaves) (hs : a.record=.source source) (right : Nat) :
    NormalHit A B D E w normalBase t source right ↔ Within A B D E w g source right t.depth t := by
  constructor
  · rintro ⟨i,hi,delta,q,hrow,hactive,hfinal⟩
    obtain ⟨b,hb,target,ht,hip,hcol,hq⟩:=
      (snapshot_active D E w fallback g normalBase hng hnb t hg hn hv i delta q).mp hactive
    have hp:=(RTable.node_correct A B D w fallback t hg hn _ _).mp hrow
    rw [hcol] at hp
    have hc:=(node_cut_iff A B D w fallback g t hg a b source target ha hb (hv a ha) hs (hv b hb) ht).mp hp
    refine ⟨b,hb,target,ht,?_,?_,hc⟩
    · rw [hip] at hi; exact hi
    · rw [hip,hq] at hfinal; exact hfinal
  · rintro ⟨b,hb,target,ht,hr,hE,hcut⟩
    refine ⟨position target,hr,color D w g target t.depth,E.initial,?_,?_,hE⟩
    · apply (RTable.node_correct A B D w fallback t hg hn _ _).mpr
      exact (node_cut_iff A B D w fallback g t hg a b source target ha hb (hv a ha) hs (hv b hb) ht).mpr hcut
    · exact (snapshot_active D E w fallback g normalBase hng hnb t hg hn hv _ _ _).mpr
        ⟨b,hb,target,ht,rfl,rfl,rfl⟩

end REWB.BoundaryApplication.Coverage
