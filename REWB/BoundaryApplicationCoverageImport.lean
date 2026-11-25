import REWB.BoundaryApplicationCoverageState

/-! Exact semantics of the actual maintained light list. Importing its
endpoints uses the parent's D colors and acceptance rows. It therefore
contributes precisely the accepted cuts bounded by the parent depth,
without searching the heavy child's endpoints. -/
namespace REWB.BoundaryApplication.Coverage
open REWB.BoundaryIndex
open REWB.BoundaryIndex.Merge
open REWB.Spec (slice)
variable {σ : Nat}

def lightTrie (D E : DFA (Fin σ)) (w : Word (Fin σ))
    (base : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length)) (t : TrieFor w) : TrieFor w :=
  match t with
  | .node _ _ l r => if Heavy.heavyRight (snapshot D E w base t) then l else r
  | _ => t

theorem light_leaves (D E : DFA (Fin σ)) (w : Word (Fin σ))
    (base : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length)) (t : TrieFor w)
    (a : KeyFor w) (ha : a∈(lightTrie D E w base t).leaves) : a∈t.leaves := by
  cases t with
  | empty => exact ha
  | leaf _ => exact ha
  | node stem d l r =>
    simp only [lightTrie] at ha
    split at ha
    · exact List.mem_append_left _ ha
    · exact List.mem_append_right _ ha

theorem light_positions (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (base : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hbg : Tree.Good base) (hbb : MergeSchedule.Blank base)
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g (originalKey w a)) (i : Position (height w.length)) :
    i∈(Heavy.batch w t (snapshot D E w base t)).positions ↔
      ∃a,a∈(lightTrie D E w base t).leaves ∧ ∃target,a.record=.target target ∧ i=position target := by
  cases t with
  | empty => exact False.elim (hn rfl)
  | leaf key => exact snapshot_positions D E w fallback g base hbg hbb (.leaf key) hg hn hv i
  | node stem d l r =>
    have hlv : ∀a,a∈l.leaves→ValidKey g (originalKey w a) :=
      fun a ha=>hv a (List.mem_append_left _ ha)
    have hrv : ∀a,a∈r.leaves→ValidKey g (originalKey w a) :=
      fun a ha=>hv a (List.mem_append_right _ ha)
    simp only [Heavy.batch,Heavy.lightState,lightTrie]
    split
    · exact snapshot_positions D E w fallback g base hbg hbb l hg.1 hg.2.2.1 hlv i
    · exact snapshot_positions D E w fallback g base hbg hbb r hg.2.1 hg.2.2.2.1 hrv i

theorem within_embed (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (source : Fin (w.length+1)) (right depth : Nat) (u t : TrieFor w)
    (hu : ∀a,a∈u.leaves→a∈t.leaves) :
    Within A B D E w g source right depth u→Within A B D E w g source right depth t := by
  rintro ⟨a,ha,target,ht,hpair⟩
  exact ⟨a,hu a ha,target,ht,hpair⟩

theorem import_hit_iff (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hng : Tree.Good normalBase) (hnb : MergeSchedule.Blank normalBase)
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g (originalKey w a))
    (a : KeyFor w) (source : Fin (w.length+1)) (ha : a∈t.leaves) (hs : a.record=.source source)
    (u : TrieFor w) (hu : ∀a,a∈u.leaves→a∈t.leaves)
    (ps : List (Position (height w.length)))
    (hps : ∀i,i∈ps ↔ ∃b,b∈u.leaves ∧ ∃target,b.record=.target target ∧ i=position target)
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) (right : Nat) :
    Incoming A E w t.depth
      (Lift.importMany (RTable.node A B D w (RTable.prepare A B D w) t).map
        (Versions.root (snapshot D E w normalBase t)).state.tree ps incoming).1 source right ↔
      Incoming A E w t.depth incoming source right ∨ Within A B D E w g source right t.depth u := by
  constructor
  · rintro ⟨i,hi,q,hselected,hfinal⟩
    rcases (Subset.node_import_selected A B D w fallback t hg hn _ ps incoming i _ q).mp hselected with
      hprior | ⟨hip,delta,hcut,hactive⟩
    · exact Or.inl ⟨i,hi,q,hprior,hfinal⟩
    · obtain ⟨b,hb,target,ht,he⟩:=(hps i).mp hip
      obtain ⟨c,hc,other,ho,hio,hdelta,hq⟩:=
        (snapshot_active D E w fallback g normalBase hng hnb t hg hn hv i delta q).mp hactive
      have heq : other=target := Fin.ext (by exact congrArg (fun z : Position (height w.length)=>z.val) (hio.symm.trans he))
      subst other
      rw [hdelta] at hcut
      have hcuts:=(node_cut_iff A B D w fallback g t hg a b source target ha (hu b hb)
        (hv a ha) hs (hv b (hu b hb)) ht).mp hcut
      right
      refine ⟨b,hb,target,ht,?_,?_,hcuts⟩
      · rw [he] at hi; exact hi
      · rw [he,hq] at hfinal; exact hfinal
  · rintro (⟨i,hi,q,hprior,hfinal⟩ | ⟨b,hb,target,ht,hr,hE,hcuts⟩)
    · refine ⟨i,hi,q,?_,hfinal⟩
      exact (Subset.node_import_selected A B D w fallback t hg hn _ ps incoming i _ q).mpr (Or.inl hprior)
    · refine ⟨position target,hr,E.initial,?_,hE⟩
      apply (Subset.node_import_selected A B D w fallback t hg hn _ ps incoming _ _ _).mpr
      right
      refine ⟨(hps _).mpr ⟨b,hb,target,ht,rfl⟩,color D w g target t.depth,?_,?_⟩
      · exact (node_cut_iff A B D w fallback g t hg a b source target ha (hu b hb)
          (hv a ha) hs (hv b (hu b hb)) ht).mpr hcuts
      · exact (snapshot_active D E w fallback g normalBase hng hnb t hg hn hv _ _ _).mpr
          ⟨b,hu b hb,target,ht,rfl,rfl,rfl⟩

theorem root_incoming_iff (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hng : Tree.Good normalBase) (hnb : MergeSchedule.Blank normalBase)
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g (originalKey w a))
    (a : KeyFor w) (source : Fin (w.length+1)) (ha : a∈t.leaves) (hs : a.record=.source source)
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) (right : Nat) :
    Incoming A E w t.depth (Heavy.root (saved A B D E w base normalBase t incoming)).subsets source right ↔
      Incoming A E w t.depth incoming source right ∨
        Within A B D E w g source right t.depth (lightTrie D E w normalBase t) := by
  rw [Heavy.root_subsets]
  exact import_hit_iff A B D E w fallback g normalBase hng hnb t hg hn hv a source ha hs
    (lightTrie D E w normalBase t) (light_leaves D E w normalBase t)
    _ (light_positions D E w fallback g normalBase hng hnb t hg hn hv) incoming right

theorem root_local_iff (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hng : Tree.Good normalBase) (hnb : MergeSchedule.Blank normalBase)
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g (originalKey w a))
    (a : KeyFor w) (source : Fin (w.length+1)) (ha : a∈t.leaves) (hs : a.record=.source source)
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) (right : Nat) :
    HeavyIndex.LocalEntry A D E w source right (Heavy.root (saved A B D E w base normalBase t incoming)) ↔
      Incoming A E w t.depth incoming source right ∨ Within A B D E w g source right t.depth t := by
  simp only [HeavyIndex.LocalEntry,HeavyIndex.Local,Heavy.root_depth,Heavy.root_rows,Heavy.root_normal]
  change (Incoming A E w t.depth (Heavy.root (saved A B D E w base normalBase t incoming)).subsets source right ∨
    NormalHit A B D E w normalBase t source right) ↔ _
  rw [root_incoming_iff A B D E w fallback g base normalBase hng hnb t hg hn hv a source ha hs,
    normal_hit_iff A B D E w fallback g normalBase hng hnb t hg hn hv a source ha hs]
  constructor
  · rintro ((hi | hl) | ht)
    · exact Or.inl hi
    · exact Or.inr (within_embed A B D E w g source right t.depth _ t (light_leaves D E w normalBase t) hl)
    · exact Or.inr ht
  · rintro (hi | ht)
    · exact Or.inl (Or.inl hi)
    · exact Or.inr ht

end REWB.BoundaryApplication.Coverage
