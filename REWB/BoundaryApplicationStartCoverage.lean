import REWB.BoundaryApplicationStartPass

/-! Text-level coverage for the fixed-start pass. A descendant may omit
sources whose common prefix ends at an ancestor depth: those accepted
cuts are already in its incoming E row. Every longer shared prefix is
contained in the selected child, even across zero-depth refinements. -/
namespace REWB.BoundaryApplication.StartCoverage
open REWB.BoundaryTrie
open REWB.Spec (slice)
open REWB.BoundaryIndex
variable {σ : Nat}

def Covered (w : Word (Fin σ)) (fallback : Fin σ) (whole t : StartKeys.TrieFor w) (p : Nat) : Prop :=
  (∀a,a∈t.leaves→a∈whole.leaves) ∧
    ∀b,b∈t.leaves→∀a,a∈whole.leaves→∀L,p<L→Key.Common (StartKeys.text w fallback) a b L→a∈t.leaves

theorem covered_root (w : Word (Fin σ)) (fallback : Fin σ) (t : StartKeys.TrieFor w) (p : Nat) :
    Covered w fallback t t p := ⟨fun _ h=>h,fun _ _ _ h _ _ _=>h⟩

theorem covered_left (w : Word (Fin σ)) (fallback : Fin σ) (whole : StartKeys.TrieFor w)
    (stem : StartKeys.KeyFor w) (d : Nat) (l r : StartKeys.TrieFor w) (p : Nat)
    (hg : (BoundaryTrie.Tree.node stem d l r).Good (StartKeys.text w fallback))
    (hp : p≤d) (hc : Covered w fallback whole (.node stem d l r) p) : Covered w fallback whole l d := by
  refine ⟨fun a ha=>hc.1 a (List.mem_append_left _ ha),?_⟩
  intro b hb a ha L hL hcom
  have hin:=hc.2 b (List.mem_append_left _ hb) a ha L (by omega) hcom
  rcases List.mem_append.mp hin with hal | har
  · exact hal
  · have hex:=hg.2.2.2.2.2.2 b hb a har
    have hbound:=hex.2 L ((Key.common_symmetric _ _ _ _).mp hcom)
    omega

theorem covered_right (w : Word (Fin σ)) (fallback : Fin σ) (whole : StartKeys.TrieFor w)
    (stem : StartKeys.KeyFor w) (d : Nat) (l r : StartKeys.TrieFor w) (p : Nat)
    (hg : (BoundaryTrie.Tree.node stem d l r).Good (StartKeys.text w fallback))
    (hp : p≤d) (hc : Covered w fallback whole (.node stem d l r) p) : Covered w fallback whole r d := by
  refine ⟨fun a ha=>hc.1 a (List.mem_append_right _ ha),?_⟩
  intro b hb a ha L hL hcom
  have hin:=hc.2 b (List.mem_append_right _ hb) a ha L (by omega) hcom
  rcases List.mem_append.mp hin with hal | har
  · have hex:=hg.2.2.2.2.2.2 a hal b hb
    have hbound:=hex.2 L hcom
    omega
  · exact har

def Hits (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (whole : StartKeys.TrieFor w) (b : StartKeys.KeyFor w) (j : Fin (w.length+1))
    (bound finish : Nat) (q : Fin E.stateCount) : Prop :=
  ∃a,a∈whole.leaves ∧ ∃i,a.record=.source i ∧ ∃L,L≤bound ∧
    Key.Common (StartKeys.text w fallback) a b L ∧
    A.accepts (slice w 0 i.val) ∧ B.accepts (slice w j.val (j.val+L)) ∧
    C.accepts (slice w (i.val+L) g) ∧ E.run E.initial (slice w (j.val+L) (j.val+finish))=q

theorem hits_extend (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (whole : StartKeys.TrieFor w) (b : StartKeys.KeyFor w) (j : Fin (w.length+1))
    (p m : Nat) (hp : p≤m) (q : Fin E.stateCount) :
    (∃old,Hits A B C E w fallback g whole b j p p old ∧
      E.run old (slice w (j.val+p) (j.val+m))=q) ↔ Hits A B C E w fallback g whole b j p m q := by
  constructor
  · rintro ⟨old,⟨a,ha,i,ht,L,hL,hc,hA,hB,hC,hE⟩,he⟩
    refine ⟨a,ha,i,ht,L,hL,hc,hA,hB,hC,?_⟩
    rw [OuterColumn.slice_split w (j.val+L) (j.val+p) (j.val+m) (by omega) (by omega),DFA.run_append,hE]
    exact he
  · rintro ⟨a,ha,i,ht,L,hL,hc,hA,hB,hC,hE⟩
    refine ⟨E.run E.initial (slice w (j.val+L) (j.val+p)),⟨a,ha,i,ht,L,hL,hc,hA,hB,hC,rfl⟩,?_⟩
    rw [← DFA.run_append,← OuterColumn.slice_split w (j.val+L) (j.val+p) (j.val+m) (by omega) (by omega)]
    exact hE

theorem combine_iff (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (whole t : StartKeys.TrieFor w) (hg : t.Good (StartKeys.text w fallback)) (p m : Nat)
    (hp : p≤m) (hm : m≤t.depth) (hcover : Covered w fallback whole t p)
    (b : StartKeys.KeyFor w) (hb : b∈t.leaves) (j : Fin (w.length+1)) (q : Fin E.stateCount) :
    Hits A B C E w fallback g whole b j p m q ∨ StartLocal.Fresh A B C E w g t j p m q ↔
      Hits A B C E w fallback g whole b j m m q := by
  constructor
  · rintro (⟨a,ha,i,ht,L,hL,hc,hA,hB,hC,hE⟩ | ⟨a,ha,i,ht,L,hpL,hLm,hA,hB,hC,hE⟩)
    · exact ⟨a,ha,i,ht,L,by omega,hc,hA,hB,hC,hE⟩
    · exact ⟨a,hcover.1 a ha,i,ht,L,hLm,
        Key.common_shorten _ _ _ _ _ (BoundaryTrie.Tree.depth_common _ t hg a b ha hb) (by omega),
        hA,hB,hC,hE⟩
  · rintro ⟨a,ha,i,ht,L,hL,hc,hA,hB,hC,hE⟩
    by_cases hLp : L≤p
    · exact Or.inl ⟨a,ha,i,ht,L,hLp,hc,hA,hB,hC,hE⟩
    · exact Or.inr ⟨a,hcover.2 b hb a ha L (by omega) hc,i,ht,L,by omega,hL,hA,hB,hC,hE⟩

theorem root_fresh (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (t : StartKeys.TrieFor w) (hg : t.Good (StartKeys.text w fallback)) (m : Nat) (hm : m≤t.depth)
    (b : StartKeys.KeyFor w) (hb : b∈t.leaves) (j : Fin (w.length+1)) (q : Fin E.stateCount) :
    StartLocal.Fresh A B C E w g t j 0 m q ↔ Hits A B C E w fallback g t b j m m q := by
  constructor
  · rintro ⟨a,ha,i,ht,L,_,hL,hA,hB,hC,hE⟩
    exact ⟨a,ha,i,ht,L,hL,
      Key.common_shorten _ _ _ _ _ (BoundaryTrie.Tree.depth_common _ t hg a b ha hb) (by omega),
      hA,hB,hC,hE⟩
  · rintro ⟨a,ha,i,ht,L,hL,_,hA,hB,hC,hE⟩
    exact ⟨a,ha,i,ht,L,Nat.zero_le _,hL,hA,hB,hC,hE⟩

def Previous (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (whole t : StartKeys.TrieFor w) (p : Nat) (incoming : StartCuts.Row E) : Prop :=
  (p=0 ∧ t=whole ∧ ∀q,incoming.get q=false) ∨
    ∀b,b∈t.leaves→∀j,b.record=.target j→∀q,
      incoming.get q=true ↔ Hits A B C E w fallback g whole b j p p q

theorem query_hits (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (whole t : StartKeys.TrieFor w) (hg : t.Good (StartKeys.text w fallback))
    (hv : ∀a,a∈t.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a))
    (b : StartKeys.KeyFor w) (hb : b∈t.leaves) (j : Fin (w.length+1)) (ht : b.record=.target j)
    (p m : Nat) (hp : p≤m) (hm : m≤t.depth) (hcover : Covered w fallback whole t p)
    (beta : Fin B.stateCount) (hbeta : beta=B.run B.initial (slice w j.val (j.val+p)))
    (incoming : StartCuts.Row E) (hprev : Previous A B C E w fallback g whole t p incoming)
    (row : StartCuts.Row C) (hrow : ∀q,row.get q=true ↔ StartSummary.Source A C w g t q)
    (q : Fin E.stateCount) :
    (StartStep.query B C E (StartCuts.build B C E w) (Range.build C w) (Range.build E w)
      (StartLocal.entry B C E w t p beta incoming row) m).states.get q=true ↔
      Hits A B C E w fallback g whole b j m m q := by
  rw [StartLocal.query_correct A B C E w fallback g t hg hv b hb j ht p m hp hm beta hbeta incoming row hrow q]
  rcases hprev with ⟨hp0,heq,hempty⟩ | hprev
  · subst p
    subst whole
    simp only [hempty,Bool.false_eq_true,false_and,exists_false,false_or]
    exact root_fresh A B C E w fallback g t hg m hm b hb j q
  · have hpre (old : Fin E.stateCount) := hprev b hb j ht old
    simp only [hpre]
    rw [hits_extend A B C E w fallback g whole b j p m hp q]
    exact combine_iff A B C E w fallback g whole t hg p m hp hm hcover b hb j q

end REWB.BoundaryApplication.StartCoverage
