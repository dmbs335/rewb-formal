import REWB.BoundaryApplicationSeparatedSummary

/-! Materialized separated-boundary D rows. Each node asks the shared
fixed-end cut index once for every fixed finite A/D state pair, then
intersects those acceptance rows with the actual source A colors. The
incoming D row is pulled back through one forward range map. -/
namespace REWB.BoundaryApplication.Separated.Cuts
open REWB.BoundaryTrie
open REWB.BoundaryIndex REWB.FiniteRelation
open REWB.Spec (slice)
variable {σ : Nat}

def select (A D : DFA (Fin σ)) (source : Vector Bool A.stateCount)
    (table : Vector (Colors.Color A) D.stateCount) : Vector Bool D.stateCount×Nat :=
  let cells:=Vector.ofFn (fun delta : Fin D.stateCount=>Counted.scan
    (fun alpha=>source.get alpha && Colors.select A alpha (table.get delta)) (List.ofFn id))
  (Vector.ofFn (fun delta=>(cells.get delta).1),Counted.rowWork cells)

theorem select_get (A D : DFA (Fin σ)) (source : Vector Bool A.stateCount)
    (table : Vector (Colors.Color A) D.stateCount) (delta : Fin D.stateCount) :
    (select A D source table).1.get delta=true ↔
      ∃alpha,source.get alpha=true ∧ Colors.select A alpha (table.get delta)=true := by
  simp only [select,Table.get_ofFn,Counted.scan_value]
  change any (finEnum A.stateCount) _=true ↔ _
  simp only [any_true,Bool.and_eq_true]

theorem select_steps (A D : DFA (Fin σ)) (source : Vector Bool A.stateCount)
    (table : Vector (Colors.Color A) D.stateCount) :
    (select A D source table).2=D.stateCount*(A.stateCount+1) := by
  apply Counted.rowWork_uniform
  intro delta
  simp only [Table.get_ofFn,Counted.scan_steps,List.length_ofFn]

structure Result (D : DFA (Fin σ)) where
  row : Vector Bool D.stateCount
  work : Nat

def advance (A B D : DFA (Fin σ)) (cuts : RTable.Shared A B D) (dranges : Range.Index D)
    (start depth parent : Nat) (source : Vector Bool A.stateCount)
    (incoming : Vector Bool D.stateCount) : Result D :=
  let table:=RTable.compute A B D cuts (cuts.length-start) depth
  let localRow:=select A D source table.map
  let map:=Range.query D dranges (dranges.length-start-depth) (dranges.length-start-parent)
  ⟨Vector.ofFn (fun delta=>incoming.get (map.map.get delta) || localRow.1.get delta),
    RTable.Result.work A D table+localRow.2+map.work+D.stateCount+8⟩

def Hits (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (g0 g1 : Nat)
    (u : TrieFor w) (target : Fin (w.length+1)) (bound : Nat) : Prop :=
  ∃a,a∈u.leaves ∧ ∃p,a.record=.source p ∧ C.accepts (slice w p.val g0) ∧
    ∃L,L≤bound ∧ Coverage.Cut A B D w g1 p target L

theorem local_correct (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (u : TrieFor w) (hg : u.Good (reverseText w fallback))
    (hv : ∀a,a∈u.leaves→ValidKey g1 (originalKey w a))
    (b : KeyFor w) (hb : b∈u.leaves) (target : Fin (w.length+1)) (ht : b.record=.target target)
    (source : Vector Bool A.stateCount)
    (hsource : ∀q,source.get q=true ↔ Summary.Source A C w g0 u q) :
    (select A D source (RTable.node A B D w (RTable.prepare A B D w) u).map).1.get
      (color D w g1 target u.depth)=true ↔ Hits A B C D w g0 g1 u target u.depth := by
  have hn : u.leaves≠[] := by intro he; rw [he] at hb; cases hb
  rw [select_get]
  simp only [hsource]
  constructor
  · rintro ⟨alpha,⟨a,ha,p,hp,hC,he⟩,hr⟩
    rw [he] at hr
    have hc:=(RTable.node_correct A B D w fallback u hg hn _ _).mp hr
    exact ⟨a,ha,p,hp,hC,(Coverage.node_cut_iff A B D w fallback g1 u hg a b p target
      ha hb (hv a ha) hp (hv b hb) ht).mp hc⟩
  · rintro ⟨a,ha,p,hp,hC,hcuts⟩
    refine ⟨Coverage.alpha A w p.val u.depth,⟨a,ha,p,hp,hC,rfl⟩,?_⟩
    apply (RTable.node_correct A B D w fallback u hg hn _ _).mpr
    exact (Coverage.node_cut_iff A B D w fallback g1 u hg a b p target
      ha hb (hv a ha) hp (hv b hb) ht).mpr hcuts

theorem advance_correct (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 parent : Nat) (u : TrieFor w) (hg : u.Good (reverseText w fallback))
    (hp : parent≤u.depth) (hv : ∀a,a∈u.leaves→ValidKey g1 (originalKey w a))
    (b : KeyFor w) (hb : b∈u.leaves) (target : Fin (w.length+1)) (ht : b.record=.target target)
    (source : Vector Bool A.stateCount)
    (hsource : ∀q,source.get q=true ↔ Summary.Source A C w g0 u q)
    (incoming : Vector Bool D.stateCount) :
    (advance A B D (RTable.prepare A B D w) (Range.build D w)
      (representative w u).start u.depth parent source incoming).row.get (color D w g1 target u.depth)=true ↔
      incoming.get (color D w g1 target parent)=true ∨ Hits A B C D w g0 g1 u target u.depth := by
  change (Vector.ofFn (fun delta=>incoming.get ((edge D w (Range.build D w) parent u).map.get delta) ||
    (select A D source (RTable.node A B D w (RTable.prepare A B D w) u).map).1.get delta)).get
      (color D w g1 target u.depth)=true ↔ _
  rw [Table.get_ofFn,Bool.or_eq_true,edge_color D w fallback g1 parent u b target hg hb (hv b hb) ht hp,
    local_correct A B C D w fallback g0 g1 u hg hv b hb target ht source hsource]

def budget (A D : DFA (Fin σ)) (n : Nat) : Nat :=
  D.stateCount*(A.stateCount*6)+8*(D.stateCount*(A.stateCount*(3*(n.log2+2))))+D.stateCount+
    D.stateCount*(A.stateCount+1)+(D.stateCount+8*(n.log2+2)+1)+D.stateCount+8

theorem advance_work (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (parent : Nat) (u : TrieFor w) (hg : u.Good (reverseText w fallback)) (hn : u.leaves≠[])
    (hp : parent≤u.depth) (source : Vector Bool A.stateCount) (incoming : Vector Bool D.stateCount) :
    (advance A B D (RTable.prepare A B D w) (Range.build D w)
      (representative w u).start u.depth parent source incoming).work≤budget A D w.length := by
  have hr:=RTable.node_work A B D w fallback u hg hn
  have he:=edge_work D w parent u hp
  change RTable.Result.work A D (RTable.node A B D w (RTable.prepare A B D w) u)+
    (select A D source (RTable.node A B D w (RTable.prepare A B D w) u).map).2+
    (edge D w (Range.build D w) parent u).work+D.stateCount+8≤_
  rw [select_steps]
  unfold budget
  omega

end REWB.BoundaryApplication.Separated.Cuts
