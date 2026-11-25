import REWB.BoundaryApplicationHeavyIndex

/-! The direct-address fixed-end query uses the actual A prefix map and
the two persistent endpoint indexes stored at each heavy-segment bottom.
This file proves its logarithmic jump and endpoint-query costs and exact
semantics along the stored jump chain. Whole source/target LCA coverage is
a separate theorem; the chain statement does not assume that coverage. -/
namespace REWB.BoundaryApplication.HeavyIndex
open REWB.BoundaryIndex
open REWB.BoundaryIndex.Merge
open REWB.Spec (slice)
variable {σ : Nat}

def probeAt (A D E : DFA (Fin σ)) (n : Nat) (ranges : Range.Index A)
    (source : Fin (n+1)) (right : Nat) (c : Address.Cell A D E n) : Bool×Nat :=
  let pre:=Range.query A ranges 0 (source.val-c.entry.depth)
  let alpha:=pre.map.get A.initial
  let path:=TokenIndex.query E (Colors.select A alpha) c.entry.subsets.tree (right+1)
  let normal:=TokenIndex.query E (fun delta=>Colors.select A alpha (c.entry.rows.get delta))
    c.entry.normal.state.tree (right+1)
  (path.1 || normal.1,pre.work+path.2+normal.2+4)

/-- A specification-friendly wrapper. Actual index queries call
`probeAt` with the stored length, so the word is never rescanned. -/
def probe (A D E : DFA (Fin σ)) (w : Word (Fin σ)) (ranges : Range.Index A)
    (source : Fin (w.length+1)) (right : Nat) (c : Address.Cell A D E w.length) : Bool×Nat :=
  probeAt A D E w.length ranges source right c

def probeBudget (A D E : DFA (Fin σ)) (n : Nat) : Nat :=
  A.stateCount+8*(n.log2+2)+1+
    ((height n+1)*Tree.queryBudget (Subset.count A) E.stateCount+Subset.count A+Subset.count A*E.stateCount)+
    ((height n+1)*Tree.queryBudget D.stateCount E.stateCount+D.stateCount+D.stateCount*E.stateCount)+4

theorem probe_work (A D E : DFA (Fin σ)) (w : Word (Fin σ))
    (source : Fin (w.length+1)) (right : Nat) (c : Address.Cell A D E w.length) :
    (probe A D E w (Range.build A w) source right c).2≤probeBudget A D E w.length := by
  let pre:=Range.query A (Range.build A w) 0 (source.val-c.entry.depth)
  let alpha:=pre.map.get A.initial
  have ha:=Range.query_work A w 0 (source.val-c.entry.depth) (Nat.zero_le _)
    (by have hh:=source.isLt; omega)
  have hp:=TokenIndex.query_steps E (Colors.select A alpha) c.entry.subsets.tree (right+1)
  have hn:=TokenIndex.query_steps E (fun delta=>Colors.select A alpha (c.entry.rows.get delta))
    c.entry.normal.state.tree (right+1)
  change pre.work+_+_+4≤_
  unfold probeBudget
  simp only [Subset.count] at hp ⊢
  dsimp only [pre,alpha] at *
  omega

def Local (A D E : DFA (Fin σ)) (w : Word (Fin σ)) (source : Fin (w.length+1)) (right : Nat)
    (c : Address.Cell A D E w.length) : Prop :=
  let alpha:=A.run A.initial (slice w 0 (source.val-c.entry.depth))
  (∃i : Position (height w.length),i.val≤right ∧ ∃q,
    Subset.Selected A c.entry.subsets.tree i alpha q ∧ E.final (E.run q (slice w i.val right))=true) ∨
  (∃i : Position (height w.length),i.val≤right ∧ ∃delta q,
    Colors.select A alpha (c.entry.rows.get delta)=true ∧
    (point c.entry.normal.state.tree i).active delta q=true ∧ E.final (E.run q (slice w i.val right))=true)

theorem probe_correct (A D E : DFA (Fin σ)) (w : Word (Fin σ))
    (source : Fin (w.length+1)) (right : Nat) (hr : right≤w.length)
    (c : Address.Cell A D E w.length)
    (hc : Heavy.EntryGood A D E w.length (base D.stateCount E w).1 (base (Subset.count A) E w).1 c.entry) :
    (probe A D E w (Range.build A w) source right c).1=true ↔ Local A D E w source right c := by
  have hs : ∀i : Position (height w.length),(point c.entry.subsets.tree i).trans=
      ((FixedEnd.rows E w)[i.val]?.getD (Vector.ofFn id)).get := by
    intro i
    rw [hc.2.2 i]
    exact MergeBuild.prepare_trans _ _ _
  have hn : ∀i : Position (height w.length),(point c.entry.normal.state.tree i).trans=
      ((FixedEnd.rows E w)[i.val]?.getD (Vector.ofFn id)).get := by
    intro i
    rw [hc.1.2 i]
    exact MergeBuild.prepare_trans _ _ _
  have ha:=Range.query_correct A w 0 (source.val-c.entry.depth) (Nat.zero_le _)
    (by have hh:=source.isLt; omega) A.initial
  simp only [probe,probeAt,Bool.or_eq_true,ha,Local]
  rw [Aggregate.query_correct E w c.entry.subsets.tree hc.2.1.1 (Tree.capacity _) hs _ right hr,
    Aggregate.query_correct E w c.entry.normal.state.tree hc.1.1.1 (Tree.capacity _) hn _ right hr]
  constructor
  · rintro (⟨i,hi,color,q,hcolor,hactive,hfinal⟩ | hnormal)
    · exact Or.inl ⟨i,hi,q,⟨color,hcolor,hactive⟩,hfinal⟩
    · exact Or.inr hnormal
  · rintro (⟨i,hi,q,⟨color,hcolor,hactive⟩,hfinal⟩ | hnormal)
    · exact Or.inl ⟨i,hi,color,q,hcolor,hactive,hfinal⟩
    · exact Or.inr hnormal

def cachedSource (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Index A B D E w)
    (source : Fin (w.length+1)) : Fin (idx.cachedLength+1) :=
  ⟨source.val,by rw [idx.length_eq]; exact source.isLt⟩

def cachedStore (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Index A B D E w) :
    Address.Store A D E idx.cachedLength := idx.length_eq.symm ▸ idx.addresses

def query (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Index A B D E w)
    (source : Fin (w.length+1)) (right : Nat) : Address.Answer :=
  let p:=cachedSource A B D E w idx source
  Address.query (probeAt A D E idx.cachedLength idx.ranges p right) (cachedStore A B D E w idx) p

theorem query_bound (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (source : Fin (w.length+1)) (right : Nat) :
    (query A B D E w (build A B D E w fallback g hg) source right).visits≤(w.length+2).log2+1 ∧
    (query A B D E w (build A B D E w fallback g hg) source right).work≤
      ((w.length+2).log2+1)*(probeBudget A D E w.length+4)+5 :=
  Address.query_bound _ _ _ _ _ (build_rank A B D E w fallback g hg)
    (fun _ c _=>probe_work A D E w source right c)

def OnChain (xs : Array (Address.Cell A D E n)) (cursor : Option Nat)
    (c : Address.Cell A D E n) : Prop :=
  match cursor with
  | none => False
  | some i => Address.Reaches xs i c

theorem reaches_get {A D E : DFA (Fin σ)} {n : Nat} (xs : Array (Address.Cell A D E n))
    (i : Nat) (c : Address.Cell A D E n) (hc : Address.Reaches xs i c) :
    ∃j : Nat,xs[j]?=some c := by
  induction hc with
  | here h => exact ⟨_,h⟩
  | next _ _ _ ih => exact ih

def ChainPredicate (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Index A B D E w)
    (source : Fin (w.length+1)) (right : Nat) : Prop :=
  ∃c,OnChain idx.addresses.nodes (idx.addresses.sources.get source) c ∧ Local A D E w source right c

theorem query_chain_iff (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (source : Fin (w.length+1)) (right : Nat) (hr : right≤w.length) :
    (query A B D E w (build A B D E w fallback g hg) source right).value=true ↔
      ChainPredicate A B D E w (build A B D E w fallback g hg) source right := by
  let idx:=build A B D E w fallback g hg
  change (Address.query _ idx.addresses source).value=true ↔ _
  rw [Address.query_correct _ _ _ (build_good A B D E w fallback g hg) (build_slots A B D E w fallback g hg)]
  change Address.Hits (probe A D E w (Range.build A w) source right) idx.addresses.nodes
    (idx.addresses.sources.get source) ↔ ∃c,OnChain idx.addresses.nodes (idx.addresses.sources.get source) c ∧ _
  cases hs : idx.addresses.sources.get source with
  | none => simp only [Address.Hits,OnChain,false_and,exists_false]
  | some i =>
    constructor
    · rintro ⟨c,hc,hp⟩
      obtain ⟨j,hj⟩:=reaches_get idx.addresses.nodes i c hc
      exact ⟨c,hc,(probe_correct A D E w source right hr c (build_stored A B D E w fallback g hg j c hj)).mp hp⟩
    · rintro ⟨c,hc,hp⟩
      obtain ⟨j,hj⟩:=reaches_get idx.addresses.nodes i c hc
      exact ⟨c,hc,(probe_correct A D E w source right hr c (build_stored A B D E w fallback g hg j c hj)).mpr hp⟩

end REWB.BoundaryApplication.HeavyIndex
