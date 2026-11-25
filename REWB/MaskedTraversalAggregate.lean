import REWB.MaskedFiniteActionRange
import REWB.MaskedClusterMutableStore
import REWB.MaskedTraversalAggregateTrace

/-! Persistent aggregate operations on real stored banks. One identity
template is built and shared by all frontiers. Refreshing a dirty leader
reads its actual slot and replaces one leaf; retired slots become identity.
The source-region query uses three ordered range products, enabling only
the middle source component while retaining every target component.
Physical source intervals that cut clusters require the separate two
boundary-bank clipping step; leader-aligned regions need no clipping.
-/
namespace REWB.MaskedTraversalAggregate
open REWB.MaskedFiniteAction REWB.MaskedCluster
variable {α : Type} {h k m : Nat}

abbrev BankTree (C E : DFA α) (h : Nat) :=
  Tree (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount) h

structure Template (C E : DFA α) (h : Nat) where
  blank : BankTree C E h
  capacity : Nat
  work : Nat

def prepare (C E : DFA α) (h : Nat) : Template C E h :=
  let built:=Tree.build #[] h 0
  ⟨built.1,2^h,built.2+h+1⟩

/-- Reuse the prepared persistent identity; no whole-position rebuild. -/
def fresh (template : Template C E h) : BankTree C E h×Nat := (template.blank,1)

def slot (st : Mutable.Store.State C E) (position : Nat) : Mutable.Store.Bank C E :=
  match st.slots[position]? with
  | some (some entry) => entry.bank
  | _ => Table.one

def refresh (st : Mutable.Store.State C E) (position : Nat) (tree : BankTree C E h) : BankTree C E h×Nat :=
  let out:=Tree.replace tree position (slot st position)
  (out.1,out.2+4)

def refreshMany (st : Mutable.Store.State C E) (positions : List Nat) (tree : BankTree C E h) : BankTree C E h×Nat :=
  positions.foldl (fun acc p=>let out:=refresh st p acc.1; (out.1,acc.2+out.2+1)) (tree,0)

def shorten (action : Vector (Fin (2*ReplayMaps.count C.stateCount E.stateCount))
    (2*ReplayMaps.count C.stateCount E.stateCount)) (tree : BankTree C E h) : BankTree C E h×Nat :=
  Tree.reindex action tree

theorem prepare_good (C E : DFA α) (h : Nat) : (prepare C E h).blank.Good := Tree.build_good #[] h 0

theorem prepare_work (C E : DFA α) (h : Nat) :
    (prepare C E h).work≤2^h*(Tree.joinBudget (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount)+Tree.leafBudget (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount))+h+1 := by
  have hs:=Tree.build_steps (#[] : Array (Mutable.Store.Bank C E)) h 0
  change (Tree.build (#[] : Array (Mutable.Store.Bank C E)) h 0).2+h+1≤_
  omega

theorem prepare_cells (C E : DFA α) (h : Nat) :
    (prepare C E h).blank.leaves=List.replicate (2^h) View.one := by
  rw [show (prepare C E h).blank=(Tree.build (#[] : Array (Mutable.Store.Bank C E)) h 0).1 from rfl,
    Tree.build_leaves]
  simp only [Tree.cells,Array.getElem?_empty,Option.getD_none,Table.view_one]
  simpa only [List.length_range'] using (List.map_const' (l:=List.range' 0 (2^h)) (b:=View.one))

theorem refresh_good (st : Mutable.Store.State C E) (p : Nat) (tree : BankTree C E h) (hg : tree.Good) :
    (refresh st p tree).1.Good := Tree.replace_good tree hg p _

theorem refresh_cells (st : Mutable.Store.State C E) (p : Nat) (tree : BankTree C E h) :
    (refresh st p tree).1.leaves=tree.leaves.set p (slot st p).view := Tree.replace_leaves tree p _

theorem refresh_work (st : Mutable.Store.State C E) (p : Nat) (tree : BankTree C E h) :
    (refresh st p tree).2≤(h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount)+4 := by
  have hw:=Tree.replace_steps tree p (slot st p)
  exact Nat.add_le_add_right hw 4

theorem refreshMany_good (st : Mutable.Store.State C E) (positions : List Nat) (tree : BankTree C E h)
    (hg : tree.Good) : (refreshMany st positions tree).1.Good := by
  have go : ∀(ps : List Nat) (acc : BankTree C E h×Nat),acc.1.Good→
      (ps.foldl (fun acc p=>let out:=refresh st p acc.1; (out.1,acc.2+out.2+1)) acc).1.Good := by
    intro ps
    induction ps with
    | nil => intro acc hv; exact hv
    | cons p ps ih =>
      intro acc hv
      exact ih _ (refresh_good st p acc.1 hv)
  exact go positions (tree,0) hg

theorem refreshMany_work (st : Mutable.Store.State C E) (positions : List Nat) (tree : BankTree C E h) :
    (refreshMany st positions tree).2≤positions.length*((h+1)*Tree.replaceBudget
      (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)+5) := by
  let budget:=(h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
    (2*(MaskedClusterStage.dfa C E).stateCount)+5
  have go : ∀(ps : List Nat) (acc : BankTree C E h×Nat),
      (ps.foldl (fun acc p=>let out:=refresh st p acc.1; (out.1,acc.2+out.2+1)) acc).2≤
        acc.2+ps.length*budget := by
    intro ps
    induction ps with
    | nil => intro acc; simp only [List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero,Nat.le_refl]
    | cons p ps ih =>
      intro acc
      have tail:=ih ((refresh st p acc.1).1,acc.2+(refresh st p acc.1).2+1)
      have one:=refresh_work st p acc.1
      simp only [List.foldl_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      dsimp only at tail
      dsimp only [budget] at tail ⊢
      omega
  simpa only [refreshMany,Nat.zero_add] using go positions (tree,0)

theorem shorten_cells (action : Vector (Fin (2*ReplayMaps.count C.stateCount E.stateCount))
    (2*ReplayMaps.count C.stateCount E.stateCount)) (tree : BankTree C E h) :
    (shorten action tree).1.leaves=tree.leaves.map (View.reindex action.get) := Tree.reindex_leaves action tree

/-- Proof-only chronological matrix paths; no query builds this list. -/
def Chain (key : Fin k) : List (View k m)→Fin m→Fin m→Prop
  | [],i,j => i=j
  | a::as,i,j => ∃mid,a key i mid=true ∧ Chain key as mid j

theorem product_chain (key : Fin k) (cells : List (View k m)) (i j : Fin m) :
    View.product cells key i j=true ↔ Chain key cells i j := by
  induction cells generalizing i with
  | nil => exact decide_eq_true_iff
  | cons a as ih =>
    change FiniteRelation.comp (FiniteRelation.finEnum m) (a key) (View.product as key) i j=true ↔ _
    rw [FiniteRelation.comp_true]
    simp only [Chain,ih]

theorem cache_chain (tree : Tree k m h) (hg : tree.Good) (key : Fin k) (i j : Fin m) :
    tree.cache.view key i j=true ↔ Chain key tree.leaves i j := by
  rw [Tree.cache_correct tree hg,product_chain]

def component {c e : Nat} (gate : Bool) (v : View (2*ReplayMaps.count c e) m) : View (ReplayMaps.count c e) m :=
  fun key=>v (code _ gate key)

theorem component_product {c e : Nat} (gate : Bool) (vs : List (View (2*ReplayMaps.count c e) m)) :
    component gate (View.product vs)=View.product (vs.map (component gate)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change View.mul (component gate v) (component gate (View.product vs))=_
    rw [ih]
    rfl

/-- Source gates apply to leaf/leader positions. Arbitrary source windows
also need clipped boundary banks. The target mask is untouched throughout. -/
def region (tree : BankTree C E h) (lo hi : Nat) :
    Table (ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat :=
  let before:=Tree.queryPrefix tree lo
  let inside:=Tree.queryRange tree lo hi
  let after:=Tree.querySuffix tree hi
  let a:=bankComponent before.1 false
  let b:=bankComponent inside.1 true
  let c:=bankComponent after.1 false
  let ab:=Counted.mul a.1 b.1
  let abc:=Counted.mul ab.1 c.1
  (abc.1,before.2+inside.2+after.2+a.2+b.2+c.2+ab.2+abc.2+8)

def regionCells {c e : Nat} (cells : List (View (2*ReplayMaps.count c e) m)) (lo hi : Nat) :
    List (View (ReplayMaps.count c e) m) :=
  (cells.take lo).map (component false)++(Spec.slice cells lo hi).map (component true)++
    (cells.drop hi).map (component false)

theorem region_view (tree : BankTree C E h) (hg : tree.Good) (lo hi : Nat) :
    (region tree lo hi).1.view=View.product (regionCells tree.leaves lo hi) := by
  have componentView : ∀ (t : Mutable.Store.Bank C E) (gate : Bool),
      (bankComponent t gate).1.view=component gate t.view := by
    intro t gate
    funext key i j
    exact bankComponent_view t gate key i j
  simp only [region,Counted.mul_view,componentView,Tree.queryPrefix_correct tree hg,
    Tree.queryRange_correct tree hg,Tree.querySuffix_correct tree hg,component_product,
    regionCells,View.product_append]

theorem region_chain (tree : BankTree C E h) (hg : tree.Good) (lo hi : Nat)
    (key : Fin (ReplayMaps.count C.stateCount E.stateCount))
    (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount)) :
    (region tree lo hi).1.view key i j=true ↔ Chain key (regionCells tree.leaves lo hi) i j := by
  rw [region_view tree hg,product_chain]

theorem region_work (tree : BankTree C E h) (lo hi : Nat) :
    (region tree lo hi).2≤4*(h+1)*Tree.queryBudget (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount)+3*ReplayMaps.count C.stateCount E.stateCount+
      2*(ReplayMaps.count C.stateCount E.stateCount*((2*(MaskedClusterStage.dfa C E).stateCount)*
        ((2*(MaskedClusterStage.dfa C E).stateCount)*((2*(MaskedClusterStage.dfa C E).stateCount)+1))))+8 := by
  have hp:=Tree.queryPrefix_steps tree lo
  have hm:=Tree.queryRange_steps tree lo hi
  have hs:=Tree.querySuffix_steps tree hi
  simp only [region,bankComponent_work,Counted.mul_steps]
  simp only [Nat.mul_assoc] at hm ⊢
  omega

end REWB.MaskedTraversalAggregate
