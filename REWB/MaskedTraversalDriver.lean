import REWB.MaskedTraversalFrontierMerge
import REWB.MaskedRunOwnerCost

/-! A concrete bottom-up driver for the constructed compressed suffix trie.

Both children are fully lowered to the parent depth before their actual
small-to-large occurrence merge.  Their plans remain in chronological
child/child/merge/edge order.  Equal-depth refinements produce empty edge
plans; they do not pretend to be complete occurrence classes.

This executes occurrence insertion, queue consumption and leader repair.
The retained plan is the input for a separate mutable-source/bank executor:
its bank initialization, local repairs, and masked reports are not charged
as if they had already been implemented by this geometric driver.
-/
namespace REWB.MaskedTraversalDriver
open REWB.MaskedTraversalFrontier
open REWB.BoundaryTrie
variable {h n : Nat}

structure Step (h : Nat) where
  floor : Nat
  high : Nat
  before : Frontier h
  lowered : Lowered h
  deriving Repr

inductive Plan (h : Nat) where
  | empty : Step h→Plan h
  | leaf : Nat→Inserted h→Step h→Plan h
  | node : Plan h→Plan h→Merged h→Step h→Plan h
  deriving Repr

structure Counters where
  generated : Nat
  popped : Nat
  discarded : Nat
  imports : Nat
  bands : Nat
  work : Nat
  deriving Repr

structure Built (h : Nat) extends Counters where
  frontier : Frontier h
  plan : Plan h
  deriving Repr

/-- The sole extra list traversal is the new edge's band-count read.  Its
actual length is explicitly added to work, and no previous log is copied. -/
def finish (capacity floor high : Nat) (s : Frontier h) (wrap : Step h→Plan h)
    (before : Counters) : Built h :=
  let lowered:=lower capacity floor high s
  let count:=lowered.edge.path.bands.length
  ⟨⟨before.generated,before.popped+lowered.edge.path.popped,before.discarded,before.imports,
      before.bands+count,before.work+lowered.edge.path.work+count+4⟩,
    lowered.frontier,wrap ⟨floor,high,s,lowered⟩⟩

def build (capacity floor : Nat) : Tree n Nat→Built h
  | .empty => finish capacity floor 0 (empty h) .empty ⟨0,0,0,0,0,4⟩
  | .leaf a =>
    let leaf:=insert capacity a.length a.start (empty h)
    finish capacity floor a.length leaf.frontier (.leaf a.start leaf)
      ⟨leaf.generated,0,0,0,0,leaf.work+4⟩
  | .node _ depth left right =>
    let a:=build capacity depth left
    let b:=build capacity depth right
    let merged:=merge capacity depth a.frontier b.frontier
    finish capacity floor depth merged.frontier (.node a.plan b.plan merged)
      ⟨a.generated+b.generated+merged.generated,a.popped+b.popped,
        a.discarded+b.discarded+merged.discarded,a.imports+b.imports+merged.imports,
        a.bands+b.bands,a.work+b.work+merged.work+4⟩

/-- Capacity construction is shared across the complete traversal. -/
def run (h : Nat) (t : Tree n Nat) : Built h :=
  let capacity:=MaskedOrdered.capacity h
  let out:=build capacity.1 0 t
  {out with work:=out.work+capacity.2}

theorem finish_occurrences (capacity floor high : Nat) (s : Frontier h)
    (wrap : Step h→Plan h) (before : Counters) :
    (finish capacity floor high s wrap before).frontier.state.occurrences=s.state.occurrences :=
  lower_occurrences capacity floor high s

theorem finish_valid (capacity floor high : Nat) (s : Frontier h)
    (wrap : Step h→Plan h) (before : Counters) (hv : s.Valid high)
    (hc : capacity=2^h) (hle : floor≤high) :
    (finish capacity floor high s wrap before).frontier.Valid floor :=
  lower_valid capacity floor high s hv hc hle

end REWB.MaskedTraversalDriver
