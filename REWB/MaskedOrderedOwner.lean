import REWB.MaskedOrderedLifecycle
import REWB.MaskedRunTrieBridge

/-! Preorder node IDs, complete-class owner IDs, persistent ordered
snapshots and owner-tagged fresh adjacency generations. Each node is
pushed once and completed once. Only the current merge's short fresh
fragment is traversed; accumulated node and event arrays are threaded
through the traversal without recursive concatenation. -/
namespace REWB.MaskedOrdered.Owner
open REWB.MaskedEventBudget (Edge)
open REWB.BoundaryTrie (Key)
abbrev Trie := REWB.BoundaryTrie.Tree
variable {h n : Nat}

structure Parent where
  depth : Nat
  owner : Nat
  deriving Repr,DecidableEq

def select (parent : Option Parent) (depth id : Nat) : Nat :=
  match parent with
  | none => id
  | some p => if p.depth<depth then id else p.owner

theorem select_equal (depth owner id : Nat) : select (some ⟨depth,owner⟩) depth id=owner := by
  simp [select]

theorem select_strict (parent : Parent) (depth id : Nat) (hd : parent.depth<depth) :
    select (some parent) depth id=id := by simp [select,hd]

structure Event where
  owner : Nat
  edge : Edge
  deriving Repr,DecidableEq

structure Record (h : Nat) where
  depth : Nat
  owner : Nat
  children : Option (Nat×Nat)
  state : State h
  deriving Repr

structure Store (h : Nat) where
  nodes : Array (Record h) := #[]
  events : Array Event := #[]
  work : Nat := 0
  deriving Repr

def emit (owner : Nat) : List Edge→Array Event→Array Event×Nat
  | [],out => (out,1)
  | e::es,out =>
    let r:=emit owner es (out.push ⟨owner,e⟩)
    (r.1,r.2+3)

theorem emit_list (owner : Nat) (es : List Edge) (out : Array Event) :
    (emit owner es out).1.toList=out.toList++es.map (fun e=>⟨owner,e⟩) := by
  induction es generalizing out with
  | nil => simp [emit]
  | cons e es ih =>
    simp only [emit,ih,Array.push_toList,List.map_cons,List.append_assoc,List.singleton_append]

theorem emit_size (owner : Nat) (es : List Edge) (out : Array Event) :
    (emit owner es out).1.size=out.size+es.length := by
  have hh:=congrArg List.length (emit_list owner es out)
  simpa only [Array.length_toList,List.length_append,List.length_map] using hh

theorem emit_work (owner : Nat) (es : List Edge) (out : Array Event) :
    (emit owner es out).2=3*es.length+1 := by
  induction es generalizing out with
  | nil => rfl
  | cons e es ih => simp only [emit,ih,List.length_cons]; omega

theorem emit_mem (owner : Nat) (es : List Edge) (out : Array Event) (e : Event) :
    e∈(emit owner es out).1.toList ↔ e∈out.toList ∨ ∃x,x∈es ∧ e=⟨owner,x⟩ := by
  rw [emit_list,List.mem_append,List.mem_map]
  constructor
  · rintro (hh|⟨x,hx,he⟩)
    · exact Or.inl hh
    · exact Or.inr ⟨x,hx,he.symm⟩
  · rintro (hh|⟨x,hx,he⟩)
    · exact Or.inl hh
    · exact Or.inr ⟨x,hx,he.symm⟩

def emitTR (owner : Nat) : List Edge→Array Event→Nat→Array Event×Nat
  | [],out,work => (out,work)
  | e::es,out,work => emitTR owner es (out.push ⟨owner,e⟩) (work+3)

theorem emitTR_spec (owner : Nat) (es : List Edge) (out : Array Event) (work : Nat) :
    emitTR owner es out work=((emit owner es out).1,work+3*es.length) := by
  induction es generalizing out work with
  | nil => simp [emitTR,emit]
  | cons e es ih =>
    simp only [emitTR,ih,emit,List.length_cons]
    apply Prod.ext
    · rfl
    · dsimp only; omega

def tailEmit (owner : Nat) (es : List Edge) (out : Array Event) : Array Event×Nat :=
  emitTR owner es out 1

@[csimp] theorem emit_eq_tailEmit : emit=tailEmit := by
  funext owner es out
  rw [tailEmit,emitTR_spec]
  apply Prod.ext
  · rfl
  · simp only [emit_work]; omega

/-- Empty descriptors are retained as empty records. In a nonempty Good
trie they never occur below an internal node. No occurrence is invented. -/
def slots : Trie n Nat→Nat
  | .empty => 1
  | .leaf _ => 1
  | .node _ _ l r => slots l+slots r+1

def mass (t : Trie n Nat) : Nat := t.leaves.length

def light : Trie n Nat→Nat
  | .empty => 0
  | .leaf _ => 0
  | .node _ _ l r => light l+light r+min (mass l) (mass r)

def visit (cap : Nat) : Trie n Nat→Option Parent→Store h→State h×Store h
  | .empty,parent,s =>
    let id:=s.nodes.size
    let owner:=select parent 0 id
    let state:=State.empty h
    (state,{s with nodes:=s.nodes.push ⟨0,owner,none,state⟩,work:=s.work+12})
  | .leaf a,parent,s =>
    let id:=s.nodes.size
    let owner:=select parent a.length id
    let step:=add (State.empty h) cap a.start
    (step.1,⟨s.nodes.push ⟨a.length,owner,none,step.1⟩,s.events,s.work+step.2.work+12⟩)
  | .node _ d l r,parent,s =>
    let id:=s.nodes.size
    let owner:=select parent d id
    let next:=some (Parent.mk d owner)
    let pushed:={s with nodes:=s.nodes.push ⟨d,owner,none,State.empty h⟩,work:=s.work+12}
    let leftId:=pushed.nodes.size
    let a:=visit cap l next pushed
    let rightId:=a.2.nodes.size
    let b:=visit cap r next a.2
    let step:=merge cap a.1 b.1 {}
    let events:=emit owner step.2.fresh b.2.events
    (step.1,⟨b.2.nodes.setIfInBounds id ⟨d,owner,some (leftId,rightId),step.1⟩,
      events.1,b.2.work+step.2.work+events.2+8⟩)

def PositionsBounded (h : Nat) (t : Trie n Nat) : Prop :=
  ∀p,p∈MaskedRunDiscovery.positions t→p<2^h

theorem positions_left (stem : Key n Nat) (d : Nat) (l r : Trie n Nat)
    (hb : PositionsBounded h (.node stem d l r)) : PositionsBounded h l := by
  intro p hp
  exact hb p (by simpa only [MaskedRunDiscovery.positions,BoundaryTrie.Tree.leaves,List.map_append,List.mem_append]
    using (Or.inl hp : p∈MaskedRunDiscovery.positions l ∨ p∈MaskedRunDiscovery.positions r))

theorem positions_right (stem : Key n Nat) (d : Nat) (l r : Trie n Nat)
    (hb : PositionsBounded h (.node stem d l r)) : PositionsBounded h r := by
  intro p hp
  exact hb p (by simpa only [MaskedRunDiscovery.positions,BoundaryTrie.Tree.leaves,List.map_append,List.mem_append]
    using (Or.inr hp : p∈MaskedRunDiscovery.positions l ∨ p∈MaskedRunDiscovery.positions r))

theorem visit_valid (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (hc : cap=2^h) (hb : PositionsBounded h t) : (visit cap t parent s).1.Valid := by
  induction t generalizing parent s with
  | empty => exact State.empty_valid h
  | leaf a =>
    exact add_valid _ _ _ (State.empty_valid h) hc (hb a.start (by
      simp [MaskedRunDiscovery.positions,BoundaryTrie.Tree.leaves]))
  | node stem d l r il ir =>
    exact merge_valid _ _ _ _ (il _ _ (positions_left _ _ _ _ hb))
      (ir _ _ (positions_right _ _ _ _ hb)) hc

theorem visit_mem (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (hc : cap=2^h) (hb : PositionsBounded h t) (p : Nat) :
    p∈(visit cap t parent s).1.tree.entries ↔ p∈MaskedRunDiscovery.positions t := by
  induction t generalizing parent s with
  | empty => rfl
  | leaf a =>
    rw [visit,add_mem _ _ _ _ (State.empty_valid h) hc (hb a.start (by
      simp [MaskedRunDiscovery.positions,BoundaryTrie.Tree.leaves]))]
    simp [MaskedRunDiscovery.positions,BoundaryTrie.Tree.leaves,State.empty,Tree.entries]
  | node stem d l r il ir =>
    have hl:=positions_left _ _ _ _ hb
    have hr:=positions_right _ _ _ _ hb
    rw [visit,merge_mem _ _ _ _ (visit_valid _ _ _ _ hc hl)
      (visit_valid _ _ _ _ hc hr) hc,il _ _ hl,ir _ _ hr]
    simp only [MaskedRunDiscovery.positions,BoundaryTrie.Tree.leaves,List.map_append,List.mem_append]

theorem visit_count (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (hc : cap=2^h) (hb : PositionsBounded h t) (hn : (MaskedRunDiscovery.positions t).Nodup) :
    (visit cap t parent s).1.tree.count=mass t := by
  have hv:=visit_valid cap t parent s hc hb
  have hp:=nodup_perm _ _ (Tree.nodup _ _ hv.2.1) hn (visit_mem cap t parent s hc hb)
  rw [Tree.count_correct _ hv.1,hp.length_eq]
  simp only [MaskedRunDiscovery.positions,List.length_map,mass]

theorem visit_size (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h) :
    (visit cap t parent s).2.nodes.size=s.nodes.size+slots t := by
  induction t generalizing parent s with
  | empty => simp [visit,slots]
  | leaf a => simp [visit,slots]
  | node stem d l r il ir =>
    simp only [visit,Array.size_setIfInBounds,ir,il,Array.size_push,slots]
    omega

theorem visit_prefix (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (i : Nat) (hi : i<s.nodes.size) : (visit cap t parent s).2.nodes[i]?=s.nodes[i]? := by
  induction t generalizing parent s with
  | empty => simp only [visit,Array.getElem?_push,if_neg (by omega : i≠s.nodes.size)]
  | leaf a => simp only [visit,Array.getElem?_push,if_neg (by omega : i≠s.nodes.size)]
  | node stem d l r il ir =>
    simp only [visit]
    rw [Array.getElem?_setIfInBounds_ne (by omega : s.nodes.size≠i)]
    rw [ir _ _ (by simp only [visit_size,Array.size_push]; omega)]
    rw [il _ _ (by simp only [Array.size_push]; omega)]
    simp only [Array.getElem?_push,if_neg (by omega : i≠s.nodes.size)]

def childIds : Trie n Nat→Nat→Option (Nat×Nat)
  | .node _ _ l _,id => some (id+1,id+1+slots l)
  | _,_ => none

theorem visit_root (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h) :
    (visit cap t parent s).2.nodes[s.nodes.size]?=
      some ⟨t.depth,select parent t.depth s.nodes.size,childIds t s.nodes.size,
        (visit cap t parent s).1⟩ := by
  cases t with
  | empty => exact Array.getElem?_push_size
  | leaf a => exact Array.getElem?_push_size
  | node stem d l r =>
    simp only [visit]
    rw [Array.getElem?_setIfInBounds_self_of_lt (by simp only [visit_size,Array.size_push]; omega)]
    simp only [visit_size,Array.size_push,childIds,BoundaryTrie.Tree.depth]

theorem visit_events_mono (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (e : Event) (he : e∈s.events.toList) : e∈(visit cap t parent s).2.events.toList := by
  induction t generalizing parent s with
  | empty => exact he
  | leaf a => exact he
  | node stem d l r il ir =>
    apply (emit_mem _ _ _ e).mpr
    exact Or.inl (ir _ _ (il _ _ he))

theorem positions_nodup_left (stem : Key n Nat) (d : Nat) (l r : Trie n Nat)
    (hn : (MaskedRunDiscovery.positions (.node stem d l r)).Nodup) :
    (MaskedRunDiscovery.positions l).Nodup := by
  have hh : (MaskedRunDiscovery.positions l++MaskedRunDiscovery.positions r).Nodup := by
    simpa only [MaskedRunDiscovery.positions,BoundaryTrie.Tree.leaves,List.map_append] using hn
  exact (List.sublist_append_left _ _).nodup hh

theorem positions_nodup_right (stem : Key n Nat) (d : Nat) (l r : Trie n Nat)
    (hn : (MaskedRunDiscovery.positions (.node stem d l r)).Nodup) :
    (MaskedRunDiscovery.positions r).Nodup := by
  have hh : (MaskedRunDiscovery.positions l++MaskedRunDiscovery.positions r).Nodup := by
    simpa only [MaskedRunDiscovery.positions,BoundaryTrie.Tree.leaves,List.map_append] using hn
  exact (List.sublist_append_right _ _).nodup hh

def nodeBudget (h : Nat) : Nat := 28*h+32

theorem visit_work (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (hc : cap=2^h) (hb : PositionsBounded h t) (hn : (MaskedRunDiscovery.positions t).Nodup) :
    (visit cap t parent s).2.work≤s.work+slots t*nodeBudget h+light t*(importBudget h+6) := by
  induction t generalizing parent s with
  | empty => simp only [visit,slots,light,nodeBudget,Nat.one_mul,Nat.zero_mul,Nat.add_zero]; omega
  | leaf a =>
    have hh:=insert_work (State.empty h).tree cap a.start
    simp only [visit,add,slots,light,nodeBudget,Nat.one_mul,Nat.zero_mul,Nat.add_zero]
    omega
  | node stem d l r il ir =>
    let next:=some (Parent.mk d (select parent d s.nodes.size))
    let pushed : Store h:=⟨s.nodes.push ⟨d,select parent d s.nodes.size,none,State.empty h⟩,
      s.events,s.work+12⟩
    let a:=visit cap l next pushed
    let b:=visit cap r next a.2
    let step:=merge cap a.1 b.1 {}
    have hl:=positions_left _ _ _ _ hb
    have hr:=positions_right _ _ _ _ hb
    have hnl:=positions_nodup_left _ _ _ _ hn
    have hnr:=positions_nodup_right _ _ _ _ hn
    have hva:=visit_valid cap l next pushed hc hl
    have hvb:=visit_valid cap r next a.2 hc hr
    have hwa:=il next pushed hl hnl
    have hwb:=ir next a.2 hr hnr
    have hwm:=merge_work cap a.1 b.1 {} hva hvb
    have hfm:=merge_fresh cap a.1 b.1 {} hva hvb
    have hgm:=merge_ledger cap a.1 b.1 {} Ledger.empty_good
    have hfg:=hgm.1
    have hca : a.1.tree.count=mass l:=visit_count cap l next pushed hc hl hnl
    have hcb : b.1.tree.count=mass r:=visit_count cap r next a.2 hc hr hnr
    rw [hca,hcb] at hwm hfm
    have he:=emit_work (select parent d s.nodes.size) step.2.fresh b.2.events
    change _≤s.work+(slots l+slots r+1)*nodeBudget h+
      (light l+light r+min (mass l) (mass r))*(importBudget h+6)
    change b.2.work+step.2.work+
      (emit (select parent d s.nodes.size) step.2.fresh b.2.events).2+8≤_
    change a.2.work≤s.work+12+slots l*nodeBudget h+light l*(importBudget h+6) at hwa
    change b.2.work≤a.2.work+slots r*nodeBudget h+light r*(importBudget h+6) at hwb
    change step.2.work≤0+min (mass l) (mass r)*importBudget h+2 at hwm
    change step.2.freshCount≤0+2*min (mass l) (mass r) at hfm
    change step.2.freshCount=step.2.fresh.length at hfg
    simp only [Nat.add_mul,Nat.one_mul,Nat.mul_add] at hwa hwb ⊢
    have hbudget : 23≤nodeBudget h := by simp only [nodeBudget]; omega
    omega

theorem visit_events_bound (cap : Nat) (t : Trie n Nat) (parent : Option Parent) (s : Store h)
    (hc : cap=2^h) (hb : PositionsBounded h t) (hn : (MaskedRunDiscovery.positions t).Nodup) :
    (visit cap t parent s).2.events.size≤s.events.size+2*light t := by
  induction t generalizing parent s with
  | empty => exact Nat.le_refl _
  | leaf a => exact Nat.le_refl _
  | node stem d l r il ir =>
    let next:=some (Parent.mk d (select parent d s.nodes.size))
    let pushed : Store h:=⟨s.nodes.push ⟨d,select parent d s.nodes.size,none,State.empty h⟩,
      s.events,s.work+12⟩
    let a:=visit cap l next pushed
    let b:=visit cap r next a.2
    let step:=merge cap a.1 b.1 {}
    have hl:=positions_left _ _ _ _ hb
    have hr:=positions_right _ _ _ _ hb
    have hnl:=positions_nodup_left _ _ _ _ hn
    have hnr:=positions_nodup_right _ _ _ _ hn
    have hva:=visit_valid cap l next pushed hc hl
    have hvb:=visit_valid cap r next a.2 hc hr
    have hwa:=il next pushed hl hnl
    have hwb:=ir next a.2 hr hnr
    have hfm:=merge_fresh cap a.1 b.1 {} hva hvb
    have hgm:=(merge_ledger cap a.1 b.1 {} Ledger.empty_good).1
    have hca : a.1.tree.count=mass l:=visit_count cap l next pushed hc hl hnl
    have hcb : b.1.tree.count=mass r:=visit_count cap r next a.2 hc hr hnr
    rw [hca,hcb] at hfm
    change (emit (select parent d s.nodes.size) step.2.fresh b.2.events).1.size≤_
    rw [emit_size]
    change a.2.events.size≤s.events.size+2*light l at hwa
    change b.2.events.size≤a.2.events.size+2*light r at hwb
    change step.2.freshCount≤0+2*min (mass l) (mass r) at hfm
    change step.2.freshCount=step.2.fresh.length at hgm
    simp only [light]
    omega

def run (h : Nat) (t : Trie n Nat) : State h×Store h :=
  let c:=capacity h
  visit c.1 t none {work:=c.2}

end REWB.MaskedOrdered.Owner
