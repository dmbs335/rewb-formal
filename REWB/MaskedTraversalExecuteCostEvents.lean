import REWB.MaskedTraversalExecuteCostDirty
import REWB.MaskedTraversalDriverCost

/-! The number of actual dirty-neighborhood events in the retained plan.
Each leaf contributes one insertion, each light import contributes its
real patch, and each crossed live record contributes one neighborhood.
The global bound follows the actual priority-queue balance and retained
heavy-child schedule. The definitions below are proof views of that plan,
not additional traversals performed by the public solver. -/
namespace REWB.MaskedTraversalExecute.Cost
open REWB.MaskedTraversalEdge REWB.MaskedTraversalFrontier REWB.BoundaryTrie
open REWB.MaskedTraversalDriver REWB.MaskedClusterLeaders
open REWB.MaskedRunDiscovery
open REWB.MaskedOrdered.Owner (mass slots light)
variable {h n σ : Nat}

def bandEvents : List (Band h)→Nat
  | []=>0
  | b::bs=>b.crossing.live.length+bandEvents bs

def initialEvents (step : Step h) : Nat :=
  match step.lowered.edge.initial with
  | none=>0
  | some crossed=>crossed.live.length

def stepEvents (step : Step h) : Nat := initialEvents step+bandEvents step.lowered.edge.path.bands

def marks : MaskedTraversalDriver.Plan h→Nat
  | .empty step=>stepEvents step
  | .leaf _ _ step=>1+stepEvents step
  | .node left right merged step=>marks left+marks right+merged.revPatches.length+stepEvents step

def nodes : MaskedTraversalDriver.Plan h→Nat
  | .empty _=>1
  | .leaf _ _ _=>1
  | .node left right _ _=>nodes left+nodes right+1

def scheduledBands : MaskedTraversalDriver.Plan h→Nat
  | .empty step=>step.lowered.edge.path.bands.length
  | .leaf _ _ step=>step.lowered.edge.path.bands.length
  | .node left right _ step=>scheduledBands left+scheduledBands right+step.lowered.edge.path.bands.length

theorem walk_events (capacity floor high : Nat) (s : MaskedClusterLeaders.State h)
    (hi : Invariant high s) (hf : Future high s) (hc : capacity=2^h) :
    bandEvents (MaskedTraversalEdge.walk capacity floor high s).bands≤
      (MaskedTraversalEdge.walk capacity floor high s).popped := by
  induction high using Nat.strongRecOn generalizing s with
  | ind high ih=>
    by_cases hh : floor<high
    · let boundary:=MaskedTraversalEdge.next floor high s
      let crossed:=MaskedClusterLeaders.shorten capacity boundary.length s
      have hlt : boundary.length<high := MaskedTraversalEdge.next_lt floor high s hh
      have hsi:=shorten_invariant capacity high boundary.length s hi hf hc (by omega)
      have hsf:=shorten_future capacity high boundary.length s hi hf (by omega)
      have tail:=ih boundary.length hlt crossed.state hsi hsf
      have live : crossed.live.length≤crossed.popped :=
        (MaskedThresholdEvents.shorten_work (h+1) boundary.length s.occurrences capacity s.queue hi.queueGood).2.1
      rw [MaskedTraversalEdge.walk,dif_pos hh]
      change crossed.live.length+bandEvents (MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).bands≤
        crossed.popped+(MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).popped
      exact Nat.add_le_add live tail
    · rw [MaskedTraversalEdge.walk,dif_neg hh]
      exact Nat.le_refl 0

theorem step_events (capacity floor high : Nat) (s : Frontier h)
    (hi : s.Valid high) (hc : capacity=2^h) :
    stepEvents ⟨floor,high,s,lower capacity floor high s⟩≤
      (lower capacity floor high s).edge.path.popped := by
  by_cases hh : floor<high
  · let first:=MaskedClusterLeaders.shorten capacity high s.state
    have hsi:=shorten_invariant capacity high high s.state hi.invariant hi.future hc (Nat.le_refl _)
    have hsf:=shorten_future capacity high high s.state hi.invariant hi.future (Nat.le_refl _)
    have tail:=walk_events capacity floor high first.state hsi hsf hc
    have live : first.live.length≤first.popped :=
      (MaskedThresholdEvents.shorten_work (h+1) high s.state.occurrences capacity s.state.queue hi.invariant.queueGood).2.1
    simp only [stepEvents,initialEvents,lower,MaskedTraversalEdge.run,if_pos hh]
    exact Nat.add_le_add live tail
  · simp only [stepEvents,initialEvents,lower,MaskedTraversalEdge.run,if_neg hh,bandEvents,Nat.zero_add,Nat.le_refl]

theorem nodes_build (capacity floor : Nat) (t : Tree n Nat) :
    nodes (MaskedTraversalDriver.build (h:=h) capacity floor t).plan=slots t := by
  induction t generalizing floor with
  | empty=>rfl
  | leaf=>rfl
  | node stem depth left right il ir=>
    change nodes (MaskedTraversalDriver.build capacity depth left).plan+
      nodes (MaskedTraversalDriver.build capacity depth right).plan+1=slots left+slots right+1
    rw [il,ir]

theorem bands_build (capacity floor : Nat) (t : Tree n Nat) :
    scheduledBands (MaskedTraversalDriver.build (h:=h) capacity floor t).plan=
      (MaskedTraversalDriver.build (h:=h) capacity floor t).bands := by
  induction t generalizing floor with
  | empty=>rfl
  | leaf=>simp only [MaskedTraversalDriver.build,MaskedTraversalDriver.finish,scheduledBands,Nat.zero_add]
  | node stem depth left right il ir=>
    change scheduledBands (MaskedTraversalDriver.build capacity depth left).plan+
      scheduledBands (MaskedTraversalDriver.build capacity depth right).plan+_=_
    rw [il,ir]
    rfl

theorem marks_build (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth) :
    marks (MaskedTraversalDriver.build (h:=h) capacity floor t).plan≤
      mass t+(MaskedTraversalDriver.build (h:=h) capacity floor t).imports+
        (MaskedTraversalDriver.build (h:=h) capacity floor t).popped := by
  induction t generalizing floor with
  | empty=>
    exact step_events capacity floor 0 (empty h) (empty_valid h 0) hc
  | leaf a=>
    have hp : a.start<capacity := by have hb:=a.bounded; omega
    let inserted:=insert capacity a.length a.start (empty h)
    have valid:=insert_valid capacity a.length a.start (empty h) (empty_valid h _) hc hp
    have events:=step_events capacity floor a.length inserted.frontier valid hc
    change 1+stepEvents ⟨floor,a.length,inserted.frontier,lower capacity floor a.length inserted.frontier⟩≤
      1+0+(0+(lower capacity floor a.length inserted.frontier).edge.path.popped)
    omega
  | node stem depth left right il ir=>
    have depths:=Tree.edge_depths f stem depth left right hg
    let a:=MaskedTraversalDriver.build (h:=h) capacity depth left
    let b:=MaskedTraversalDriver.build (h:=h) capacity depth right
    let merged:=MaskedTraversalFrontier.merge capacity depth a.frontier b.frontier
    have va:=build_valid capacity depth f left hg.1 hc hn depths.1
    have vb:=build_valid capacity depth f right hg.2.1 hc hn depths.2
    have vm:=merge_valid capacity depth a.frontier b.frontier va vb hc
    have em:=step_events capacity floor depth merged.frontier vm hc
    have patches : merged.revPatches.length=merged.imports :=
      (merge_measured capacity depth a.frontier b.frontier va vb hc).2.2.2.2
    have ha:=il depth hg.1 depths.1
    have hb:=ir depth hg.2.1 depths.2
    simp only [mass,Tree.leaves,List.length_append]
    change marks a.plan+marks b.plan+merged.revPatches.length+
      stepEvents ⟨floor,depth,merged.frontier,lower capacity floor depth merged.frontier⟩≤
      mass left+mass right+(a.imports+b.imports+merged.imports)+
        (a.popped+b.popped+(lower capacity floor depth merged.frontier).edge.path.popped)
    change marks a.plan≤mass left+a.imports+a.popped at ha
    change marks b.plan≤mass right+b.imports+b.popped at hb
    omega

theorem build_volume (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth)
    (distinct : (positions t).Nodup) :
    marks (MaskedTraversalDriver.build (h:=h) capacity floor t).plan≤5*(light t+mass t) ∧
      scheduledBands (MaskedTraversalDriver.build (h:=h) capacity floor t).plan≤4*(light t+mass t)+slots t := by
  have actual:=marks_build capacity floor f t hg hc hn hf
  have measured:=build_measured capacity floor f t hg hc hn hf
  have imports:=build_imports capacity floor f t hg hc hn hf distinct
  have generated:=measured.generations
  have balance:=measured.balance
  have bands:=measured.bands
  rw [imports] at actual generated
  rw [bands_build]
  constructor <;> omega

theorem suffix_volume (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat) (hn : text.size<2^h) :
    let plan:=(MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan
    marks plan≤5*((text.size+1)*(text.size+1).log2+(text.size+1)) ∧
      scheduledBands plan≤4*((text.size+1)*(text.size+1).log2+(text.size+1))+2*(text.size+1) ∧
      nodes plan≤2*(text.size+1) := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have good : t.Good (ArrayText.read text fallback) := (Build.run_correct text fallback (suffixKeys text.size)).2.1
  have volume:=build_volume (MaskedOrdered.capacity h).1 0 _ t good (MaskedOrdered.capacity_value h) hn
    (Nat.zero_le _) (MaskedRunTrieBridge.suffix_positions_nodup text fallback)
  have shape:=MaskedRunOwnerCost.suffix_shape text fallback
  have hm:=Nat.mul_le_mul_left 5 (Nat.add_le_add shape.2.2 (Nat.le_of_eq shape.2.1))
  have hb:=Nat.mul_le_mul_left 4 (Nat.add_le_add shape.2.2 (Nat.le_of_eq shape.2.1))
  change marks (MaskedTraversalDriver.build (MaskedOrdered.capacity h).1 0 t).plan≤_ ∧
    scheduledBands (MaskedTraversalDriver.build (MaskedOrdered.capacity h).1 0 t).plan≤_ ∧
      nodes (MaskedTraversalDriver.build (MaskedOrdered.capacity h).1 0 t).plan≤_
  rw [nodes_build]
  exact ⟨Nat.le_trans volume.1 hm,Nat.le_trans volume.2 (Nat.add_le_add hb shape.1),shape.1⟩

end REWB.MaskedTraversalExecute.Cost
