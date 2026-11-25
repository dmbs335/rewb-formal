import REWB.MaskedTraversalDriverCorrect

/-! Global accounting for the concrete geometric traversal.  Fresh
records are generated only by actual occurrence insertions; records are
either popped, retained in the final queue, or discarded with a completed
light child.  Numeric edge widths do not appear in the bound. -/
namespace REWB.MaskedTraversalDriver
open REWB.MaskedTraversalFrontier REWB.BoundaryTrie
open REWB.MaskedRunDiscovery (positions prepareSuffixes suffixKeys)
open REWB.MaskedOrdered.Owner (mass slots light)
variable {h n σ : Nat}

structure Measured (mass slots : Nat) (out : Built h) : Prop where
  generations : out.generated≤4*(out.imports+mass)
  balance : out.popped+out.discarded+MaskedThresholdQueue.count out.frontier.state.queue=out.generated
  bands : out.bands≤out.popped+slots
  work : out.work≤(129*h+158)*(out.imports+mass)+(98*h+176)*slots+
    (98*h+162)*out.popped+out.bands

structure BeforeMeasured (mass slots : Nat) (s : Frontier h) (out : Counters) : Prop where
  generations : out.generated≤4*(out.imports+mass)
  balance : out.popped+out.discarded+MaskedThresholdQueue.count s.state.queue=out.generated
  bands : out.bands≤out.popped+slots
  work : out.work≤(129*h+158)*(out.imports+mass)+(98*h+176)*slots+
    (98*h+162)*out.popped+out.bands+10

theorem finish_measured (capacity floor high : Nat) (s : Frontier h)
    (wrap : Step h→Plan h) (before : Counters) (mass slots : Nat)
    (hv : s.Valid high) (hc : capacity=2^h) (hm : BeforeMeasured mass slots s before) :
    Measured mass (slots+1) (finish capacity floor high s wrap before) := by
  have he:=MaskedTraversalEdge.run_measured capacity floor high s.state hv.invariant hv.future hc
  let edge:=MaskedTraversalEdge.run capacity floor high s.state
  have hq : edge.path.popped+MaskedThresholdQueue.count edge.path.state.queue=
      MaskedThresholdQueue.count s.state.queue := he.1
  have hb : edge.path.bands.length≤edge.path.popped+1 := he.2.1
  have hw : edge.path.work≤(98*h+162)*(edge.path.popped+1) := he.2.2
  refine ⟨hm.generations,?_,?_,?_⟩
  · change before.popped+edge.path.popped+before.discarded+
      MaskedThresholdQueue.count edge.path.state.queue=before.generated
    have h:=hm.balance
    omega
  · change before.bands+edge.path.bands.length≤before.popped+edge.path.popped+(slots+1)
    have h:=hm.bands
    omega
  · change before.work+edge.path.work+edge.path.bands.length+4≤
      (129*h+158)*(before.imports+mass)+(98*h+176)*(slots+1)+
        (98*h+162)*(before.popped+edge.path.popped)+(before.bands+edge.path.bands.length)
    have ht:=hm.work
    simp only [Nat.mul_add,Nat.mul_one] at hw ht ⊢
    omega

theorem build_measured (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth) :
    Measured (mass t) (slots t) (build (h:=h) capacity floor t) := by
  induction t generalizing floor with
  | empty =>
    apply finish_measured capacity floor 0 (empty h) .empty ⟨0,0,0,0,0,4⟩ 0 0
      (empty_valid h 0) hc
    exact ⟨by decide,rfl,by decide,by simp⟩
  | leaf a =>
    have hp : a.start<capacity := by have hb:=a.bounded; omega
    let leaf:=insert capacity a.length a.start (empty h)
    have hv:=insert_valid capacity a.length a.start (empty h) (empty_valid h _) hc hp
    have hm:=insert_measured capacity a.length a.start (empty h) (empty_valid h _) hc hp
    apply finish_measured capacity floor a.length leaf.frontier (.leaf a.start leaf)
      ⟨leaf.generated,0,0,0,0,leaf.work+4⟩ 1 0 hv hc
    refine ⟨hm.2.1,?_,Nat.le_refl 0,?_⟩
    · change 0+0+MaskedThresholdQueue.count leaf.frontier.state.queue=leaf.generated
      simp only [Nat.zero_add]
      simpa only [empty,MaskedClusterLeaders.empty,MaskedThresholdQueue.count,Nat.zero_add] using hm.2.2
    · change leaf.work+4≤(129*h+158)*(0+1)+(98*h+176)*0+(98*h+162)*0+0+10
      have hw : leaf.work≤129*h+153 := hm.1
      simp only [Nat.zero_add,Nat.mul_one,Nat.mul_zero,Nat.add_zero]
      omega
  | node stem depth left right il ir =>
    have hd:=Tree.edge_depths f stem depth left right hg
    let a:=build (h:=h) capacity depth left
    let b:=build (h:=h) capacity depth right
    let merged:=merge capacity depth a.frontier b.frontier
    have ha:=il depth hg.1 hd.1
    have hb:=ir depth hg.2.1 hd.2
    have hva:=build_valid capacity depth f left hg.1 hc hn hd.1
    have hvb:=build_valid capacity depth f right hg.2.1 hc hn hd.2
    have hvm:=merge_valid capacity depth a.frontier b.frontier hva hvb hc
    have hm:=merge_measured capacity depth a.frontier b.frontier hva hvb hc
    have hmg : merged.generated≤4*merged.imports := hm.2.1
    have hmw : merged.work≤(129*h+158)*merged.imports+6 := hm.2.2.1
    have hmq : MaskedThresholdQueue.count merged.frontier.state.queue+merged.discarded=
        MaskedThresholdQueue.count a.frontier.state.queue+MaskedThresholdQueue.count b.frontier.state.queue+
          merged.generated := hm.2.2.2.1
    simp only [mass,Tree.leaves,List.length_append,slots]
    change Measured (mass left+mass right) (slots left+slots right+1) _
    apply finish_measured capacity floor depth merged.frontier (.node a.plan b.plan merged)
      ⟨a.generated+b.generated+merged.generated,a.popped+b.popped,
        a.discarded+b.discarded+merged.discarded,a.imports+b.imports+merged.imports,
        a.bands+b.bands,a.work+b.work+merged.work+4⟩
      (mass left+mass right) (slots left+slots right) hvm hc
    refine ⟨?_,?_,?_,?_⟩
    · have hga : a.generated≤4*(a.imports+mass left) := ha.generations
      have hgb : b.generated≤4*(b.imports+mass right) := hb.generations
      change a.generated+b.generated+merged.generated≤
        4*(a.imports+b.imports+merged.imports+(mass left+mass right))
      omega
    · have hqa : a.popped+a.discarded+MaskedThresholdQueue.count a.frontier.state.queue=a.generated := ha.balance
      have hqb : b.popped+b.discarded+MaskedThresholdQueue.count b.frontier.state.queue=b.generated := hb.balance
      change a.popped+b.popped+(a.discarded+b.discarded+merged.discarded)+
        MaskedThresholdQueue.count merged.frontier.state.queue=a.generated+b.generated+merged.generated
      omega
    · have hba : a.bands≤a.popped+slots left := ha.bands
      have hbb : b.bands≤b.popped+slots right := hb.bands
      change a.bands+b.bands≤a.popped+b.popped+(slots left+slots right)
      omega
    · have hwa : a.work≤(129*h+158)*(a.imports+mass left)+(98*h+176)*slots left+
        (98*h+162)*a.popped+a.bands := ha.work
      have hwb : b.work≤(129*h+158)*(b.imports+mass right)+(98*h+176)*slots right+
        (98*h+162)*b.popped+b.bands := hb.work
      change a.work+b.work+merged.work+4≤
        (129*h+158)*(a.imports+b.imports+merged.imports+(mass left+mass right))+
        (98*h+176)*(slots left+slots right)+(98*h+162)*(a.popped+b.popped)+(a.bands+b.bands)+10
      simp only [Nat.mul_add] at hwa hwb ⊢
      omega

theorem build_imports (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth)
    (hd : (positions t).Nodup) : (build (h:=h) capacity floor t).imports=light t := by
  induction t generalizing floor with
  | empty => rfl
  | leaf => rfl
  | node stem depth left right il ir =>
    have hdepth:=Tree.edge_depths f stem depth left right hg
    have hnd : (positions left++positions right).Nodup := by
      simpa only [positions,Tree.leaves,List.map_append] using hd
    have hnl:=(List.pairwise_append.mp hnd).1
    have hnr:=(List.pairwise_append.mp hnd).2.1
    have hl:=build_valid capacity depth f left hg.1 hc hn hdepth.1
    have hr:=build_valid capacity depth f right hg.2.1 hc hn hdepth.2
    have hm:=(merge_measured capacity depth _ _ hl hr hc).1
    have hcl:=build_count capacity depth f left hg.1 hc hn hdepth.1 hnl
    have hcr:=build_count capacity depth f right hg.2.1 hc hn hdepth.2 hnr
    change (build (h:=h) capacity depth left).imports+(build (h:=h) capacity depth right).imports+
      (merge capacity depth (build (h:=h) capacity depth left).frontier
        (build (h:=h) capacity depth right).frontier).imports=
      light left+light right+min (mass left) (mass right)
    rw [il depth hg.1 hdepth.1 hnl,ir depth hg.2.1 hdepth.2 hnr,hm,hcl,hcr]
    rfl

theorem build_work (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth)
    (hd : (positions t).Nodup) :
    (build (h:=h) capacity floor t).work≤
      (521*h+810)*(light t+mass t)+(98*h+177)*slots t := by
  have hm:=build_measured capacity floor f t hg hc hn hf
  have hi:=build_imports capacity floor f t hg hc hn hf hd
  have hg:=hm.generations
  have hq:=hm.balance
  have hb:=hm.bands
  have hw:=hm.work
  rw [hi] at hg hw
  have hp : (build (h:=h) capacity floor t).popped≤4*(light t+mass t) := by omega
  have hpm:=Nat.mul_le_mul_left (98*h+163) hp
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at hpm hw ⊢
  simp only [Nat.mul_left_comm h 4] at hpm
  omega

theorem suffix_work (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat) (hn : text.size<2^h) :
    (run h (prepareSuffixes text fallback).trie.tree).work≤
      h+1+(521*h+810)*((text.size+1)*(text.size+1).log2+(text.size+1))+
        (196*h+354)*(text.size+1) := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have hg : t.Good (ArrayText.read text fallback) :=
    (Build.run_correct text fallback (suffixKeys text.size)).2.1
  have hw:=build_work (MaskedOrdered.capacity h).1 0 _ t hg (MaskedOrdered.capacity_value h) hn
    (Nat.zero_le _) (MaskedRunTrieBridge.suffix_positions_nodup text fallback)
  have hs:=MaskedRunOwnerCost.suffix_shape text fallback
  have hwm:=Nat.mul_le_mul_left (521*h+810)
    (Nat.add_le_add hs.2.2 (Nat.le_of_eq hs.2.1))
  have hws:=Nat.mul_le_mul_left (98*h+177) hs.1
  have hcap:=MaskedOrdered.capacity_work h
  change (build (MaskedOrdered.capacity h).1 0 t).work+(MaskedOrdered.capacity h).2≤_
  dsimp only [t] at hw ⊢
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] at hw hwm hws ⊢
  simp only [Nat.mul_left_comm h 2] at hws
  omega

end REWB.MaskedTraversalDriver
