import REWB.MaskedThresholdQueueDrain
import REWB.MaskedOrderedLifecycle
import REWB.MaskedRunDiscoveryEvents

/-! Concrete density/overlap records from actual ordered insertion.
Only freshly emitted edges are enqueued. Old queue records are retained
and later validated by membership/successor queries; no scan rebuilds
the thresholds of an unchanged occurrence set.
-/
namespace REWB.MaskedThresholdEvents
open REWB.MaskedEventBudget (Edge Threshold thresholds)
open REWB.MaskedThresholdQueue

abbrev Queue := Tree Threshold

def pack (e : Threshold) : Entry Threshold := ⟨e.level,e⟩

def pushLoop (h cap : Nat) : List Threshold → Queue → Nat → Queue × Nat
  | [],q,work => (q,work+1)
  | e::es,q,work =>
    let next:=insert h cap 0 (pack e) q
    pushLoop h cap es next.1 (work+next.2+3)

theorem pushLoop_spec (h cap : Nat) (es : List Threshold) (q : Queue) (work : Nat)
    (hc : cap=2^h) (hq : Good h 0 q) (he : ∀e,e∈es → e.level<cap) :
    Good h 0 (pushLoop h cap es q work).1 ∧
      (entries (pushLoop h cap es q work).1).Perm (es.map pack++entries q) ∧
      count (pushLoop h cap es q work).1=count q+es.length ∧
      (pushLoop h cap es q work).2≤work+(12*h+8)*es.length+1 := by
  induction es generalizing q work with
  | nil => simp only [pushLoop,List.map_nil,List.nil_append,List.length_nil,Nat.add_zero,
      Nat.mul_zero]; exact ⟨hq,List.Perm.refl _,by trivial,Nat.le_refl _⟩
  | cons e es ih =>
    have hs:=insert_spec h cap 0 (pack e) q hc hq
      ⟨Nat.zero_le _,by simpa only [pack,Nat.zero_add] using he e List.mem_cons_self⟩
    have ht:=ih (insert h cap 0 (pack e) q).1 (work+(insert h cap 0 (pack e) q).2+3)
      hs.1 (fun x hx=>he x (List.mem_cons_of_mem e hx))
    simp only [pushLoop]
    refine ⟨ht.1,?_,?_,?_⟩
    · have hp:=ht.2.1.trans (hs.2.1.append_left (es.map pack))
      have hp':=hp.trans List.perm_middle
      simpa only [List.map_cons,List.cons_append] using hp'
    · have hcount:=ht.2.2.1
      rw [hs.2.2.1] at hcount
      simp only [List.length_cons]
      omega
    · have hw:=ht.2.2.2
      have hi:=hs.2.2.2
      simp only [List.length_cons,Nat.mul_succ]
      omega

def pushEdges (h cap : Nat) (es : List Edge) (q : Queue) : Queue × Nat :=
  pushLoop h cap (es.flatMap thresholds) q (3*es.length)

theorem threshold_length (es : List Edge) : (es.flatMap thresholds).length=2*es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,thresholds,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem threshold_bounded (cap : Nat) (es : List Edge)
    (he : ∀e,e∈es → e.2<cap) (e : Threshold) (hm : e∈es.flatMap thresholds) : e.level<2*cap := by
  obtain ⟨edge,hedge,hm⟩:=List.mem_flatMap.mp hm
  have hb:=he edge hedge
  simp only [thresholds,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl <;> dsimp only <;> omega

theorem pushEdges_spec (h cap : Nat) (es : List Edge) (q : Queue)
    (hc : cap=2^h) (hq : Good (h+1) 0 q) (he : ∀e,e∈es → e.2<cap) :
    Good (h+1) 0 (pushEdges (h+1) (2*cap) es q).1 ∧
      (entries (pushEdges (h+1) (2*cap) es q).1).Perm
        ((es.flatMap thresholds).map pack++entries q) ∧
      count (pushEdges (h+1) (2*cap) es q).1=count q+2*es.length ∧
      (pushEdges (h+1) (2*cap) es q).2≤(24*h+43)*es.length+1 := by
  have hcap : 2*cap=2^(h+1) := by rw [hc,Nat.pow_succ,Nat.mul_comm]
  have hh:=pushLoop_spec (h+1) (2*cap) (es.flatMap thresholds) q (3*es.length) hcap hq
    (threshold_bounded cap es he)
  simp only [threshold_length] at hh
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_⟩
  have hw:=hh.2.2.2
  change (pushLoop (h+1) (2*cap) (es.flatMap thresholds) q (3*es.length)).2≤_
  have heq : (12*(h+1)+8)*(2*es.length)+3*es.length=(24*h+43)*es.length := by
    rw [←Nat.mul_assoc,←Nat.add_mul]
    congr 1
    omega
  omega

structure Added (h : Nat) where
  insertion : MaskedOrdered.Insertion h
  queue : Queue
  generated : Nat
  work : Nat
  deriving Repr

def add (h cap p : Nat) (t : MaskedOrdered.Tree h) (q : Queue) : Added h :=
  let step:=MaskedOrdered.insert t cap p
  let pushed:=pushEdges (h+1) (2*cap) step.fresh q
  ⟨step,pushed.1,2*step.fresh.length,step.work+pushed.2+5⟩

theorem fresh_bound {h : Nat} (cap p : Nat) (t : MaskedOrdered.Tree h)
    (hg : t.Good) (hf : t.Fits 0) (hc : cap=2^h) (hp : p<cap)
    (e : Edge) (he : e∈(MaskedOrdered.insert t cap p).fresh) : e.2<cap := by
  have hpow : p<2^h := by rwa [hc] at hp
  obtain ⟨pre,post,hafter,_⟩:=MaskedOrdered.insert_edge_repair t cap p hg hf hc hpow
  have hm : e∈MaskedEventBudget.edges (MaskedOrdered.insert t cap p).tree.entries := by
    rw [hafter]
    exact List.mem_append_left _ (List.mem_append_right _ he)
  have hend:=MaskedRunDiscovery.edge_members _ e.1 e.2 hm
  have hfits:=MaskedOrdered.insert_fits t cap p hf hc hpow
  have hb:=MaskedOrdered.Tree.within _ 0 hfits e.2 hend.2
  rw [hc]
  omega

theorem add_spec (h cap p : Nat) (t : MaskedOrdered.Tree h) (q : Queue)
    (hg : t.Good) (hf : t.Fits 0) (hc : cap=2^h) (hp : p<cap) (hq : Good (h+1) 0 q) :
    Good (h+1) 0 (add h cap p t q).queue ∧
      (entries (add h cap p t q).queue).Perm
        (((MaskedOrdered.insert t cap p).fresh.flatMap thresholds).map pack++entries q) ∧
      count (add h cap p t q).queue=count q+(add h cap p t q).generated ∧
      (add h cap p t q).generated≤4 ∧ (add h cap p t q).work≤76*h+110 := by
  have hs:=pushEdges_spec h cap (MaskedOrdered.insert t cap p).fresh q hc hq
    (fresh_bound cap p t hg hf hc hp)
  have hi:=MaskedOrdered.insert_work t cap p
  have hfresh:=MaskedOrdered.insert_fresh_bound t cap p
  dsimp only [add]
  refine ⟨hs.1,hs.2.1,hs.2.2.1,by omega,?_⟩
  have hmul:=Nat.mul_le_mul_left (24*h+43) hfresh
  have hw:=hs.2.2.2
  omega

end REWB.MaskedThresholdEvents
