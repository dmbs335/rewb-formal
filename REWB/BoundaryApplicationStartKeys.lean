import REWB.BoundaryApplicationKeys
import REWB.BoundaryApplicationStartPartial

/-! Forward descriptors for the fixed-target-start boundary case. All
sources start at i≤g and end at g; all targets start at j≥g and end at n.
Only (start,length,record) is stored for each key, in one materialized
forward text. Empty descriptors and duplicate words remain terminals. -/
namespace REWB.BoundaryApplication.StartKeys
open REWB.BoundaryTrie
open REWB.Periodic
open REWB.Spec (slice)
variable {σ n : Nat}

def ValidKey (g : Nat) (a : Key n (Endpoint n)) : Prop :=
  match a.record with
  | .source p => p.val≤g ∧ a.start=p.val ∧ a.length=g-p.val
  | .target p => g≤p.val ∧ a.start=p.val ∧ a.length=n-p.val

def sourceKeys (n g : Nat) (hg : g≤n) : List (Key n (Endpoint n)) :=
  List.ofFn fun i : Fin (g+1)=>
    ⟨i.val,g-i.val,by have hh:=i.isLt; omega,
      .source ⟨i.val,by have hh:=i.isLt; omega⟩⟩

def targetKeys (n g : Nat) (hg : g≤n) : List (Key n (Endpoint n)) :=
  List.ofFn fun i : Fin (n-g+1)=>
    ⟨g+i.val,n-(g+i.val),by have hh:=i.isLt; omega,
      .target ⟨g+i.val,by have hh:=i.isLt; omega⟩⟩

def keys (n g : Nat) (hg : g≤n) := sourceKeys n g hg++targetKeys n g hg

theorem keys_length (n g : Nat) (hg : g≤n) : (keys n g hg).length=n+2 := by
  simp only [keys,sourceKeys,targetKeys,List.length_append,List.length_ofFn]
  omega

theorem keys_valid (n g : Nat) (hg : g≤n) (a : Key n (Endpoint n))
    (ha : a∈keys n g hg) : ValidKey g a := by
  rcases List.mem_append.mp ha with hs | ht
  · obtain ⟨i,hi⟩:=List.mem_ofFn.mp hs
    subst a
    change i.val≤g ∧ i.val=i.val ∧ g-i.val=g-i.val
    exact ⟨by have hh:=i.isLt; omega,rfl,rfl⟩
  · obtain ⟨i,hi⟩:=List.mem_ofFn.mp ht
    subst a
    change g≤g+i.val ∧ g+i.val=g+i.val ∧ n-(g+i.val)=n-(g+i.val)
    exact ⟨by omega,rfl,rfl⟩

theorem source_mem (n g : Nat) (hg : g≤n) (i : Fin (n+1)) (hi : i.val≤g) :
    ∃k,k∈keys n g hg ∧ k.record=.source i := by
  refine ⟨⟨i.val,g-i.val,by omega,.source i⟩,?_,rfl⟩
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨⟨i.val,by omega⟩,rfl⟩)

theorem target_mem (n g : Nat) (hg : g≤n) (j : Fin (n+1)) (hj : g≤j.val) :
    ∃k,k∈keys n g hg ∧ k.record=.target j := by
  let i : Fin (n-g+1):=⟨j.val-g,by have hh:=j.isLt; omega⟩
  let p : Fin (n+1):=⟨g+i.val,by have hh:=i.isLt; omega⟩
  have hp : p=j := Fin.ext (by dsimp only [p,i]; omega)
  refine ⟨⟨p.val,n-p.val,by have hh:=p.isLt; omega,.target p⟩,?_,?_⟩
  · exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · change Endpoint.target p=Endpoint.target j
    rw [hp]

abbrev KeyFor (w : Word (Fin σ)) := Key w.toArray.size (Endpoint w.length)
abbrev TrieFor (w : Word (Fin σ)) := BoundaryTrie.Tree w.toArray.size (Endpoint w.length)

def forwardKeys (w : Word (Fin σ)) (g : Nat) (hg : g≤w.length) : List (KeyFor w) :=
  (keys w.length g hg).map fun a=>⟨a.start,a.length,by simpa only [List.size_toArray] using a.bounded,a.record⟩

def originalKey (w : Word (Fin σ)) (a : KeyFor w) : Key w.length (Endpoint w.length) :=
  ⟨a.start,a.length,by simpa only [List.size_toArray] using a.bounded,a.record⟩

theorem original_forwardKeys (w : Word (Fin σ)) (g : Nat) (hg : g≤w.length) :
    (forwardKeys w g hg).map (originalKey w)=keys w.length g hg := by
  simp only [forwardKeys,List.map_map]
  conv => rhs; rw [← List.map_id (keys w.length g hg)]
  apply congrArg (fun f=>(keys w.length g hg).map f)
  funext a
  cases a
  rfl

theorem forwardKeys_length (w : Word (Fin σ)) (g : Nat) (hg : g≤w.length) :
    (forwardKeys w g hg).length=w.length+2 := by
  simp only [forwardKeys,List.length_map,keys_length]

theorem forwardKeys_valid (w : Word (Fin σ)) (g : Nat) (hg : g≤w.length)
    (a : KeyFor w) (ha : a∈forwardKeys w g hg) : ValidKey g (originalKey w a) := by
  have hh : originalKey w a∈(forwardKeys w g hg).map (originalKey w) := List.mem_map.mpr ⟨a,ha,rfl⟩
  rw [original_forwardKeys] at hh
  exact keys_valid w.length g hg _ hh

def text (w : Word (Fin σ)) (fallback : Fin σ) : Nat→Fin σ := ArrayText.read w.toArray fallback

theorem segment_slice (w : Word (Fin σ)) (fallback : Fin σ) (s L : Nat) (hs : s+L≤w.length) :
    segment (text w fallback) s L=slice w s (s+L) := by
  change segment (ArrayText.read w.toArray fallback) s L= _
  rw [ArrayText.segment_word w fallback s L hs]
  simp only [slice,Nat.add_sub_cancel_left]

def edgeWord (w : Word (Fin σ)) (start parent child : Nat) := slice w (start+parent) (start+child)

theorem edge_segment (w : Word (Fin σ)) (fallback : Fin σ) (s p d : Nat)
    (hp : p≤d) (hd : s+d≤w.length) :
    segment (text w fallback) (s+p) (d-p)=edgeWord w s p d := by
  rw [segment_slice w fallback (s+p) (d-p) (by omega)]
  have hh : s+p+(d-p)=s+d := by omega
  rw [hh]
  rfl

theorem edge_equal (w : Word (Fin σ)) (fallback : Fin σ) (a b : KeyFor w) (p d : Nat)
    (hp : p≤d) (hc : Key.Common (text w fallback) a b d) :
    edgeWord w a.start p d=edgeWord w b.start p d := by
  have ha : a.start+d≤w.length := by
    have hh:=a.bounded
    simp only [List.size_toArray] at hh
    have hh':=hc.1
    omega
  have hb : b.start+d≤w.length := by
    have hh:=b.bounded
    simp only [List.size_toArray] at hh
    have hh':=hc.2.1
    omega
  rw [← edge_segment w fallback a.start p d hp ha,← edge_segment w fallback b.start p d hp hb]
  exact LCEIndex.agree_tail (text w fallback) w.length a.start b.start d p (d-p)
    ⟨ha,hb,hc.2.2⟩ (by omega)

def representative (w : Word (Fin σ)) : TrieFor w→KeyFor w
  | .empty => ⟨0,0,by omega,.source ⟨0,Nat.zero_lt_succ _⟩⟩
  | .leaf a => a
  | .node a _ _ _ => a

theorem representative_mem (w : Word (Fin σ)) (fallback : Fin σ) (t : TrieFor w)
    (hg : t.Good (text w fallback)) (hn : t.leaves≠[]) : representative w t∈t.leaves := by
  cases t with
  | empty => exact False.elim (hn rfl)
  | leaf a => simp only [representative,BoundaryTrie.Tree.leaves,List.mem_singleton]
  | node a d l r => exact List.mem_append_left _ hg.2.2.2.2.1

theorem representative_common (w : Word (Fin σ)) (fallback : Fin σ) (t : TrieFor w)
    (hg : t.Good (text w fallback)) (a : KeyFor w) (ha : a∈t.leaves) :
    Key.Common (text w fallback) (representative w t) a t.depth := by
  cases t with
  | empty => cases ha
  | leaf b =>
    simp only [BoundaryTrie.Tree.leaves,List.mem_singleton] at ha
    subst a
    exact ⟨Nat.le_refl _,Nat.le_refl _,rfl⟩
  | node b d l r => exact hg.2.2.2.2.2.1 a ha

theorem representative_bound (w : Word (Fin σ)) (fallback : Fin σ) (t : TrieFor w)
    (hg : t.Good (text w fallback)) (hn : t.leaves≠[]) :
    (representative w t).start+t.depth≤w.length := by
  have hc:=representative_common w fallback t hg _ (representative_mem w fallback t hg hn)
  have hb:=(representative w t).bounded
  simp only [List.size_toArray] at hb
  have hh:=hc.1
  omega

def edge (C : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Range.Index C) (p : Nat) (t : TrieFor w) :=
  Range.query C idx ((representative w t).start+p) ((representative w t).start+t.depth)

theorem edge_run (C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (p : Nat)
    (t : TrieFor w) (hg : t.Good (text w fallback)) (hn : t.leaves≠[])
    (hp : p≤t.depth) (q : Fin C.stateCount) :
    (edge C w (Range.build C w) p t).map.get q=
      C.run q (edgeWord w (representative w t).start p t.depth) :=
  Range.query_correct C w _ _ (by omega) (representative_bound w fallback t hg hn) q

theorem edge_work (C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (p : Nat)
    (t : TrieFor w) (hg : t.Good (text w fallback)) (hn : t.leaves≠[])
    (hp : p≤t.depth) :
    (edge C w (Range.build C w) p t).work≤C.stateCount+8*(w.length.log2+2)+1 :=
  Range.query_work C w _ _ (by omega) (representative_bound w fallback t hg hn)

theorem source_edge (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (a b : KeyFor w) (i : Fin (w.length+1)) (hv : ValidKey g (originalKey w b))
    (ht : b.record=.source i) (p d : Nat) (hp : p≤d)
    (hc : Key.Common (text w fallback) a b d) :
    edgeWord w a.start p d=slice w (i.val+p) (i.val+d) := by
  rw [edge_equal w fallback a b p d hp hc]
  simp only [ValidKey,originalKey] at hv
  rw [ht] at hv
  simp only [edgeWord,hv.2.1]

theorem target_edge (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (a b : KeyFor w) (j : Fin (w.length+1)) (hv : ValidKey g (originalKey w b))
    (ht : b.record=.target j) (p d : Nat) (hp : p≤d)
    (hc : Key.Common (text w fallback) a b d) :
    edgeWord w a.start p d=slice w (j.val+p) (j.val+d) := by
  rw [edge_equal w fallback a b p d hp hc]
  simp only [ValidKey,originalKey] at hv
  rw [ht] at hv
  simp only [edgeWord,hv.2.1]

end REWB.BoundaryApplication.StartKeys
