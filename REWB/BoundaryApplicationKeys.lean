import REWB.BoundaryApplicationRange
import REWB.LCSTable

/-! Actual fixed-end source/target descriptors in one reversed text.
Sources are prefixes ending at a≤g; targets are factors starting at g
and ending at t≥g. Their endpoint records remain separate even when
their represented strings are identical or empty. -/
namespace REWB.BoundaryApplication
open REWB.BoundaryTrie
open REWB.Periodic
open REWB.Spec (slice)
variable {α : Type} {σ n : Nat}

inductive Endpoint (n : Nat) where
  | source : Fin (n+1)→Endpoint n
  | target : Fin (n+1)→Endpoint n
  deriving DecidableEq, Repr

def ValidKey (g : Nat) (a : Key n (Endpoint n)) : Prop :=
  match a.record with
  | .source p => p.val≤g ∧ a.start=n-p.val ∧ a.length=p.val
  | .target p => g≤p.val ∧ a.start=n-p.val ∧ a.length=p.val-g

def sourceKeys (n g : Nat) (hg : g≤n) : List (Key n (Endpoint n)) :=
  List.ofFn fun i : Fin (g+1)=>
    ⟨n-i.val,i.val,by have hh:=i.isLt; omega,.source ⟨i.val,by have hh:=i.isLt; omega⟩⟩

def targetKeys (n g : Nat) (hg : g≤n) : List (Key n (Endpoint n)) :=
  List.ofFn fun i : Fin (n-g+1)=>
    ⟨n-(g+i.val),i.val,by have hh:=i.isLt; omega,
      .target ⟨g+i.val,by have hh:=i.isLt; omega⟩⟩

def keys (n g : Nat) (hg : g≤n) : List (Key n (Endpoint n)) :=
  sourceKeys n g hg++targetKeys n g hg

theorem keys_length (n g : Nat) (hg : g≤n) : (keys n g hg).length=n+2 := by
  simp only [keys,sourceKeys,targetKeys,List.length_append,List.length_ofFn]
  omega

theorem keys_valid (n g : Nat) (hg : g≤n) (a : Key n (Endpoint n))
    (ha : a∈keys n g hg) : ValidKey g a := by
  rcases List.mem_append.mp ha with hs | ht
  · obtain ⟨i,hi⟩:=List.mem_ofFn.mp hs
    subst a
    change i.val≤g ∧ _ ∧ _
    exact ⟨by have hh:=i.isLt; omega,rfl,rfl⟩
  · obtain ⟨i,hi⟩:=List.mem_ofFn.mp ht
    subst a
    change g≤g+i.val ∧ _ ∧ i.val=g+i.val-g
    exact ⟨by omega,rfl,by omega⟩

theorem source_mem (n g : Nat) (hg : g≤n) (a : Fin (n+1)) (ha : a.val≤g) :
    ∃k,k∈keys n g hg ∧ k.record=.source a := by
  let i : Fin (g+1):=⟨a.val,by omega⟩
  refine ⟨⟨n-a.val,a.val,by have hh:=a.isLt; omega,.source a⟩,?_,rfl⟩
  apply List.mem_append_left
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem target_mem (n g : Nat) (hg : g≤n) (t : Fin (n+1)) (ht : g≤t.val) :
    ∃k,k∈keys n g hg ∧ k.record=.target t := by
  let i : Fin (n-g+1):=⟨t.val-g,by have hh:=t.isLt; omega⟩
  let pos : Fin (n+1):=⟨g+i.val,by have hh:=i.isLt; omega⟩
  have hp : pos=t := Fin.ext (by dsimp only [pos,i]; omega)
  refine ⟨⟨n-pos.val,i.val,by have hh:=i.isLt; dsimp only [pos]; omega,.target pos⟩,?_,?_⟩
  · apply List.mem_append_right
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · change Endpoint.target pos=Endpoint.target t
    rw [hp]

def reversed (w : Word (Fin σ)) : Array (Fin σ) := w.reverse.toArray

theorem reversed_size (w : Word (Fin σ)) : (reversed w).size=w.length := by
  simp only [reversed,List.size_toArray,List.length_reverse]

/-- Reversal is materialized once; this cast changes only the erased
bound proof in each descriptor. -/
def reverseKeys (w : Word (Fin σ)) (g : Nat) (hg : g≤w.length) :
    List (Key (reversed w).size (Endpoint w.length)) :=
  (keys w.length g hg).map fun a=>⟨a.start,a.length,by rw [reversed_size]; exact a.bounded,a.record⟩

def originalKey (w : Word (Fin σ)) (a : Key (reversed w).size (Endpoint w.length)) :
    Key w.length (Endpoint w.length) :=
  ⟨a.start,a.length,by have hh:=a.bounded; have hn:=reversed_size w; omega,a.record⟩

theorem original_reverseKeys (w : Word (Fin σ)) (g : Nat) (hg : g≤w.length) :
    (reverseKeys w g hg).map (originalKey w)=keys w.length g hg := by
  simp only [reverseKeys,List.map_map]
  conv => rhs; rw [← List.map_id (keys w.length g hg)]
  apply congrArg (fun f=>(keys w.length g hg).map f)
  funext a
  cases a
  rfl

theorem reverseKeys_length (w : Word (Fin σ)) (g : Nat) (hg : g≤w.length) :
    (reverseKeys w g hg).length=w.length+2 := by
  simp only [reverseKeys,List.length_map,keys_length]

theorem reverseKeys_valid (w : Word (Fin σ)) (g : Nat) (hg : g≤w.length)
    (a : Key (reversed w).size (Endpoint w.length)) (ha : a∈reverseKeys w g hg) :
    ValidKey g (originalKey w a) := by
  have hh : originalKey w a∈(reverseKeys w g hg).map (originalKey w) :=
    List.mem_map.mpr ⟨a,ha,rfl⟩
  rw [original_reverseKeys] at hh
  exact keys_valid w.length g hg _ hh

def reverseText (w : Word (Fin σ)) (fallback : Fin σ) : Nat→Fin σ :=
  ArrayText.read (reversed w) fallback

theorem reverse_segment (w : Word (Fin σ)) (fallback : Fin σ) (a L : Nat)
    (ha : a+L≤w.length) :
    (segment (reverseText w fallback) a L).reverse=
      slice w (w.length-a-L) (w.length-a) := by
  have hs:=ArrayText.segment_word w.reverse fallback a L (by simpa only [List.length_reverse] using ha)
  change segment (reverseText w fallback) a L=(w.reverse.drop a).take L at hs
  have he : w.length-(w.length-a)=a := by omega
  have hr:=LCSTable.rev_end_take w (w.length-a) L (by omega) (by omega)
  rw [he] at hr
  rw [hs,hr,List.reverse_reverse]

def edgeWord (w : Word (Fin σ)) (start parent child : Nat) : Word (Fin σ) :=
  slice w (w.length-start-child) (w.length-start-parent)

theorem edge_reverse (w : Word (Fin σ)) (fallback : Fin σ) (start parent child : Nat)
    (hp : parent≤child) (hc : start+child≤w.length) :
    (segment (reverseText w fallback) (start+parent) (child-parent)).reverse=
      edgeWord w start parent child := by
  rw [reverse_segment w fallback (start+parent) (child-parent) (by omega)]
  unfold edgeWord
  congr 1 <;> omega

theorem edge_equal (w : Word (Fin σ)) (fallback : Fin σ)
    (a b : Key (reversed w).size (Endpoint w.length)) (parent child : Nat)
    (hp : parent≤child) (hc : Key.Common (reverseText w fallback) a b child) :
    edgeWord w a.start parent child=edgeWord w b.start parent child := by
  have ha : a.start+child≤w.length := by
    have hh:=a.bounded
    have hn:=reversed_size w
    have hh':=hc.1
    omega
  have hb : b.start+child≤w.length := by
    have hh:=b.bounded
    have hn:=reversed_size w
    have hh':=hc.2.1
    omega
  rw [← edge_reverse w fallback a.start parent child hp ha,
      ← edge_reverse w fallback b.start parent child hp hb]
  apply congrArg List.reverse
  exact LCEIndex.agree_tail (reverseText w fallback) w.length a.start b.start child parent
    (child-parent) ⟨ha,hb,hc.2.2⟩ (by omega)

theorem target_edge (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (a b : Key (reversed w).size (Endpoint w.length)) (t : Fin (w.length+1))
    (hv : ValidKey g (originalKey w b)) (ht : b.record=.target t)
    (parent child : Nat) (hp : parent≤child)
    (hc : Key.Common (reverseText w fallback) a b child) :
    edgeWord w a.start parent child=slice w (t.val-child) (t.val-parent) := by
  rw [edge_equal w fallback a b parent child hp hc]
  simp only [ValidKey,originalKey] at hv
  rw [ht] at hv
  unfold edgeWord
  rw [hv.2.1]
  have he : w.length-(w.length-t.val)=t.val := by have hh:=t.isLt; omega
  rw [he]

end REWB.BoundaryApplication
