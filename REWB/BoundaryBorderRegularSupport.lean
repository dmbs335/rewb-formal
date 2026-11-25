import REWB.BoundaryBorderRegularChoice
import REWB.BoundaryBorderDyadic

/-! Every choice returned by the actual text-built dyadic index has the
period certificate required by the regular acceptance layer. Proofs use
saved complete suffix classes and measured component geometry; neither
execution nor the theorem assumes an externally supplied class. -/
namespace REWB.BoundaryBorder.Regular
open REWB.Periodic REWB.MaskedRunDiscovery REWB.MaskedOrdered REWB.LCEIndex
variable {α : Type} {σ h : Nat}

def RowSupported (f : Nat→α) (a j : Nat) (row : Window.Selected) : Prop :=
  Supported f a j row.first ∧ Supported f a j row.second

def RowsSupported (f : Nat→α) (a j : Nat) (rows : List Window.Selected) : Prop :=
  ∀row,row∈rows→RowSupported f a j row

theorem option_supported (f : Nat→Fin σ) (n a j L hi : Nat) (xs : List Nat)
    (band : Option Window.Band) (hfull : Complete f n j L xs)
    (hv : ∀b,band=some b→Window.Valid f n L hi xs b) (hj : j+L≤n) :
    Supported f a j (Window.selectOption (prepare f n) n a j band).choice := by
  cases band with
  | none => trivial
  | some b =>
    have hb:=hv b rfl
    have hs:=Window.valid_seed f n j L hi xs b hfull hb
    exact select_supported f n b.first b.step b.first b.last a j hb.positive hs.1
      (by have hq:=hb.step_le; omega)

theorem window_supported (f : Nat→Fin σ) (n j L lo hi a : Nat) (t : Tree h) (capacity : Nat)
    (hg : Tree.Good t) (ht : Tree.Fits t 0) (hc : capacity=2^h)
    (hfull : Complete f n j L t.entries) (hL : 0<L) (hj : j+L≤n) :
    RowSupported f a j (Window.query (prepare f n) t capacity n L lo hi a j) := by
  constructor
  · exact option_supported f n a j L hi t.entries _ hfull
      (fun b hb=>(Window.extract_valid f n j L lo hi t capacity hg ht hc hfull hL b (Or.inl hb)).1) hj
  · exact option_supported f n a j L hi t.entries _ hfull
      (fun b hb=>(Window.extract_valid f n j L lo hi t capacity hg ht hc hfull hL b (Or.inr hb)).1) hj

theorem indexed_supported (text : Array (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (text.size+1)) (L lo hi : Nat) :
    RowSupported (ArrayText.read text fallback) a j.val
      (WindowIndex.query (WindowIndex.prepare text fallback) a j L lo hi) := by
  simp only [WindowIndex.query,WindowIndex.prepare_classes]
  split
  · rename_i hg
    cases ho : (MaskedSuffixClass.query (MaskedSuffixClass.prepare text fallback) j L).value with
    | none => simp only [ho,RowSupported,Supported,true_and]
    | some out =>
      have hH:=(MaskedSuffixClass.query_exists_iff text fallback j L).mp ⟨out,ho⟩
      have hv:=MaskedSuffixClass.query_sound text fallback j L hH out ho
      have hj : j.val+L≤text.size := by have hb:=j.isLt; omega
      simp only [ho]
      change RowSupported (ArrayText.read text fallback) a j.val
        (Window.query (MaskedSuffixClass.prepare text fallback).suffix.trie.prepared.ranks
          out.record.state.tree (WindowIndex.prepare text fallback).capacity text.size L lo hi a j.val)
      rw [MaskedSuffixClass.prepare_forward]
      exact window_supported _ text.size j.val L lo hi a _ _ hv.1.1 hv.1.2.1
        (WindowIndex.prepare_capacity text fallback) hv.2 hg.1 hj
  · exact ⟨True.intro,True.intro⟩

theorem scale_supported (text : Array (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (text.size+1)) (L : Nat) :
    RowSupported (ArrayText.read text fallback) a j.val
      (Dyadic.scale (WindowIndex.prepare text fallback) a j L) := by
  unfold Dyadic.scale
  split
  · exact indexed_supported text fallback a j L _ _
  · exact ⟨True.intro,True.intro⟩

theorem collect_supported (text : Array (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (text.size+1)) (fuel L : Nat) :
    RowsSupported (ArrayText.read text fallback) a j.val
      (Dyadic.collect (WindowIndex.prepare text fallback) a j fuel L).rows := by
  induction fuel generalizing L with
  | zero => intro row hm; cases hm
  | succ fuel ih =>
    intro row hm
    rcases List.mem_cons.mp hm with he|ht
    · subst row
      exact scale_supported text fallback a j L
    · exact ih (2*L) row ht

theorem dyadic_supported (text : Array (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (text.size+1)) :
    RowsSupported (ArrayText.read text fallback) a j.val
      (Dyadic.query (WindowIndex.prepare text fallback) a j).rows :=
  collect_supported text fallback a j _ _

end REWB.BoundaryBorder.Regular
