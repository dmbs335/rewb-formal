import REWB.BoundaryBorderWindowSelect
import REWB.MaskedSuffixClassCost

/-! An actual text-built border index. Complete occurrence trees and
forward LCE ranks come from one shared suffix preparation. Ordered-tree
capacity, text length, and the later dyadic scale count are cached once.
No query input supplies a class, AP, period, or equality oracle. -/
namespace REWB.BoundaryBorder.WindowIndex
open REWB.MaskedOrdered REWB.MaskedRunDiscovery REWB.LCEIndex
variable {n h σ : Nat}

structure Index (n h : Nat) where
  classes : MaskedSuffixClass.Index n h
  capacity : Nat
  length : Nat
  scales : Nat
  work : Nat

def fromClasses (classes : MaskedSuffixClass.Index n h) : Index n h :=
  let cap:=MaskedOrdered.capacity h
  ⟨classes,cap.1,n,h,classes.work+cap.2+4⟩

def prepare (text : Array (Fin σ)) (fallback : Fin σ) : Index text.size (MaskedSuffixClass.height text.size) :=
  fromClasses (MaskedSuffixClass.prepare text fallback)

theorem prepare_classes (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).classes=MaskedSuffixClass.prepare text fallback := rfl

theorem prepare_capacity (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).capacity=2^(MaskedSuffixClass.height text.size) :=
  MaskedOrdered.capacity_value _

theorem prepare_length (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).length=text.size := rfl

theorem prepare_scales (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).scales=MaskedSuffixClass.height text.size := rfl

def query (idx : Index n h) (a : Nat) (j : Fin (n+1)) (L lo hi : Nat) : Window.Selected :=
  if 0<L ∧ hi-lo<L ∧ a≤idx.length then
    let found:=MaskedSuffixClass.query idx.classes j L
    match found.value with
    | none => ⟨.empty,.empty,found.work+5⟩
    | some out =>
      let answer:=Window.query idx.classes.suffix.trie.prepared.ranks out.record.state.tree
        idx.capacity idx.length L lo hi a j.val
      ⟨answer.first,answer.second,found.work+answer.work+7⟩
  else ⟨.empty,.empty,4⟩

def queryBudget (idx : Index n h) : Nat :=
  6*idx.classes.levels+28*h+104*(idx.length.log2+1)+162

theorem query_work (idx : Index n h) (a : Nat) (j : Fin (n+1)) (L lo hi : Nat) :
    (query idx a j L lo hi).work≤queryBudget idx := by
  have hf:=MaskedSuffixClass.query_work idx.classes j L
  simp only [query]
  split
  · cases he : (MaskedSuffixClass.query idx.classes j L).value with
    | none => simp only [he,queryBudget]; omega
    | some out =>
      have hw:=Window.query_work idx.classes.suffix.trie.prepared.ranks out.record.state.tree
        idx.capacity idx.length L lo hi a j.val
      simp only [he,queryBudget]
      omega
  · simp only [queryBudget]; omega

theorem query_correct (text : Array (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (text.size+1)) (L lo hi : Nat) (hwidth : hi-lo<L)
    (ha : a≤text.size) (hj : j.val+L≤text.size) (p : Nat) :
    (query (prepare text fallback) a j L lo hi).Holds p ↔
      Occurs (ArrayText.read text fallback) text.size j.val L p ∧
      lo≤p ∧ p≤hi ∧ p≤a ∧ Agree (ArrayText.read text fallback) text.size p j.val (a-p) := by
  have hL : 0<L := by omega
  obtain ⟨out,ho,hv,hfull⟩:=MaskedSuffixClass.query_complete text fallback j L (by omega)
  have hguard : 0<L ∧ hi-lo<L ∧ a≤(prepare text fallback).length := ⟨hL,hwidth,ha⟩
  rw [query,if_pos hguard]
  simp only [prepare_classes,ho]
  change (Window.query (MaskedSuffixClass.prepare text fallback).suffix.trie.prepared.ranks
    out.record.state.tree (prepare text fallback).capacity text.size L lo hi a j.val).Holds p ↔ _
  rw [MaskedSuffixClass.prepare_forward]
  rw [Window.query_correct (ArrayText.read text fallback) text.size j.val L lo hi a
    out.record.state.tree (prepare text fallback).capacity hv.1 hv.2.1
    (prepare_capacity text fallback) hfull hwidth ha hj p,hfull p]

theorem query_invalid_class (text : Array (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (text.size+1)) (L lo hi : Nat) (hj : text.size<j.val+L) (p : Nat) :
    ¬(query (prepare text fallback) a j L lo hi).Holds p := by
  have hn:=MaskedSuffixClass.query_invalid text fallback j L (by omega)
  simp only [query,prepare_classes,hn]
  split <;> simp only [Window.Selected.Holds,Choice.Holds,or_self,not_false_eq_true]

theorem prepare_work (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).work≤MaskedSuffixClass.budget σ text.size+
      MaskedSuffixClass.height text.size+5 := by
  have hb:=MaskedSuffixClass.prepare_work text fallback
  have hc:=MaskedOrdered.capacity_work (MaskedSuffixClass.height text.size)
  change (MaskedSuffixClass.prepare text fallback).work+
    (MaskedOrdered.capacity (MaskedSuffixClass.height text.size)).2+4≤_
  omega

theorem prepare_work_closed (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).work≤
      (32*(σ+2)+836)*(text.size+1)*((text.size+1).log2+1)^2 := by
  have hb:=prepare_work text fallback
  have hc:=MaskedSuffixClass.budget_closed σ text.size
  have hv:=MaskedRunEnumerationCost.square_bounds text.size
  change 1≤MaskedRunEnumerationCost.volume text.size ∧
    text.size+1≤MaskedRunEnumerationCost.volume text.size ∧
    MaskedSuffixClass.height text.size≤MaskedRunEnumerationCost.volume text.size ∧
    (text.size+1)*MaskedSuffixClass.height text.size≤MaskedRunEnumerationCost.volume text.size at hv
  rw [Nat.mul_assoc] at hc ⊢
  change MaskedSuffixClass.budget σ text.size≤(32*(σ+2)+830)*MaskedRunEnumerationCost.volume text.size at hc
  change (prepare text fallback).work≤(32*(σ+2)+836)*MaskedRunEnumerationCost.volume text.size
  have he : 32*(σ+2)+836=(32*(σ+2)+830)+6 := by omega
  rw [he,Nat.add_mul]
  omega

end REWB.BoundaryBorder.WindowIndex
