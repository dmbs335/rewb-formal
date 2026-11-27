import REWB.LCEIndex
import REWB.ArrayText

/-! Materialize a finite word once, then prepare forward and reverse
exact rank indexes. All text reads during preparation are array reads;
queries use only the prepared arrays. -/
namespace REWB.LCEIndexArray
open REWB.Periodic REWB.LCEIndex
variable {σ : Nat}

structure WordIndex where
  length : Nat
  forward : RankIndex.Index
  backward : RankIndex.Index
  inputCells : Nat
  deriving Repr

def prepareWord (w : Word (Fin σ)) (fallback : Fin σ) : WordIndex :=
  let text:=w.toArray
  let f:=ArrayText.read text fallback
  ⟨text.size,prepare f text.size,prepareReverse f text.size,text.size⟩

def lceWord (I : WordIndex) (i j : Nat) : Nat×Nat := lce I.forward I.length i j
def lcsWord (I : WordIndex) (e k : Nat) : Nat×Nat := lcs I.backward I.length e k

def AgreeWord (w : Word (Fin σ)) (i j L : Nat) : Prop :=
  i+L≤w.length ∧ j+L≤w.length ∧ (w.drop i).take L=(w.drop j).take L

def SuffixAgreeWord (w : Word (Fin σ)) (e k L : Nat) : Prop :=
  L≤e ∧ L≤k ∧ (w.drop (e-L)).take L=(w.drop (k-L)).take L

theorem agree_word (w : Word (Fin σ)) (fallback : Fin σ) (i j L : Nat) :
    Agree (ArrayText.read w.toArray fallback) w.length i j L ↔ AgreeWord w i j L := by
  constructor
  · rintro ⟨hi,hj,he⟩
    exact ⟨hi,hj,by rwa [ArrayText.segment_word w fallback i L hi,
      ArrayText.segment_word w fallback j L hj] at he⟩
  · rintro ⟨hi,hj,he⟩
    exact ⟨hi,hj,by rwa [ArrayText.segment_word w fallback i L hi,
      ArrayText.segment_word w fallback j L hj]⟩

theorem suffix_agree_word (w : Word (Fin σ)) (fallback : Fin σ) (e k L : Nat)
    (he : e≤w.length) (hk : k≤w.length) :
    SuffixAgree (ArrayText.read w.toArray fallback) e k L ↔ SuffixAgreeWord w e k L := by
  constructor
  · rintro ⟨hLe,hLk,heq⟩
    exact ⟨hLe,hLk,by rwa [ArrayText.segment_word w fallback (e-L) L (by omega),
      ArrayText.segment_word w fallback (k-L) L (by omega)] at heq⟩
  · rintro ⟨hLe,hLk,heq⟩
    exact ⟨hLe,hLk,by rwa [ArrayText.segment_word w fallback (e-L) L (by omega),
      ArrayText.segment_word w fallback (k-L) L (by omega)]⟩

theorem lceWord_correct (w : Word (Fin σ)) (fallback : Fin σ) (i j : Nat)
    (hi : i≤w.length) (hj : j≤w.length) :
    AgreeWord w i j (lceWord (prepareWord w fallback) i j).1 ∧
      ∀ k,AgreeWord w i j k→k≤(lceWord (prepareWord w fallback) i j).1 := by
  simp only [lceWord,prepareWord,List.size_toArray]
  have hh := lce_correct (ArrayText.read w.toArray fallback) w.length i j hi hj
  exact ⟨(agree_word w fallback i j _).mp hh.1,
    fun k hk=>hh.2 k ((agree_word w fallback i j k).mpr hk)⟩

theorem lcsWord_correct (w : Word (Fin σ)) (fallback : Fin σ) (e k : Nat)
    (he : e≤w.length) (hk : k≤w.length) :
    SuffixAgreeWord w e k (lcsWord (prepareWord w fallback) e k).1 ∧
      ∀ L,SuffixAgreeWord w e k L→L≤(lcsWord (prepareWord w fallback) e k).1 := by
  simp only [lcsWord,prepareWord,List.size_toArray]
  have hh := lcs_correct (ArrayText.read w.toArray fallback) w.length e k he hk
  exact ⟨(suffix_agree_word w fallback e k _ he hk).mp hh.1,
    fun L hL=>hh.2 L ((suffix_agree_word w fallback e k L he hk).mpr hL)⟩

theorem prepareWord_inputCells (w : Word (Fin σ)) (fallback : Fin σ) :
    (prepareWord w fallback).inputCells=w.length := by simp only [prepareWord,List.size_toArray]

theorem prepareWord_work (w : Word (Fin σ)) (fallback : Fin σ) :
    (prepareWord w fallback).forward.countedWork+
      (prepareWord w fallback).backward.countedWork≤
        2*((w.length+1)*((w.length.log2+1)*(16*RankIndex.width σ w.length+4)+1)) := by
  simp only [prepareWord,List.size_toArray]
  have hh := Nat.add_le_add (prepare_work (ArrayText.read w.toArray fallback) w.length)
    (prepareReverse_work (ArrayText.read w.toArray fallback) w.length)
  omega

theorem lceWord_rankReads (w : Word (Fin σ)) (fallback : Fin σ) (i j : Nat) :
    2*(lceWord (prepareWord w fallback) i j).2≤2*(w.length.log2+1) := by
  simp only [lceWord,prepareWord,List.size_toArray]
  exact lce_rankReads (ArrayText.read w.toArray fallback) w.length i j

theorem lcsWord_rankReads (w : Word (Fin σ)) (fallback : Fin σ) (e k : Nat) :
    2*(lcsWord (prepareWord w fallback) e k).2≤2*(w.length.log2+1) := by
  simp only [lcsWord,prepareWord,List.size_toArray]
  exact lcs_rankReads (ArrayText.read w.toArray fallback) w.length e k

end REWB.LCEIndexArray
