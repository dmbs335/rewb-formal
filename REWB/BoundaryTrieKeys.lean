import REWB.LCEIndexArray
import Init.Data.List.Lex

/-! Substring descriptors for a boundary trie. Executable operations retain
only endpoints, lengths, and terminal records. The words below occur solely
in specifications; comparisons use a prepared exact LCE index and at most
two direct text reads. -/
namespace REWB.BoundaryTrie
open REWB.Periodic

local instance {σ : Nat} : Std.Irrefl (· < · : Fin σ→Fin σ→Prop) where
  irrefl a := Fin.lt_irrefl a
local instance {σ : Nat} : Std.Asymm (· < · : Fin σ→Fin σ→Prop) where
  asymm _ _ := Fin.lt_asymm
local instance {σ : Nat} : Std.Antisymm (¬ · < · : Fin σ→Fin σ→Prop) where
  antisymm a b h₁ h₂ := Fin.ext (by change ¬a.val<b.val at h₁; change ¬b.val<a.val at h₂; omega)
local instance {σ : Nat} : Trans (¬ · < · : Fin σ→Fin σ→Prop) (¬ · < ·) (¬ · < ·) where
  trans h₁ h₂ := by change ¬_<_ at h₁ h₂ ⊢; omega
local instance {σ : Nat} : Std.Total (¬ · < · : Fin σ→Fin σ→Prop) where
  total a b := by change (¬a.val<b.val)∨(¬b.val<a.val); omega

inductive Terminal (k m : Nat) where
  | source : Nat → Terminal k m
  | target : Nat → Fin k → Fin m → Terminal k m
  deriving DecidableEq, Repr

structure Key (n : Nat) (ρ : Type) where
  start : Nat
  length : Nat
  bounded : start+length≤n
  record : ρ
  deriving Repr

namespace Key
variable {n σ : Nat} {ρ : Type}

def word (f : Nat→Fin σ) (a : Key n ρ) : Word (Fin σ) :=
  segment f a.start a.length

def Common (f : Nat→Fin σ) (a b : Key n ρ) (d : Nat) : Prop :=
  d≤a.length ∧ d≤b.length ∧ segment f a.start d=segment f b.start d

def Exact (f : Nat→Fin σ) (a b : Key n ρ) (d : Nat) : Prop :=
  Common f a b d ∧ ∀ e,Common f a b e→e≤d

def ordered (f : Nat→Fin σ) (a b : Key n ρ) : Prop := word f a≤word f b

theorem common_zero (f : Nat→Fin σ) (a b : Key n ρ) : Common f a b 0 :=
  ⟨Nat.zero_le _,Nat.zero_le _,rfl⟩

theorem common_shorten (f : Nat→Fin σ) (a b : Key n ρ) (d e : Nat)
    (hd : Common f a b d) (he : e≤d) : Common f a b e := by
  refine ⟨by have hh:=hd.1; omega,by have hh:=hd.2.1; omega,?_⟩
  apply (segment_eq_points f a.start b.start e).mpr
  intro i hi
  exact (segment_eq_points f a.start b.start d).mp hd.2.2 i (by omega)

theorem common_symmetric (f : Nat→Fin σ) (a b : Key n ρ) (d : Nat) :
    Common f a b d ↔ Common f b a d := by
  exact ⟨fun h=>⟨h.2.1,h.1,h.2.2.symm⟩,fun h=>⟨h.2.1,h.1,h.2.2.symm⟩⟩

theorem common_trans (f : Nat→Fin σ) (a b c : Key n ρ) (d : Nat)
    (hab : Common f a b d) (hbc : Common f b c d) : Common f a c d :=
  ⟨hab.1,hbc.2.1,hab.2.2.trans hbc.2.2⟩

theorem exact_unique (f : Nat→Fin σ) (a b : Key n ρ) (d e : Nat)
    (hd : Exact f a b d) (he : Exact f a b e) : d=e :=
  Nat.le_antisymm (he.2 d hd.1) (hd.2 e he.1)

theorem mismatch (f : Nat→Fin σ) (a b : Key n ρ) (d : Nat)
    (hd : Exact f a b d) (ha : d<a.length) (hb : d<b.length) :
    f (a.start+d)≠f (b.start+d) := by
  intro he
  have hg : Common f a b (d+1) := by
    refine ⟨by omega,by omega,?_⟩
    rw [segment_append,segment_append,hd.1.2.2]
    simp only [segment,he]
  have hh:=hd.2 (d+1) hg
  omega

private theorem append_order (p x y : List (Fin σ)) : p++x≤p++y ↔ x≤y := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.cons_append,List.cons_le_cons_iff,Fin.lt_irrefl,false_or,true_and,ih]

theorem ordered_at (f : Nat→Fin σ) (a b : Key n ρ) (d : Nat)
    (hd : Exact f a b d) :
    ordered f a b ↔ a.length=d ∨
      (d<a.length ∧ d<b.length ∧ f (a.start+d)<f (b.start+d)) := by
  have ha:=hd.1.1
  have hb:=hd.1.2.1
  have hea : a.length=d+(a.length-d) := by omega
  have heb : b.length=d+(b.length-d) := by omega
  unfold ordered word
  conv => lhs; lhs; rw [hea,segment_append]
  conv => lhs; rhs; rw [heb,segment_append]
  rw [hd.1.2.2,append_order]
  by_cases hda : a.length=d
  · simp only [hda,Nat.sub_self,segment,List.nil_le,true_or]
  · have hda' : d<a.length := by omega
    have hpos : a.length-d=(a.length-d-1)+1 := by omega
    rw [hpos,segment]
    by_cases hdb : b.length=d
    · simp only [hdb,Nat.sub_self,segment,List.le_nil,List.cons_ne_nil,hda,
        false_or,Nat.lt_irrefl,false_and,and_false]
    · have hdb' : d<b.length := by omega
      have hpos' : b.length-d=(b.length-d-1)+1 := by omega
      rw [hpos',segment,List.cons_le_cons_iff]
      have hne:=mismatch f a b d hd hda' hdb'
      simp only [hne,false_and,or_false,hda,false_or,hda',hdb',true_and]

theorem ordered_trans (f : Nat→Fin σ) (a b c : Key n ρ)
    (hab : ordered f a b) (hbc : ordered f b c) : ordered f a c :=
  List.le_trans hab hbc

theorem ordered_total (f : Nat→Fin σ) (a b : Key n ρ) :
    ordered f a b ∨ ordered f b a := List.le_total _ _

theorem word_split (f : Nat→Fin σ) (a : Key n ρ) (d : Nat) (hd : d≤a.length) :
    word f a=segment f a.start d++segment f (a.start+d) (a.length-d) := by
  unfold word
  conv => lhs; rw [show a.length=d+(a.length-d) by omega]
  exact segment_append _ _ _ _

theorem take_word (f : Nat→Fin σ) (a : Key n ρ) (d : Nat) (hd : d≤a.length) :
    (word f a).take d=segment f a.start d := by
  rw [word_split f a d hd]
  have hh:=List.take_left (l₁:=segment f a.start d) (l₂:=segment f (a.start+d) (a.length-d))
  simpa only [segment_length] using hh

private theorem prefix_between (p a b x : List (Fin σ))
    (ha : p++a≤x) (hb : x≤p++b) : ∃y,x=p++y := by
  induction p generalizing x with
  | nil => exact ⟨x,rfl⟩
  | cons c p ih =>
    cases x with
    | nil => simp only [List.cons_append,List.le_nil,List.cons_ne_nil] at ha
    | cons v x =>
      simp only [List.cons_append,List.cons_le_cons_iff] at ha hb
      have he : c=v := by
        rcases ha with ha | ⟨ha,_⟩
        · rcases hb with hb | ⟨hb,_⟩
          · exact False.elim (Fin.lt_asymm ha hb)
          · exact False.elim (Fin.lt_irrefl c (by simpa only [hb] using ha))
        · exact ha
      subst v
      simp only [Fin.lt_irrefl,false_or,true_and] at ha hb
      obtain ⟨y,hy⟩:=ih x ha hb
      exact ⟨y,by simp only [hy,List.cons_append]⟩

theorem common_between (f : Nat→Fin σ) (a b c : Key n ρ) (d : Nat)
    (hac : ordered f a c) (hcb : ordered f c b) (hab : Common f a b d) :
    Common f a c d := by
  have ha:=word_split f a d hab.1
  have hb:=word_split f b d hab.2.1
  rw [← hab.2.2] at hb
  unfold ordered at hac hcb
  rw [ha] at hac
  rw [hb] at hcb
  obtain ⟨tail,ht⟩:=prefix_between (segment f a.start d)
    (segment f (a.start+d) (a.length-d)) (segment f (b.start+d) (b.length-d))
    (word f c) hac hcb
  have hc : d≤c.length := by
    have hl:=congrArg List.length ht
    simp only [word,segment_length,List.length_append] at hl
    omega
  refine ⟨hab.1,hc,?_⟩
  have htake:=congrArg (List.take d) ht
  rw [take_word f c d hc] at htake
  have hh:=List.take_left (l₁:=segment f a.start d) (l₂:=tail)
  rw [segment_length] at hh
  rw [hh] at htake
  exact htake.symm

/-- Zero denotes a terminal boundary; every actual alphabet symbol is
strictly positive. This makes prefix keys sort before their extensions. -/
def symbol (f : Nat→Fin σ) (a : Key n ρ) (d : Nat) : Nat :=
  if d<a.length then (f (a.start+d)).val+1 else 0

theorem symbol_order (f : Nat→Fin σ) (a b : Key n ρ) (d : Nat)
    (hab : Common f a b d) (hle : ordered f a b) : symbol f a d≤symbol f b d := by
  by_cases ha : d<a.length
  · have haw:=word_split f a d hab.1
    have hbw:=word_split f b d hab.2.1
    unfold ordered at hle
    rw [haw,hbw,hab.2.2,append_order] at hle
    have hpos : a.length-d=(a.length-d-1)+1 := by omega
    rw [hpos,segment] at hle
    by_cases hb : d<b.length
    · have hpos' : b.length-d=(b.length-d-1)+1 := by omega
      rw [hpos',segment,List.cons_le_cons_iff] at hle
      simp only [symbol,ha,hb,if_true]
      rcases hle with hh | ⟨hh,_⟩
      · exact Nat.add_le_add_right (Nat.le_of_lt hh) 1
      · rw [hh]
        exact Nat.le_refl _
    · have he : b.length-d=0 := by omega
      rw [he,segment,List.le_nil] at hle
      cases hle
  · simp only [symbol,ha,if_false]
    exact Nat.zero_le _

theorem symbol_ne_of_exact (f : Nat→Fin σ) (a b : Key n ρ) (d : Nat)
    (hd : Exact f a b d) (h : a.length≠d ∨ b.length≠d) :
    symbol f a d≠symbol f b d := by
  by_cases ha : d<a.length
  · by_cases hb : d<b.length
    · simp only [symbol,ha,hb,if_true]
      intro he
      exact mismatch f a b d hd ha hb (Fin.ext (by omega))
    · simp only [symbol,ha,hb,if_true,if_false]
      omega
  · have hae : a.length=d := by have hh:=hd.1.1; omega
    have hb : d<b.length := by have hh:=hd.1.2.1; omega
    simp only [symbol,ha,hb,if_true,if_false]
    omega

theorem exact_of_symbol_ne (f : Nat→Fin σ) (a b : Key n ρ) (d : Nat)
    (hd : Common f a b d) (hne : symbol f a d≠symbol f b d) : Exact f a b d := by
  refine ⟨hd,?_⟩
  intro e he
  by_cases hle : e≤d
  · exact hle
  have he' : d<e := by omega
  have ha : d<a.length := by have hh:=he.1; omega
  have hb : d<b.length := by have hh:=he.2.1; omega
  have heq:=(segment_eq_points f a.start b.start e).mp he.2.2 d he'
  exact False.elim (hne (by simp only [symbol,ha,hb,if_true,heq]))

end Key

variable {σ n : Nat} {ρ : Type}

/-- A capped query does not inspect the represented substring. -/
def commonPrefix (ranks : RankIndex.Index) (a b : Key n ρ) : Nat×Nat :=
  let r:=LCEIndex.lceMeasured ranks n a.start b.start
  (min (min a.length b.length) r.length,r.countedWork+3)

theorem commonPrefix_correct (f : Nat→Fin σ) (a b : Key n ρ) :
    Key.Exact f a b (commonPrefix (LCEIndex.prepare f n) a b).1 := by
  let r:=LCEIndex.lceMeasured (LCEIndex.prepare f n) n a.start b.start
  have hh:=LCEIndex.lceMeasured_correct f n a.start b.start
    (by have h:=a.bounded; omega) (by have h:=b.bounded; omega)
  change LCEIndex.IsLCE f n a.start b.start r.length at hh
  let d:=min (min a.length b.length) r.length
  have ha : d≤a.length := Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_left _ _)
  have hb : d≤b.length := Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_right _ _)
  have hr : d≤r.length := Nat.min_le_right _ _
  refine ⟨⟨ha,hb,(LCEIndex.agree_shorten f n a.start b.start r.length d hh.1 hr).2.2⟩,?_⟩
  intro e he
  have he' : LCEIndex.Agree f n a.start b.start e :=
    ⟨by have h:=a.bounded; have h':=he.1; omega,
     by have h:=b.bounded; have h':=he.2.1; omega,he.2.2⟩
  exact Nat.le_min.mpr ⟨Nat.le_min.mpr ⟨he.1,he.2.1⟩,hh.2 e he'⟩

theorem commonPrefix_work (ranks : RankIndex.Index) (a b : Key n ρ) :
    (commonPrefix ranks a b).2≤13*(n.log2+1)+4 := by
  have hh:=LCEIndex.lceMeasured_work ranks n a.start b.start
  simp only [commonPrefix]
  omega

/-- This is the actual comparator. The text is already materialized;
neither semantic words nor key copies are constructed here. -/
def compare (text : Array (Fin σ)) (fallback : Fin σ) (ranks : RankIndex.Index)
    (a b : Key text.size ρ) : Bool×Nat :=
  let r:=commonPrefix ranks a b
  if a.length=r.1 then (true,r.2+1)
  else if b.length=r.1 then (false,r.2+2)
  else (decide (ArrayText.read text fallback (a.start+r.1)<
                ArrayText.read text fallback (b.start+r.1)),r.2+7)

theorem compare_correct (text : Array (Fin σ)) (fallback : Fin σ)
    (a b : Key text.size ρ) :
    (compare text fallback (LCEIndex.prepare (ArrayText.read text fallback) text.size) a b).1=true ↔
      Key.ordered (ArrayText.read text fallback) a b := by
  let ranks:=LCEIndex.prepare (ArrayText.read text fallback) text.size
  let d:=(commonPrefix ranks a b).1
  have hd:=commonPrefix_correct (ArrayText.read text fallback) a b
  change Key.Exact (ArrayText.read text fallback) a b d at hd
  rw [Key.ordered_at _ _ _ d hd]
  unfold compare
  change (if a.length=d then (true,(commonPrefix ranks a b).2+1)
    else if b.length=d then (false,(commonPrefix ranks a b).2+2)
    else (decide (ArrayText.read text fallback (a.start+d)<ArrayText.read text fallback (b.start+d)),
      (commonPrefix ranks a b).2+7)).1=true ↔ _
  by_cases ha : a.length=d
  · simp only [ha,if_true,true_or]
  · rw [if_neg ha]
    have ha' : d<a.length := by have hh:=hd.1.1; omega
    by_cases hb : b.length=d
    · simp only [hb,if_true,Bool.false_eq_true,ha,false_or,Nat.lt_irrefl,and_false,false_and]
    · have hb' : d<b.length := by have hh:=hd.1.2.1; omega
      simp only [if_neg hb,decide_eq_true_eq,ha,false_or,ha',hb',true_and]

theorem compare_work (text : Array (Fin σ)) (fallback : Fin σ) (ranks : RankIndex.Index)
    (a b : Key text.size ρ) :
    (compare text fallback ranks a b).2≤13*(text.size.log2+1)+11 := by
  have hh:=commonPrefix_work ranks a b
  simp only [compare]
  split
  · omega
  · split <;> omega

end REWB.BoundaryTrie
