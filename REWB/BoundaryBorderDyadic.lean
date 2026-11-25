import REWB.BoundaryBorderWindowIndex

/-! All positive suffix/prefix copy lengths from one actual text index.
Each dyadic length interval contributes two AP/point/empty choices. The
number of scales is cached during construction; neither suffixes nor
capture lengths are traversed during a query. -/
namespace REWB.BoundaryBorder.Dyadic
open REWB.MaskedRunDiscovery REWB.LCEIndex
variable {n h σ : Nat}

def lower (a L : Nat) : Nat := a-(2*L-1)
def upper (a L : Nat) : Nat := a-L

theorem window_width (a L : Nat) (hL : 0<L) (_ha : L≤a) : upper a L-lower a L<L := by
  unfold upper lower
  omega

/-- Subtract the complete upper length before truncating at zero. This
includes a source at zero when a lies below the next power-of-two cutoff. -/
theorem window_iff (a L p : Nat) (hL : 0<L) (ha : L≤a) :
    lower a L≤p ∧ p≤upper a L ↔ p≤a ∧ L≤a-p ∧ a-p<2*L := by
  unfold lower upper
  omega

def scale (idx : WindowIndex.Index n h) (a : Nat) (j : Fin (n+1)) (L : Nat) : Window.Selected :=
  if 0<L ∧ L≤a ∧ j.val+L≤idx.length then
    let out:=WindowIndex.query idx a j L (lower a L) (upper a L)
    ⟨out.first,out.second,out.work+8⟩
  else ⟨.empty,.empty,5⟩

theorem scale_work (idx : WindowIndex.Index n h) (a : Nat) (j : Fin (n+1)) (L : Nat) :
    (scale idx a j L).work≤WindowIndex.queryBudget idx+8 := by
  have hh:=WindowIndex.query_work idx a j L (lower a L) (upper a L)
  simp only [scale]
  split <;> dsimp only <;> omega

theorem scale_correct (text : Array (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (text.size+1)) (L : Nat) (ha : a≤text.size) (hL : 0<L) (p : Nat) :
    (scale (WindowIndex.prepare text fallback) a j L).Holds p ↔
      p≤a ∧ L≤a-p ∧ a-p<2*L ∧ Agree (ArrayText.read text fallback) text.size p j.val (a-p) := by
  by_cases hg : 0<L ∧ L≤a ∧ j.val+L≤text.size
  · rw [scale,WindowIndex.prepare_length,if_pos hg]
    change (WindowIndex.query (WindowIndex.prepare text fallback) a j L (lower a L) (upper a L)).Holds p ↔ _
    rw [WindowIndex.query_correct text fallback a j L _ _ (window_width a L hL hg.2.1) ha hg.2.2 p]
    constructor
    · rintro ⟨_,hlo,hhi,hpa,heq⟩
      have hb:=(window_iff a L p hL hg.2.1).mp ⟨hlo,hhi⟩
      exact ⟨hpa,hb.2.1,hb.2.2,heq⟩
    · rintro ⟨hpa,hLm,hm,heq⟩
      have hs:=agree_shorten (ArrayText.read text fallback) text.size p j.val (a-p) L heq hLm
      have hb:=(window_iff a L p hL hg.2.1).mpr ⟨hpa,hLm,hm⟩
      exact ⟨⟨hs.1,hs.2.2⟩,hb.1,hb.2,hpa,heq⟩
  · rw [scale,WindowIndex.prepare_length,if_neg hg]
    change (False ∨ False) ↔ _
    constructor
    · rintro (hh|hh) <;> exact False.elim hh
    · rintro ⟨hpa,hLm,_,heq⟩
      have hj:=heq.2.1
      exact False.elim (hg ⟨hL,by omega,by omega⟩)

structure Rows where
  rows : List Window.Selected
  work : Nat
  deriving Repr, DecidableEq

def Rows.Holds (out : Rows) (p : Nat) : Prop := ∃row,row∈out.rows ∧ row.Holds p

def collect (idx : WindowIndex.Index n h) (a : Nat) (j : Fin (n+1)) : Nat→Nat→Rows
  | 0,_ => ⟨[],1⟩
  | fuel+1,L =>
    let head:=scale idx a j L
    let tail:=collect idx a j fuel (2*L)
    ⟨head::tail.rows,head.work+tail.work+3⟩

theorem collect_length (idx : WindowIndex.Index n h) (a : Nat) (j : Fin (n+1)) (fuel L : Nat) :
    (collect idx a j fuel L).rows.length=fuel := by
  induction fuel generalizing L with
  | zero => rfl
  | succ fuel ih => simp only [collect,List.length_cons,ih]

theorem collect_work (idx : WindowIndex.Index n h) (a : Nat) (j : Fin (n+1)) (fuel L : Nat) :
    (collect idx a j fuel L).work≤fuel*(WindowIndex.queryBudget idx+11)+1 := by
  induction fuel generalizing L with
  | zero => simp only [collect,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | succ fuel ih =>
    have ht:=ih (2*L)
    have hh:=scale_work idx a j L
    change (scale idx a j L).work+(collect idx a j fuel (2*L)).work+3≤_
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem collect_holds_succ (idx : WindowIndex.Index n h) (a : Nat) (j : Fin (n+1)) (fuel L p : Nat) :
    (collect idx a j (fuel+1) L).Holds p ↔
      (scale idx a j L).Holds p ∨ (collect idx a j fuel (2*L)).Holds p := by
  change (∃row,row∈(scale idx a j L)::(collect idx a j fuel (2*L)).rows ∧ row.Holds p) ↔ _
  constructor
  · rintro ⟨row,hm,hp⟩
    rcases List.mem_cons.mp hm with he|ht
    · exact Or.inl (he ▸ hp)
    · exact Or.inr ⟨row,ht,hp⟩
  · rintro (hh|⟨row,ht,hp⟩)
    · exact ⟨_,List.mem_cons_self,hh⟩
    · exact ⟨row,List.mem_cons_of_mem _ ht,hp⟩

theorem collect_correct (text : Array (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (text.size+1)) (ha : a≤text.size) (fuel L : Nat) (hL : 0<L) (p : Nat) :
    (collect (WindowIndex.prepare text fallback) a j fuel L).Holds p ↔
      p≤a ∧ L≤a-p ∧ a-p<L*2^fuel ∧ Agree (ArrayText.read text fallback) text.size p j.val (a-p) := by
  induction fuel generalizing L with
  | zero =>
    change (∃row,row∈([] : List Window.Selected) ∧ row.Holds p) ↔ _
    constructor
    · rintro ⟨_,hm,_⟩
      cases hm
    · rintro ⟨_,hlo,hhi,_⟩
      simp only [Nat.pow_zero,Nat.mul_one] at hhi
      omega
  | succ fuel ih =>
    rw [collect_holds_succ,scale_correct text fallback a j L ha hL p,ih (2*L) (by omega)]
    have he : L*2^(fuel+1)=(2*L)*2^fuel := by rw [Nat.pow_succ]; ac_rfl
    rw [he]
    have hpw : 0<2^fuel := Nat.pow_pos (by decide)
    have hbound : 2*L≤(2*L)*2^fuel := by
      have hh:=Nat.mul_le_mul_left (2*L) (show 1≤2^fuel by omega)
      simpa only [Nat.mul_one] using hh
    constructor
    · rintro (⟨hpa,hlo,hhi,heq⟩|⟨hpa,hlo,hhi,heq⟩)
      · exact ⟨hpa,hlo,by omega,heq⟩
      · exact ⟨hpa,by omega,hhi,heq⟩
    · rintro ⟨hpa,hlo,hhi,heq⟩
      by_cases hh : a-p<2*L
      · exact Or.inl ⟨hpa,hlo,hh,heq⟩
      · exact Or.inr ⟨hpa,by omega,hhi,heq⟩

def query (idx : WindowIndex.Index n h) (a : Nat) (j : Fin (n+1)) : Rows :=
  let out:=collect idx a j idx.scales 1
  ⟨out.rows,out.work+2⟩

theorem query_length (idx : WindowIndex.Index n h) (a : Nat) (j : Fin (n+1)) :
    (query idx a j).rows.length=idx.scales := collect_length idx a j idx.scales 1

theorem query_work (idx : WindowIndex.Index n h) (a : Nat) (j : Fin (n+1)) :
    (query idx a j).work≤idx.scales*(WindowIndex.queryBudget idx+11)+3 := by
  have hh:=collect_work idx a j idx.scales 1
  change (collect idx a j idx.scales 1).work+2≤_
  omega

theorem log_height (n : Nat) : n.log2+1≤MaskedSuffixClass.height n := by
  by_cases hn : n=0
  · subst n
    simp only [Nat.log2_zero,MaskedSuffixClass.height]
    omega
  · have hh:=(Nat.log2_lt hn).mpr (MaskedSuffixClass.height_capacity n)
    omega

theorem prepared_queryBudget (text : Array (Fin σ)) (fallback : Fin σ) :
    WindowIndex.queryBudget (WindowIndex.prepare text fallback)≤306*MaskedSuffixClass.height text.size := by
  have hl:=log_height text.size
  have hh : 1≤MaskedSuffixClass.height text.size := by unfold MaskedSuffixClass.height; omega
  change 6*MaskedSuffixClass.levels text.size+28*MaskedSuffixClass.height text.size+
    104*(text.size.log2+1)+162≤_
  rw [MaskedSuffixClass.levels_height]
  omega

theorem query_work_closed (text : Array (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (text.size+1)) :
    (query (WindowIndex.prepare text fallback) a j).work≤
      317*((text.size+1).log2+1)^2+3 := by
  have hw:=query_work (WindowIndex.prepare text fallback) a j
  have hb:=prepared_queryBudget text fallback
  have hh : 1≤MaskedSuffixClass.height text.size := by unfold MaskedSuffixClass.height; omega
  have hs : WindowIndex.queryBudget (WindowIndex.prepare text fallback)+11≤317*MaskedSuffixClass.height text.size := by omega
  have hm:=Nat.mul_le_mul_left (MaskedSuffixClass.height text.size) hs
  change (query (WindowIndex.prepare text fallback) a j).work≤
    (MaskedSuffixClass.height text.size)*(WindowIndex.queryBudget (WindowIndex.prepare text fallback)+11)+3 at hw
  have he : MaskedSuffixClass.height text.size*(317*MaskedSuffixClass.height text.size)=
      317*(MaskedSuffixClass.height text.size)^2 := by rw [Nat.pow_two]; ac_rfl
  rw [he] at hm
  change (query (WindowIndex.prepare text fallback) a j).work≤317*(MaskedSuffixClass.height text.size)^2+3
  omega

/-- Every positive source suffix equal to a target prefix is represented
by one of the returned AP/point choices. This is an actual constructed
text-index query with no supplied class, AP, period, or witness oracle. -/
theorem query_correct (text : Array (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (text.size+1)) (ha : a≤text.size) (p : Nat) :
    (query (WindowIndex.prepare text fallback) a j).Holds p ↔
      p<a ∧ Agree (ArrayText.read text fallback) text.size p j.val (a-p) := by
  have hh:=collect_correct text fallback a j ha (MaskedSuffixClass.height text.size) 1 (by decide) p
  have hn:=MaskedSuffixClass.height_capacity text.size
  change (collect (WindowIndex.prepare text fallback) a j (MaskedSuffixClass.height text.size) 1).Holds p ↔ _
  rw [hh]
  simp only [Nat.one_mul]
  constructor
  · rintro ⟨hpa,hpos,_,heq⟩
    exact ⟨by omega,heq⟩
  · rintro ⟨hpa,heq⟩
    exact ⟨by omega,by omega,by omega,heq⟩

theorem query_iff_slices (w : Word (Fin σ)) (fallback : Fin σ) (a : Nat)
    (j : Fin (w.toArray.size+1)) (ha : a≤w.length) (p : Nat) :
    (query (WindowIndex.prepare w.toArray fallback) a j).Holds p ↔
      p<a ∧ j.val+(a-p)≤w.length ∧ Spec.slice w p a=Spec.slice w j.val (j.val+(a-p)) := by
  rw [query_correct w.toArray fallback a j (by simpa only [List.size_toArray] using ha) p]
  constructor
  · rintro ⟨hpa,hp,hj,he⟩
    simp only [List.size_toArray] at hp hj
    rw [ArrayText.segment_word w fallback p (a-p) hp,
      ArrayText.segment_word w fallback j.val (a-p) hj] at he
    exact ⟨hpa,hj,by simpa only [Spec.slice,Nat.add_sub_cancel_left] using he⟩
  · rintro ⟨hpa,hj,he⟩
    refine ⟨hpa,by simpa only [List.size_toArray] using (show p+(a-p)≤w.length by omega),
      by simpa only [List.size_toArray] using hj,?_⟩
    rw [ArrayText.segment_word w fallback p (a-p) (by omega),
      ArrayText.segment_word w fallback j.val (a-p) hj]
    simpa only [Spec.slice,Nat.add_sub_cancel_left] using he

end REWB.BoundaryBorder.Dyadic
