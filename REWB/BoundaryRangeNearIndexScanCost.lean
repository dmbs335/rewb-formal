import REWB.BoundaryRangeNearIndexScanCorrect

/-! Work of the three short-block loops. Their displayed bounds retain
the actual block widths. Thus the two nested loops have quadratic block
width and the inherited logarithmic fixed-pattern query factor. -/
namespace REWB.BoundaryRange.NearIndex
open REWB.BoundaryApplication
variable {σ : Nat}

def separatedRowBudget (C K D E : DFA (Fin σ)) (n : Nat) : Nat :=
  rangeBudget K n+separatedBudget C D E n+4
def endCellBudget (A C D E : DFA (Fin σ)) (n : Nat) : Nat :=
  rangeBudget C n+endBudget A D E n+5
def startCellBudget (B C D E : DFA (Fin σ)) (n : Nat) : Nat :=
  rangeBudget D n+startBudget B C E n+5
def endRowBudget (A C K D E : DFA (Fin σ)) (n span : Nat) : Nat :=
  rangeBudget K n+span*(endCellBudget A C D E n+3)+5
def startRowBudget (B C K D E : DFA (Fin σ)) (n span : Nat) : Nat :=
  rangeBudget K n+span*(startCellBudget B C D E n+3)+5

theorem atSeparated_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right p : Nat) (h0l : g0≤left) (hlp : left≤p) (hpg : p≤g) :
    (atSeparated (build A B C K D E w fallback g0 g h0g hg) left right p).2≤
      separatedRowBudget C K D E w.length := by
  have hk:=regular_work K w left p hlp (by omega)
  have hq:=separated_work A B C K D E w fallback g0 g h0g hg p right (by omega) hpg
  change (regular K (Range.build K w) left p).2+
    (separated (build A B C K D E w fallback g0 g h0g hg) p right).2+2≤_
  unfold separatedRowBudget
  omega

theorem atEnd_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (right p a : Nat) (hap : a≤p) (hpg : p≤g) :
    (atEnd (build A B C K D E w fallback g0 g h0g hg) right p a).2≤
      endCellBudget A C D E w.length := by
  have ha : a≤(build A B C K D E w fallback g0 g h0g hg).length := by
    change a≤w.length; omega
  unfold atEnd
  rw [dif_pos ha]
  have hc:=regular_work C w a p hap (by omega)
  have hq:=fixedEnd_work A B C K D E w fallback g0 g h0g hg p hpg ⟨a,by omega⟩ right
  change (regular C (Range.build C w) a p).2+
    (fixedEnd (build A B C K D E w fallback g0 g h0g hg) p ⟨a,_⟩ right).2+3≤_
  unfold endCellBudget
  omega

theorem endsAt_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right p : Nat) (h0l : g0≤left) (hlp : left≤p) (hpg : p≤g) :
    (endsAt (build A B C K D E w fallback g0 g h0g hg) left right p).2≤
      endRowBudget A C K D E w.length (g-g0) := by
  let idx:=build A B C K D E w fallback g0 g h0g hg
  have hk:=regular_work K w left p hlp (by omega)
  have hs:=scan_work (atEnd idx right p) (g0+1) (p-g0) (endCellBudget A C D E w.length)
    (by intro a ha he; exact atEnd_work A B C K D E w fallback g0 g h0g hg right p a (by omega) hpg)
  have hm:=Nat.mul_le_mul_right (endCellBudget A C D E w.length+3) (show p-g0≤g-g0 by omega)
  change (regular K (Range.build K w) left p).2+
    (scan (atEnd idx right p) (g0+1) (p-g0)).2+2≤_
  unfold endRowBudget
  omega

theorem atStart_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (right p j : Nat) (h0p : g0≤p) (hpj : p≤j) (hjg : j≤g) (hr : right≤w.length) :
    (atStart (build A B C K D E w fallback g0 g h0g hg) right p j).2≤
      startCellBudget B C D E w.length := by
  have hj : j≤(build A B C K D E w fallback g0 g h0g hg).length := by
    change j≤w.length; omega
  unfold atStart
  rw [dif_pos hj]
  have hd:=regular_work D w p j hpj (by omega)
  have hq:=fixedStart_work A B C K D E w fallback g0 g h0g hg p h0p (by omega)
    ⟨j,by omega⟩ (by change g0≤j; omega) right hr
  change (regular D (Range.build D w) p j).2+
    (fixedStart (build A B C K D E w fallback g0 g h0g hg) p ⟨j,_⟩ right).2+3≤_
  unfold startCellBudget
  omega

theorem startsAt_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right p : Nat) (h0l : g0≤left) (hlp : left≤p) (hpg : p≤g) (hr : right≤w.length) :
    (startsAt (build A B C K D E w fallback g0 g h0g hg) left right p).2≤
      startRowBudget B C K D E w.length (g-g0) := by
  let idx:=build A B C K D E w fallback g0 g h0g hg
  have hk:=regular_work K w left p hlp (by omega)
  have hs:=scan_work (atStart idx right p) p (min g (right+1)-p) (startCellBudget B C D E w.length)
    (by
      intro j hpj he
      exact atStart_work A B C K D E w fallback g0 g h0g hg right p j (by omega) hpj (by omega) hr)
  have hm:=Nat.mul_le_mul_right (startCellBudget B C D E w.length+3)
    (show min g (right+1)-p≤g-g0 by omega)
  change (regular K (Range.build K w) left p).2+
    (scan (atStart idx right p) p (min g (right+1)-p)).2+2≤_
  unfold startRowBudget
  omega

theorem querySeparated_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right : Nat) (h0l : g0≤left) (hlg : left≤g) :
    (querySeparated (build A B C K D E w fallback g0 g h0g hg) left right).2≤
      (g-left)*(separatedRowBudget C K D E w.length+3)+1 := by
  apply scan_work
  intro p hlp hp
  exact atSeparated_work A B C K D E w fallback g0 g h0g hg left right p h0l hlp (by
    change p<left+(g-left) at hp; omega)

theorem queryEnd_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right : Nat) (h0l : g0≤left) (hlg : left≤g) :
    (queryEnd (build A B C K D E w fallback g0 g h0g hg) left right).2≤
      (g-left)*(endRowBudget A C K D E w.length (g-g0)+3)+1 := by
  apply scan_work
  intro p hlp hp
  exact endsAt_work A B C K D E w fallback g0 g h0g hg left right p h0l hlp (by
    change p<left+(g-left) at hp; omega)

theorem queryStart_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right : Nat) (h0l : g0≤left) (hlg : left≤g) (hr : right≤w.length) :
    (queryStart (build A B C K D E w fallback g0 g h0g hg) left right).2≤
      (g-left)*(startRowBudget B C K D E w.length (g-g0)+3)+1 := by
  apply scan_work
  intro p hlp hp
  exact startsAt_work A B C K D E w fallback g0 g h0g hg left right p h0l hlp (by
    change p<left+(g-left) at hp; omega) hr

def threeBudget (A B C K D E : DFA (Fin σ)) (n width span : Nat) : Nat :=
  width*(separatedRowBudget C K D E n+3)+width*(endRowBudget A C K D E n span+3)+
    width*(startRowBudget B C K D E n span+3)+5

theorem queryThree_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right : Nat) (h0l : g0≤left) (hlg : left≤g) (hr : right≤w.length) :
    (queryThree (build A B C K D E w fallback g0 g h0g hg) left right).2≤
      threeBudget A B C K D E w.length (g-left) (g-g0) := by
  have hs:=querySeparated_work A B C K D E w fallback g0 g h0g hg left right h0l hlg
  have he:=queryEnd_work A B C K D E w fallback g0 g h0g hg left right h0l hlg
  have ht:=queryStart_work A B C K D E w fallback g0 g h0g hg left right h0l hlg hr
  simp only [queryThree]
  unfold threeBudget
  omega

end REWB.BoundaryRange.NearIndex
