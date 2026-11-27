import REWB.BoundaryRangeCacheCorrect

/-! Counter bounds for both concrete cache stages and the online query.
The finite all-start output rows are supplied between stages, so their
production is deliberately outside these costs. Requests and indexes
are eager; no query-time factory is charged as a constant lookup. -/
namespace REWB.BoundaryRange.Cache
variable {σ : Nat}

def blockBudget (A B C K D E : DFA (Fin σ)) (n : Nat) : Nat :=
  NearIndex.buildBound A B C K D E n+FarLeft.buildBudget A B C K D E n+FarRight.prepareBudget K n+2

theorem buildBlock_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) :
    (buildBlock A B C K D E w fallback g0 g h0g hg).work≤blockBudget A B C K D E w.length := by
  have hn:=NearIndex.build_work A B C K D E w fallback g0 g h0g hg
  have hf:=FarLeft.build_work A B C K D E w fallback g hg
  have hr:=FarRight.prepare_work K w g
  change (NearIndex.build A B C K D E w fallback g0 g h0g hg).work+
    (FarLeft.build A B C K D E w fallback g hg).work+(FarRight.prepare K w g).work+2≤_
  unfold blockBudget
  omega

theorem prepare_blocks_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) :
    (prepare A B C K D E w fallback width hw).blocks.work≤
      CacheGrid.count w.length width*(blockBudget A B C K D E w.length+3)+1 := by
  apply Table.build_work_le
  intro slot
  exact buildBlock_work A B C K D E w fallback _ _ _ _

def prepareBudget (A B C K D E : DFA (Fin σ)) (n width : Nat) : Nat :=
  CacheGrid.count n width*(blockBudget A B C K D E n+3)+1+
    NearIndex.Border.buildBound A B C K D E n+n+9

theorem prepare_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) :
    (prepare A B C K D E w fallback width hw).work≤prepareBudget A B C K D E w.length width := by
  have ht:=prepare_blocks_work A B C K D E w fallback width hw
  have hb:=NearIndex.Border.build_work A B C K D E w fallback
  change (prepare A B C K D E w fallback width hw).blocks.work+
    (NearIndex.Border.build A B C K D E w fallback).work+w.length+9≤_
  unfold prepareBudget
  omega

theorem assemble_right_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (prepared : Prepared A B C K D E w) (bits : Vector (FarRight.Input K) prepared.slots) :
    (assemble A B C K D E w prepared bits).right.work≤
      prepared.slots*(FarRight.finishBudget K E w.length+5)+1 := by
  apply Table.build_work_le
  intro slot
  have hh:=FarRight.assemble_work K E w (Table.get prepared.blocks slot).requests (bits.get slot)
  dsimp only
  omega

theorem assemble_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (prepared : Prepared A B C K D E w) (bits : Vector (FarRight.Input K) prepared.slots) :
    (assemble A B C K D E w prepared bits).work≤
      prepared.work+prepared.slots*(FarRight.finishBudget K E w.length+5)+5 := by
  have hh:=assemble_right_work A B C K D E w prepared bits
  change prepared.work+(assemble A B C K D E w prepared bits).right.work+4≤_
  omega

def buildBudget (A B C K D E : DFA (Fin σ)) (n width : Nat) : Nat :=
  prepareBudget A B C K D E n width+CacheGrid.count n width*(FarRight.finishBudget K E n+5)+5

theorem build_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs K w.length width) :
    (build A B C K D E w fallback width hw bits).work≤buildBudget A B C K D E w.length width := by
  have hs:=assemble_work A B C K D E w (prepare A B C K D E w fallback width hw) bits
  have hp:=prepare_work A B C K D E w fallback width hw
  change (build A B C K D E w fallback width hw bits).work≤
    (prepare A B C K D E w fallback width hw).work+
      CacheGrid.count w.length width*(FarRight.finishBudget K E w.length+5)+5 at hs
  unfold buildBudget
  omega

theorem threeBudget_mono (A B C K D E : DFA (Fin σ)) (n a b width : Nat)
    (ha : a≤width) (hb : b≤width) :
    NearIndex.threeBudget A B C K D E n a b≤NearIndex.threeBudget A B C K D E n width width := by
  have hs:=Nat.mul_le_mul_right (NearIndex.separatedRowBudget C K D E n+3) ha
  have he:=Nat.mul_le_mul_right (NearIndex.endCellBudget A C D E n+3) hb
  have ht:=Nat.mul_le_mul_right (NearIndex.startCellBudget B C D E n+3) hb
  have he' : NearIndex.endRowBudget A C K D E n b+3≤NearIndex.endRowBudget A C K D E n width+3 := by
    unfold NearIndex.endRowBudget
    omega
  have ht' : NearIndex.startRowBudget B C K D E n b+3≤NearIndex.startRowBudget B C K D E n width+3 := by
    unfold NearIndex.startRowBudget
    omega
  have he'' :=Nat.mul_le_mul ha he'
  have ht'' :=Nat.mul_le_mul ha ht'
  unfold NearIndex.threeBudget
  omega

theorem borderBudget_mono (A B C K D E : DFA (Fin σ)) (n span width : Nat) (h : span≤width) :
    NearIndex.Border.queryBudget A B C K D E n span≤NearIndex.Border.queryBudget A B C K D E n width := by
  have hi:=Nat.mul_le_mul_right (NearIndex.Border.atBudget A B C K D E n+3) h
  have ho:=Nat.mul_le_mul h (Nat.add_le_add_right hi 4)
  unfold NearIndex.Border.queryBudget
  omega

def queryBudget (A B C K D E : DFA (Fin σ)) (n width : Nat) : Nat :=
  FarLeft.queryBudget C K E n+FarRight.queryBudget K n+
    NearIndex.threeBudget A B C K D E n width width+NearIndex.Border.queryBudget A B C K D E n width+17

theorem queryValid_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs K w.length width) (left right : Nat)
    (hlr : left≤right) (hr : right≤w.length) :
    (queryValid (build A B C K D E w fallback width hw bits) left right (by change left≤w.length; omega)).2≤
      queryBudget A B C K D E w.length width := by
  let slot : Fin (CacheGrid.count w.length width):=⟨left/width,CacheGrid.slot_bound w.length width left hw (by omega)⟩
  let g0:=CacheGrid.lower w.length width slot.val
  let g:=CacheGrid.upper w.length width slot.val
  have hgg:=CacheGrid.bounds w.length width slot.val
  change g0≤g ∧ g≤w.length at hgg
  have hl:=CacheGrid.selected_bounds w.length width left hw (by omega)
  change g0≤left ∧ left≤g ∧ g-left≤width at hl
  have hspan:=CacheGrid.span w.length width slot.val
  change g-g0≤width at hspan
  have hf:=FarLeft.query_work A B C K D E w fallback g hgg.2 left right
  have ht:=FarRight.query_work K E w g hgg.2 (bits.get slot) left right
  have hn:=NearIndex.queryThree_work A B C K D E w fallback g0 g hgg.1 hgg.2 left right hl.1 hl.2.1 hr
  have hb:=NearIndex.Border.query_work A B C K D E w fallback left right g0 g hr
  have hn':=threeBudget_mono A B C K D E w.length (g-left) (g-g0) width hl.2.2 hspan
  have hb':=borderBudget_mono A B C K D E w.length (g-g0) width hspan
  unfold queryValid
  change (FarLeft.query K E (Table.get (prepare A B C K D E w fallback width hw).blocks slot).far left right).2+
    (FarRight.query K (Table.get (build A B C K D E w fallback width hw bits).right slot) left right).2+
    (NearIndex.queryThree (Table.get (prepare A B C K D E w fallback width hw).blocks slot).near left right).2+
    (NearIndex.Border.query (NearIndex.Border.build A B C K D E w fallback) left right
      (Table.get (prepare A B C K D E w fallback width hw).blocks slot).lower
      (Table.get (prepare A B C K D E w fallback width hw).blocks slot).upper).2+17≤_
  rw [prepare_block,build_right]
  change (FarLeft.query K E (FarLeft.build A B C K D E w fallback g hgg.2) left right).2+
    (FarRight.query K (FarRight.build K E w g (bits.get slot)) left right).2+
    (NearIndex.queryThree (NearIndex.build A B C K D E w fallback g0 g hgg.1 hgg.2) left right).2+
    (NearIndex.Border.query (NearIndex.Border.build A B C K D E w fallback) left right g0 g).2+17≤_
  unfold queryBudget
  omega

theorem query_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs K w.length width) (left right : Nat) :
    (query (build A B C K D E w fallback width hw bits) left right).2≤queryBudget A B C K D E w.length width := by
  unfold query
  change ((if h : left≤right ∧ right≤w.length then _ else _) : Bool×Nat).2≤_
  split
  · rename_i h
    exact queryValid_work A B C K D E w fallback width hw bits left right h.1 h.2
  · dsimp only
    unfold queryBudget
    omega

end REWB.BoundaryRange.Cache
