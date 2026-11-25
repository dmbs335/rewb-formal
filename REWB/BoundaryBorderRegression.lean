import REWB.BoundaryBorderSelect

namespace REWB.BoundaryBorder.Regression
open Periodic RunGeometry LCEIndex

def text : Array (Fin 2) := #[0,1,0,1,0,1,0,0,0,1,0,1,0,0]
def f (i : Nat) : Fin 2 := text[i]?.getD 0
def index := prepare f 14

theorem source_prefix : PeriodPrefix f 14 0 2 7 := by
  apply prefix_from_interval f 14 0 7 0 2 ?_ (by decide) (by decide) (by decide) (by decide)
    (Or.inr (by decide))
  intro i _ hi
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide

theorem target_prefix : PeriodPrefix f 14 8 2 5 := by
  change PeriodPrefix f 14 8 2 (13-8)
  apply prefix_from_interval f 14 8 13 8 2 ?_ (by decide) (by decide) (by decide) (by decide)
    (Or.inr (by decide))
  intro i hi hb
  have hc : i=8 ∨ i=9 ∨ i=10 := by omega
  rcases hc with rfl | rfl | rfl <;> decide

theorem source_indexed : (extend index 14 0 2).extent=7 :=
  prefix_unique f 14 0 2 _ 7 (extend_correct f 14 0 2 (by decide)) source_prefix

theorem target_indexed : (extend index 14 8 2).extent=5 :=
  prefix_unique f 14 8 2 _ 5 (extend_correct f 14 8 2 (by decide)) target_prefix

theorem actual_copy : Agree f 14 2 8 6 := ⟨by decide,by decide,by decide⟩

theorem unique_past_break (p : Nat) (hp : p+2≤7) (heq : Agree f 14 p 8 (8-p)) : p=2 := by
  have hs:=prefix_move f 14 0 2 7 p source_prefix (by decide) (Nat.zero_le _) hp
  have he:=copy_past_break f 14 p 8 2 (7-p) 5 (8-p) hs target_prefix heq (by omega)
  omega

theorem actual_exceptional_selection : (select index 14 0 2 0 2 8 8).choice=.point 2 := by
  have hl:= (lce_agree_iff f 14 2 8 _ 6
    (lceMeasured_correct f 14 2 8 (by decide) (by decide))).mp actual_copy
  change 8-(0+7-5)≤(lceMeasured index 14 (0+7-5) 8).length at hl
  change (choose index 14 0 2 0 2 8 8
    (0+(extend index 14 0 2).extent) (extend index 14 8 2).extent).choice=_
  rw [source_indexed,target_indexed]
  unfold choose
  rw [if_neg (by decide : ¬8≤0+7)]
  dsimp only
  rw [if_pos (by decide : Member 0 2 0 2 (0+7-5) ∧ 0+7-5≤8),if_pos hl]

def alternating (i : Nat) : Fin 2 := ⟨i%2,Nat.mod_lt _ (by decide)⟩

theorem alternating_period : OnPeriod alternating 0 14 2 := by
  intro i _ _
  apply Fin.ext
  change i%2=(i+2)%2
  simp only [Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]

theorem alternating_source : PeriodPrefix alternating 14 0 2 14 :=
  prefix_from_interval alternating 14 0 14 0 2 alternating_period
    (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)

theorem alternating_target : PeriodPrefix alternating 14 8 2 6 :=
  prefix_from_interval alternating 14 0 14 8 2 alternating_period
    (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)

theorem actual_clipped_progression :
    (select (prepare alternating 14) 14 0 2 0 4 8 8).choice=.progression 0 2 2 4 := by
  have hs:=prefix_unique alternating 14 0 2 _ 14
    (extend_correct alternating 14 0 2 (by decide)) alternating_source
  have ht:=prefix_unique alternating 14 8 2 _ 6
    (extend_correct alternating 14 8 2 (by decide)) alternating_target
  change (choose (prepare alternating 14) 14 0 2 0 4 8 8
    (0+(extend (prepare alternating 14) 14 0 2).extent)
    (extend (prepare alternating 14) 14 8 2).extent).choice=_
  rw [hs,ht]
  rfl

theorem clipped_members :
    Choice.Holds (.progression 0 2 2 4) 2 ∧
    Choice.Holds (.progression 0 2 2 4) 4 ∧
    ¬Choice.Holds (.progression 0 2 2 4) 0 ∧
    ¬Choice.Holds (.progression 0 2 2 4) 3 := by
  change Member 0 2 2 4 2 ∧ Member 0 2 2 4 4 ∧ ¬Member 0 2 2 4 0 ∧ ¬Member 0 2 2 4 3
  decide

end REWB.BoundaryBorder.Regression
