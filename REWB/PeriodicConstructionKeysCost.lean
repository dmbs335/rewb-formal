import REWB.PeriodicConstructionKeys

/-! Bounds for actual word/rank/list construction, using the already
proved packing theorem for canonical cubic runs. No run is enumerated or
interned again to obtain a counter. -/
namespace REWB.PeriodicConstruction.Keys
variable {σ : Nat}

theorem length_le_phase (f : Nat→Fin σ) (n : Nat) (rs : List RunGeometry.Bounds)
    (hv : ∀ r,r∈rs→r.Valid f n) : rs.length≤RunBudget.phaseWork 0 rs := by
  induction rs with
  | nil=>simp [RunBudget.phaseWork]
  | cons r rs ih=>
    have hp:= (hv r (by simp)).2.2.2.1.1
    have ht:=ih (fun s hs=>hv s (by simp [hs]))
    simp only [List.length_cons,RunBudget.phaseWork,Nat.zero_add,Nat.pow_one]
    omega

namespace Rotation

theorem tables_work (R : ExactKeys.Registry σ) (f : Nat→Fin σ)
    (rs : List RunGeometry.Bounds) :
    (tables R f rs).2≤(ExactKeys.buildRunTables R f rs).work+
      32*(RunBudget.phaseWork 1 rs+RunBudget.phaseWork 0 rs+rs.length)+1 := by
  induction rs generalizing R with
  | nil=>simp [tables,ExactKeys.buildRunTables,RunBudget.phaseWork]
  | cons r rs ih=>
    have ha:=intern_work R (Periodic.shift f r.lo) r.period
    have hb:=ih (intern R (Periodic.shift f r.lo) r.period).1.registry
    rw [intern_value] at hb
    simp only [tables,intern_value,ExactKeys.buildRunTables,RunBudget.phaseWork,
      List.length_cons,Nat.zero_add,Nat.pow_one,
      show (1:Nat)+1=2 from rfl,Nat.mul_add,Nat.mul_one]
    omega

theorem tables_cubic_work (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (n Q : Nat)
    (rs : List RunGeometry.Bounds) (hd : rs.Nodup)
    (hv : ∀ r,r∈rs→r.Valid f n)
    (hc : ∀ r,r∈rs→r.period≤Q ∧ 3*r.period≤r.hi-r.lo) :
    (tables R f rs).2≤
      ((3*σ+1)*Q+1+32*(Q+2))*(2*n*DyadicIndex.heightFor n)+1 := by
  have hw:=tables_work R f rs
  have ho:=ExactKeys.buildRunTables_cubic_cost R f n Q rs hd hv hc
  have h1:=RunBudget.cubic_phase_bound f n 1 Q rs hd hv hc
  have h0:=RunBudget.cubic_phase_bound f n 0 Q rs hd hv hc
  simp only [Nat.pow_one] at h1
  simp only [Nat.pow_zero,Nat.one_mul] at h0
  have hl:=Nat.le_trans (length_le_phase f n rs hv) h0
  calc
    _ ≤ (ExactKeys.buildRunTables R f rs).work+
        32*(RunBudget.phaseWork 1 rs+RunBudget.phaseWork 0 rs+rs.length)+1 := hw
    _ ≤ ((3*σ+1)*Q+1)*(2*n*DyadicIndex.heightFor n)+
        32*(Q*(2*n*DyadicIndex.heightFor n)+(2*n*DyadicIndex.heightFor n)+
          (2*n*DyadicIndex.heightFor n))+1 :=
      Nat.add_le_add_right (Nat.add_le_add ho
        (Nat.mul_le_mul_left 32 (Nat.add_le_add (Nat.add_le_add h1 h0) hl))) 1
    _ = _ := by simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]; omega

theorem concrete_work (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (n Q : Nat) :
    (tables R f (SmallPeriodRuns.cubic f n Q)).2≤
      ((3*σ+1)*Q+1+32*(Q+2))*(2*n*DyadicIndex.heightFor n)+1 :=
  tables_cubic_work R f n Q _ (SmallPeriodRuns.cubic_nodup f n Q)
    (fun r hr=>((SmallPeriodRuns.cubic_mem f n Q r).mp hr).1)
    (fun r hr=>((SmallPeriodRuns.cubic_mem f n Q r).mp hr).2)

end Rotation

namespace Short

theorem tables_work (R : ExactKeys.Registry σ) (f : Nat→Fin σ)
    (rs : List RunGeometry.Bounds) :
    (tables R f rs).2≤(P1ShortKeys.buildRunTables R f rs).work+
      256*(RunBudget.phaseWork 2 rs+RunBudget.phaseWork 1 rs+rs.length)+1 := by
  induction rs generalizing R with
  | nil=>simp [tables,P1ShortKeys.buildRunTables,RunBudget.phaseWork]
  | cons r rs ih=>
    have ha:=intern_work R (Periodic.shift f r.lo) r.period
    have hb:=ih (intern R (Periodic.shift f r.lo) r.period).1.registry
    rw [intern_value] at hb
    simp only [tables,intern_value,P1ShortKeys.buildRunTables,RunBudget.phaseWork,
      List.length_cons,show (2:Nat)+1=3 from rfl,
      show (1:Nat)+1=2 from rfl,Nat.mul_add,Nat.mul_one] at ha ⊢
    omega

theorem tables_cubic_work (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (n Q : Nat)
    (rs : List RunGeometry.Bounds) (hd : rs.Nodup)
    (hv : ∀ r,r∈rs→r.Valid f n)
    (hc : ∀ r,r∈rs→r.period≤Q ∧ 3*r.period≤r.hi-r.lo) :
    (tables R f rs).2≤
      (P1ShortKeys.workConstant σ*Q^2+3*Q+256*(Q^2+Q+1))*
        (2*n*DyadicIndex.heightFor n)+1 := by
  have hw:=tables_work R f rs
  have ho:=P1ShortKeys.buildRunTables_cubic_cost R f n Q rs hd hv hc
  have h2:=RunBudget.cubic_phase_bound f n 2 Q rs hd hv hc
  have h1:=RunBudget.cubic_phase_bound f n 1 Q rs hd hv hc
  have h0:=RunBudget.cubic_phase_bound f n 0 Q rs hd hv hc
  simp only [Nat.pow_one] at h1
  simp only [Nat.pow_zero,Nat.one_mul] at h0
  have hl:=Nat.le_trans (length_le_phase f n rs hv) h0
  calc
    _ ≤ (P1ShortKeys.buildRunTables R f rs).work+
        256*(RunBudget.phaseWork 2 rs+RunBudget.phaseWork 1 rs+rs.length)+1 := hw
    _ ≤ (P1ShortKeys.workConstant σ*Q^2+3*Q)*(2*n*DyadicIndex.heightFor n)+
        256*(Q^2*(2*n*DyadicIndex.heightFor n)+Q*(2*n*DyadicIndex.heightFor n)+
          (2*n*DyadicIndex.heightFor n))+1 :=
      Nat.add_le_add_right (Nat.add_le_add ho
        (Nat.mul_le_mul_left 256 (Nat.add_le_add (Nat.add_le_add h2 h1) hl))) 1
    _ = _ := by simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.one_mul]

theorem concrete_work (R : ExactKeys.Registry σ) (f : Nat→Fin σ) (n Q : Nat) :
    (tables R f (SmallPeriodRuns.cubic f n Q)).2≤
      (P1ShortKeys.workConstant σ*Q^2+3*Q+256*(Q^2+Q+1))*
        (2*n*DyadicIndex.heightFor n)+1 :=
  tables_cubic_work R f n Q _ (SmallPeriodRuns.cubic_nodup f n Q)
    (fun r hr=>((SmallPeriodRuns.cubic_mem f n Q r).mp hr).1)
    (fun r hr=>((SmallPeriodRuns.cubic_mem f n Q r).mp hr).2)

end Short
end REWB.PeriodicConstruction.Keys
