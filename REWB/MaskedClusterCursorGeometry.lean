import REWB.MaskedClusterPass

/-! Exact candidate windows for the two cursor modes. The incoming
    overshoot skips exactly the first start; the outgoing overshoot can
    occur only at the last start. The physical tests use current length
    L, and the local-anchor overlap certificate justifies using H-based
    cached endpoints without changing the candidate set.
-/
namespace REWB.MaskedCluster

def cursor (s incoming : Nat) (mode : Bool) : Nat := if mode then incoming else s
def lower (mode : Bool) : Nat := if mode then 1 else 0
def modeAllowed (enabled mode : Bool) : Bool := !mode || enabled
def overMode (s q m H next : Nat) : Bool := decide (next<s+m*q+H)
def normalHi (s q m H next : Nat) : Nat := if overMode s q m H next then m-1 else m

theorem modeAllowed_iff (enabled mode : Bool) :
    modeAllowed enabled mode=true ↔ (mode=true→enabled=true) := by
  cases enabled <;> cases mode <;> decide

theorem normalHi_le (s q m H next : Nat) : normalHi s q m H next≤m := by
  unfold normalHi
  split <;> omega

theorem normalHi_end (s q m H next : Nat) (hp : s+(m-1)*q+H≤next) :
    s+normalHi s q m H next*q+H≤next := by
  by_cases ho : next<s+m*q+H
  · simpa only [normalHi,overMode,ho,decide_true,if_true] using hp
  · simp only [normalHi,overMode,ho,decide_false,Bool.false_eq_true,if_false]
    omega

theorem normal_current (s q m L H next k : Nat) (hLH : L≤H)
    (hp : s+(m-1)*q+H≤next) (hover : (next<s+m*q+H ↔ next<s+m*q+L)) :
    (k≤m ∧ s+k*q+L≤next) ↔ k≤normalHi s q m H next := by
  by_cases ho : next<s+m*q+H
  · have hoL:=hover.mp ho
    simp only [normalHi,overMode,ho,decide_true,if_true]
    constructor
    · rintro ⟨hk,hend⟩
      have hne : k≠m := by intro he; subst k; omega
      omega
    · intro hk
      have hm:=Nat.mul_le_mul_right q hk
      exact ⟨by omega,by omega⟩
  · simp only [normalHi,overMode,ho,decide_false,Bool.false_eq_true,if_false]
    constructor
    · exact And.left
    · intro hk
      have hm:=Nat.mul_le_mul_right q hk
      exact ⟨hk,by omega⟩

theorem overshoot_current (s q m L H next k : Nat) (hLH : L≤H)
    (hp : s+(m-1)*q+H≤next) (hover : (next<s+m*q+H ↔ next<s+m*q+L)) :
    (k≤m ∧ next<s+k*q+L) ↔ overMode s q m H next=true ∧ k=m := by
  simp only [overMode,decide_eq_true_eq]
  constructor
  · rintro ⟨hk,hend⟩
    have he : k=m := by
      by_cases he : k=m
      · exact he
      · have hk' : k≤m-1 := by omega
        have hm:=Nat.mul_le_mul_right q hk'
        omega
    exact ⟨hover.mpr (by simpa only [he] using hend),he⟩
  · rintro ⟨ho,rfl⟩
    exact ⟨Nat.le_refl _,hover.mp ho⟩

theorem incoming_index (s q incoming k : Nat) (hq : 0<q)
    (hlo : s<incoming) (hhi : incoming≤s+q) : incoming≤s+k*q ↔ 1≤k := by
  constructor
  · intro h
    by_cases hz : k=0
    · simp only [hz,Nat.zero_mul,Nat.add_zero] at h
      omega
    · omega
  · intro hk
    have hm:=Nat.mul_le_mul_right q hk
    simp only [Nat.one_mul] at hm
    omega

theorem cursor_candidate (s q incoming k : Nat) (enabled mode : Bool) (hq : 0<q)
    (ha : modeAllowed enabled mode=true)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) :
    cursor s incoming mode≤s+k*q ↔ lower mode≤k := by
  cases mode with
  | false => simp only [cursor,lower,Bool.false_eq_true,if_false]; omega
  | true =>
    have he:=((modeAllowed_iff enabled true).mp ha) rfl
    exact incoming_index s q incoming k hq (hin he).1 (hin he).2

theorem cursor_before_lower (s q incoming : Nat) (enabled mode : Bool)
    (ha : modeAllowed enabled mode=true)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) :
    cursor s incoming mode≤s+lower mode*q := by
  cases mode with
  | false => simp [cursor,lower]
  | true =>
    have he:=((modeAllowed_iff enabled true).mp ha) rfl
    simpa only [cursor,lower,if_true,Nat.one_mul] using (hin he).2

theorem lower_le_last (mode : Bool) (m : Nat) (hm : 0<m) : lower mode≤m := by
  cases mode <;> simp only [lower,Bool.false_eq_true,if_false,if_true] <;> omega

theorem cursor_before_last (s q m incoming : Nat) (enabled mode : Bool) (hm : 0<m)
    (ha : modeAllowed enabled mode=true)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) :
    cursor s incoming mode≤s+m*q := by
  have hi:=cursor_before_lower s q incoming enabled mode ha hin
  have hmul:=Nat.mul_le_mul_right q (lower_le_last mode m hm)
  omega

theorem cursor_before_next (s q m next incoming : Nat) (enabled mode : Bool) (hm : 0<m)
    (hs : s+m*q<next) (ha : modeAllowed enabled mode=true)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) :
    cursor s incoming mode≤next := by
  have h:=cursor_before_last s q m incoming enabled mode hm ha hin
  omega

end REWB.MaskedCluster
