import REWB.IntervalSweep

/-! Encode exact string-key ranks and residue classes in disjoint integer
    slabs. This makes one sorted interval sweep sufficient even for many
    different keys. Key ranks must be collision-free; this module does
    not build the suffix-rank dictionary. -/
namespace REWB.KeyedJoin
open REWB.ExponentIntervals REWB.IntervalSweep
open REWB.AffineProjection

structure Entry where
  key : Nat
  formula : Formula
  deriving Repr

def offset (N key : Nat) : Int := (key:Int)*((N:Int)+1)

def encode (N key : Nat) (I : Window) : Window :=
  let J := I.meet ⟨0,N⟩
  ⟨offset N key+J.lo,offset N key+J.hi⟩

theorem encode_has (N key : Nat) (I : Window) (x : Int) :
    (encode N key I).has x ↔
      I.has (x-offset N key) ∧ (0≤x-offset N key ∧ x-offset N key≤(N:Int)) := by
  have h : (encode N key I).has x ↔ (I.meet ⟨0,(N:Int)⟩).has (x-offset N key) := by
    unfold encode Window.has
    dsimp only
    omega
  rw [h,Window.meet_has]
  rfl

theorem offset_separate (N k l : Nat) (h : k<l) :
    offset N k+(N:Int)<offset N l := by
  have hh : (k:Int)+1≤(l:Int) := by omega
  have hp : 0≤(N:Int)+1 := by omega
  have hm := Int.mul_le_mul_of_nonneg_right hh hp
  rw [Int.add_mul,Int.one_mul] at hm
  unfold offset
  omega

theorem encode_hit (N k l : Nat) (I J : Window) :
    Hit (encode N k I) (encode N l J) ↔
      k=l ∧ ∃ z : Int, I.has z ∧ J.has z ∧ 0≤z ∧ z≤(N:Int) := by
  constructor
  · rintro ⟨x,hi,hj⟩
    obtain ⟨hI,hI0,hIN⟩ := (encode_has N k I x).mp hi
    obtain ⟨hJ,hJ0,hJN⟩ := (encode_has N l J x).mp hj
    have hkl : k=l := by
      by_cases he : k=l
      · exact he
      · by_cases h : k<l
        · have hh := offset_separate N k l h
          omega
        · have hh := offset_separate N l k (by omega)
          omega
    subst l
    exact ⟨rfl,x-offset N k,hI,hJ,hI0,hIN⟩
  · rintro ⟨rfl,z,hI,hJ,h0,hN⟩
    refine ⟨offset N k+z,?_,?_⟩
    · apply (encode_has N k I _).mpr
      have he : offset N k+z-offset N k=z := by omega
      rw [he]
      exact ⟨hI,h0,hN⟩
    · apply (encode_has N k J _).mpr
      have he : offset N k+z-offset N k=z := by omega
      rw [he]
      exact ⟨hJ,h0,hN⟩

def records (K N : Nat) (E : Entry) : List Window :=
  (allWindows K N E.formula).map (fun p=>encode N (E.key*K+p.1) p.2)

theorem records_mem (K N : Nat) (E : Entry) (W : Window) :
    W∈records K N E ↔ ∃ r,r<K ∧ ∃ I,I∈windows K r N E.formula ∧
      encode N (E.key*K+r) I=W := by
  unfold records allWindows
  constructor
  · intro h
    obtain ⟨⟨r,I⟩,hm,he⟩ := List.mem_map.mp h
    obtain ⟨s,hs,hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨J,hJ,hj⟩ := List.mem_map.mp hm
    cases hj
    exact ⟨r,List.mem_range.mp hs,I,hJ,he⟩
  · rintro ⟨r,hr,I,hI,rfl⟩
    exact List.mem_map.mpr ⟨(r,I),List.mem_flatMap.mpr
      ⟨r,List.mem_range.mpr hr,List.mem_map.mpr ⟨I,hI,rfl⟩⟩,rfl⟩

def prepare (K N : Nat) (es : List Entry) : List Window :=
  es.flatMap (records K N)

def weight : List Entry→Nat
  | [] => 0
  | e::es => e.formula.length+weight es

theorem records_length (K N : Nat) (E : Entry) :
    (records K N E).length=K*E.formula.length := by
  simp only [records,List.length_map,allWindows_length]

theorem prepare_length (K N : Nat) (es : List Entry) :
    (prepare K N es).length=K*weight es := by
  induction es with
  | nil => simp [prepare,weight]
  | cons e es ih =>
    change (records K N e++prepare K N es).length=K*(e.formula.length+weight es)
    rw [List.length_append,records_length,ih,Nat.mul_add]

def Good (K : Nat) (es : List Entry) : Prop := ∀ E,E∈es→Compatible K E.formula

def Match (N : Nat) (es fs : List Entry) : Prop :=
  ∃ E,E∈es ∧ ∃ F,F∈fs ∧ E.key=F.key ∧
    ∃ m : Nat,m≤N ∧ Satisfies E.formula [(m:Int)] ∧ Satisfies F.formula [(m:Int)]

theorem pack_inj (K k l r s : Nat) (hr : r<K) (hs : s<K)
    (h : k*K+r=l*K+s) : k=l ∧ r=s :=
  (PhaseSolver.length_unique K k l r s hr hs).mp h

theorem prepare_hit (K N : Nat) (es fs : List Entry)
    (hK : 0<K) (he : Good K es) (hf : Good K fs) :
    HasHit (prepare K N es) (prepare K N fs) ↔ Match N es fs := by
  constructor
  · rintro ⟨I,hI,J,hJ,hIJ⟩
    obtain ⟨E,hE,hIE⟩ := List.mem_flatMap.mp hI
    obtain ⟨F,hF,hJF⟩ := List.mem_flatMap.mp hJ
    obtain ⟨r,hr,U,hU,rfl⟩ := (records_mem K N E I).mp hIE
    obtain ⟨s,hs,V,hV,rfl⟩ := (records_mem K N F J).mp hJF
    obtain ⟨hkey,z,hUz,hVz,h0,hN⟩ := (encode_hit N (E.key*K+r) (F.key*K+s) U V).mp hIJ
    obtain ⟨heq,hrs⟩ := pack_inj K E.key F.key r s hr hs hkey
    subst s
    obtain ⟨⟨hm0,hmN⟩,hmE⟩ :=
      (windows_correct K r N E.formula z hK hr (he E hE)).mp ⟨U,hU,hUz⟩
    obtain ⟨_,hmF⟩ :=
      (windows_correct K r N F.formula z hK hr (hf F hF)).mp ⟨V,hV,hVz⟩
    let m := ((r:Int)+(K:Int)*z).toNat
    have hm : (m:Int)=(r:Int)+(K:Int)*z := by
      dsimp [m]
      rw [Int.ofNat_toNat]
      omega
    refine ⟨E,hE,F,hF,heq,m,by omega,?_,?_⟩
    · rwa [hm]
    · rwa [hm]
  · rintro ⟨E,hE,F,hF,hkey,m,hm,hmE,hmF⟩
    let r := m%K
    let z := Int.ofNat (m/K)
    have hr : r<K := Nat.mod_lt m hK
    have heq : (r:Int)+(K:Int)*z=(m:Int) := by
      have hh := congrArg Int.ofNat (Nat.mod_add_div m K)
      simpa only [Int.ofNat_add,Int.ofNat_mul,r,z] using hh
    have hz0 : 0≤z := Int.ofNat_nonneg _
    have hzN : z≤(N:Int) := by
      have hh : m/K≤m := Nat.div_le_self _ _
      change (Int.ofNat (m/K))≤(N:Int)
      exact Int.ofNat_le.mpr (Nat.le_trans hh hm)
    obtain ⟨U,hU,hUz⟩ := (windows_correct K r N E.formula z hK hr (he E hE)).mpr
      ⟨⟨by rw [heq]; exact Int.ofNat_nonneg _,by rw [heq]; exact Int.ofNat_le.mpr hm⟩,
        by rwa [heq]⟩
    obtain ⟨V,hV,hVz⟩ := (windows_correct K r N F.formula z hK hr (hf F hF)).mpr
      ⟨⟨by rw [heq]; exact Int.ofNat_nonneg _,by rw [heq]; exact Int.ofNat_le.mpr hm⟩,
        by rwa [heq]⟩
    refine ⟨encode N (E.key*K+r) U,List.mem_flatMap.mpr ⟨E,hE,
      (records_mem K N E _).mpr ⟨r,hr,U,hU,rfl⟩⟩,
      encode N (F.key*K+r) V,List.mem_flatMap.mpr ⟨F,hF,
      (records_mem K N F _).mpr ⟨r,hr,V,hV,rfl⟩⟩,?_⟩
    exact (encode_hit N _ _ _ _).mpr ⟨by rw [hkey],z,hUz,hVz,hz0,hzN⟩

def batch (K N : Nat) (es fs : List Entry) : Bool×Nat :=
  IntervalSweep.batch (prepare K N es) (prepare K N fs)

theorem batch_correct (K N : Nat) (es fs : List Entry)
    (hK : 0<K) (he : Good K es) (hf : Good K fs) :
    (batch K N es fs).1=true ↔ Match N es fs :=
  (IntervalSweep.batch_correct _ _).trans (prepare_hit K N es fs hK he hf)

theorem batch_cost (K N : Nat) (es fs : List Entry) :
    (batch K N es fs).2≤K*(weight es+weight fs) := by
  have h := IntervalSweep.batch_cost (prepare K N es) (prepare K N fs)
  rw [prepare_length,prepare_length,← Nat.mul_add] at h
  exact h

end REWB.KeyedJoin
