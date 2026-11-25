import REWB.CountedJoin
import REWB.CountedProjection

/-! Actual formula-to-window construction. Each residue, conjunction,
affine traversal, output record and list concatenation is executed by a
counted loop. The value is exactly the frozen chronological join input.
Bounds use the already certified formula measure; no exponent interval
is expanded into its individual lengths. Arithmetic is a primitive in
this ledger, as in `CountedProjection`. -/
namespace REWB.PeriodicConstruction
open REWB.AffineProjection REWB.UniformProjection REWB.ExponentIntervals
abbrev Result (α : Type) := α×Nat

theorem read_bound (env : List Int) (i : Nat) :
    (CountedProjection.read env i).2≤i+1 := by
  induction env generalizing i with
  | nil => simp [CountedProjection.read]
  | cons z zs ih =>
    cases i with
    | zero => exact Nat.le_refl _
    | succ i =>
      change (CountedProjection.read zs i).2+1≤i+1+1
      exact Nat.add_le_add_right (ih i) 1

theorem eval_bound (env : List Int) (a : Aff) :
    (CountedProjection.eval env a).2≤affMeasure a := by
  induction a with
  | lit z => exact Nat.le_refl _
  | var i => exact Nat.add_le_add_right (read_bound env i) 1
  | add a b ia ib =>
    exact Nat.add_le_add_right (Nat.add_le_add ia ib) 1
  | scale c a ih =>
    have hh : affMeasure a+1≤(c.natAbs+1)*(affMeasure a+1) := by
      simpa using Nat.mul_le_mul_right (affMeasure a+1) (show 1≤c.natAbs+1 by omega)
    exact Nat.le_trans (Nat.add_le_add_right ih 1) hh

theorem split_bound (a : Aff) : (CountedProjection.split a).2≤2*affMeasure a := by
  induction a with
  | lit z => simp [CountedProjection.split,affMeasure]
  | var i => cases i <;> simp [CountedProjection.split,affMeasure] <;> omega
  | add a b ia ib =>
    simp only [CountedProjection.split,affMeasure,Nat.mul_add]
    omega
  | scale c a ih =>
    have hh : 2*(affMeasure a+1)≤2*((c.natAbs+1)*(affMeasure a+1)) :=
      Nat.mul_le_mul_left 2 (by
        simpa using Nat.mul_le_mul_right (affMeasure a+1) (show 1≤c.natAbs+1 by omega))
    simp only [CountedProjection.split,affMeasure,Nat.mul_add] at *
    omega

theorem map_bound (f : α→Result β) (xs : List α) (C : Nat)
    (h : ∀x,x∈xs→(f x).2≤C) :
    (CountedProjection.map f xs).2≤xs.length*(C+1)+1 := by
  induction xs with
  | nil => simp [CountedProjection.map,CountedProjection.flatMap]
  | cons x xs ih =>
    have hx:=h x List.mem_cons_self
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [CountedProjection.map,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem flatMap_bound (f : α→Result (List β)) (xs : List α) (C L : Nat)
    (hc : ∀x,x∈xs→(f x).2≤C) (hl : ∀x,x∈xs→(f x).1.length≤L) :
    (CountedProjection.flatMap f xs).2≤xs.length*(C+L+2)+1 := by
  induction xs with
  | nil => simp [CountedProjection.map,CountedProjection.flatMap]
  | cons x xs ih =>
    have hx:=hc x List.mem_cons_self
    have hxl:=hl x List.mem_cons_self
    have ht:=ih (fun y hy=>hc y (List.mem_cons_of_mem x hy))
      (fun y hy=>hl y (List.mem_cons_of_mem x hy))
    simp only [CountedProjection.flatMap,CountedProjection.append_steps,
      List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def applyAtom (K r : Nat) (I : Window) : Atom→Result Window
  | .le a =>
    let s:=CountedProjection.split a
    let e:=CountedProjection.eval [(r:Int)] a
    (clip I (s.1.1*(K:Int)) e.1,s.2+e.2+10)
  | .dvd m a =>
    let e:=CountedProjection.eval [(r:Int)] a
    (if e.1%(m:Int)=0 then I else empty,e.2+4)

theorem applyAtom_value (K r : Nat) (I : Window) (a : Atom) :
    (applyAtom K r I a).1=ExponentIntervals.applyAtom K r I a := by
  cases a <;> simp only [applyAtom,ExponentIntervals.applyAtom,
    CountedProjection.split_value,CountedProjection.eval_value]

theorem applyAtom_work (K r : Nat) (I : Window) (a : Atom) :
    (applyAtom K r I a).2≤13*atomMeasure a := by
  cases a with
  | le a =>
    have hs:=split_bound a
    have he:=eval_bound [(r:Int)] a
    simp only [applyAtom,atomMeasure,Nat.mul_add]
    omega
  | dvd m a =>
    have he:=eval_bound [(r:Int)] a
    simp only [applyAtom,atomMeasure,Nat.mul_add]
    omega

def clipConj (K r : Nat) (I : Window) : Conj→Result Window
  | [] => (I,1)
  | a::as =>
    let x:=applyAtom K r I a
    let y:=clipConj K r x.1 as
    (y.1,x.2+y.2+1)

theorem clipConj_value (K r : Nat) (I : Window) (C : Conj) :
    (clipConj K r I C).1=ExponentIntervals.clipConj K r I C := by
  induction C generalizing I with
  | nil => rfl
  | cons a as ih => simp only [clipConj,ExponentIntervals.clipConj,ih,applyAtom_value]

theorem clipConj_work (K r : Nat) (I : Window) (C : Conj) :
    (clipConj K r I C).2≤14*conjMeasure C+1 := by
  induction C generalizing I with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
    have ha:=applyAtom_work K r I a
    have ht:=ih (applyAtom K r I a).1
    simp only [clipConj,conjMeasure,Nat.mul_add]
    omega

def windows (K r N : Nat) (F : Formula) : Result (List Window) :=
  let I:=baseWindow K r N
  let z:=CountedProjection.map (clipConj K r I) F
  (z.1,z.2+4)

theorem windows_value (K r N : Nat) (F : Formula) :
    (windows K r N F).1=ExponentIntervals.windows K r N F := by
  simp only [windows,CountedProjection.map_value,clipConj_value,ExponentIntervals.windows]

theorem windows_work (K r N : Nat) (F : Formula) :
    (windows K r N F).2≤16*measure F+5 := by
  have aux : ∀F : Formula, (CountedProjection.map (clipConj K r (baseWindow K r N)) F).2≤
      16*measure F+1 := by
    intro F
    induction F with
    | nil => exact Nat.le_refl _
    | cons C Cs ih =>
      have hh:=clipConj_work K r (baseWindow K r N) C
      simp only [CountedProjection.map,UniformProjection.measure,Nat.mul_add]
      omega
  have h:=aux F
  unfold windows
  dsimp only
  omega

def allWindows (K N : Nat) (F : Formula) : Result (List (Nat×Window)) :=
  let rs:=CountedProjection.range K
  let out:=CountedProjection.flatMap (fun r=>
    let ws:=windows K r N F
    let tagged:=CountedProjection.map (fun I : Window=>((r,I),1)) ws.1
    (tagged.1,ws.2+tagged.2+1)) rs.1
  (out.1,rs.2+out.2+1)

theorem allWindows_value (K N : Nat) (F : Formula) :
    (allWindows K N F).1=ExponentIntervals.allWindows K N F := by
  simp only [allWindows,CountedProjection.flatMap_value,CountedProjection.map_value,
    windows_value,CountedProjection.range_value,ExponentIntervals.allWindows]

theorem allWindows_work (K N : Nat) (F : Formula) :
    (allWindows K N F).2≤24*K*(measure F+1)+3 := by
  have hl:=length_le_measure F
  have hc : ∀r, r∈(CountedProjection.range K).1→
      (let ws:=windows K r N F
       let tagged:=CountedProjection.map (fun I : Window=>((r,I),1)) ws.1
       (tagged.1,ws.2+tagged.2+1)).2≤18*measure F+7 := by
    intro r _
    have h:=windows_work K r N F
    dsimp only
    rw [CountedProjection.map_plain_steps,windows_value,ExponentIntervals.windows_length]
    omega
  have hm : ∀r,r∈(CountedProjection.range K).1→
      (let ws:=windows K r N F
       let tagged:=CountedProjection.map (fun I : Window=>((r,I),1)) ws.1
       (tagged.1,ws.2+tagged.2+1)).1.length≤measure F := by
    intro r _
    simp only [CountedProjection.map_value,List.length_map,windows_value,
      ExponentIntervals.windows_length]
    exact hl
  have h:=flatMap_bound _ (CountedProjection.range K).1 (18*measure F+7) (measure F) hc hm
  simp only [CountedProjection.range_value,List.length_range] at h
  have hr : (CountedProjection.range K).2=2*K+1 := CountedProjection.rangeFrom_steps 0 K
  unfold allWindows
  dsimp only
  rw [hr,CountedProjection.range_value]
  have hh := Nat.mul_le_mul_left K
    (show 18*measure F+7+measure F+2+2≤24*(measure F+1) by omega)
  rw [Nat.mul_add] at hh
  have he : K*(24*(measure F+1))=24*K*(measure F+1) := by ac_rfl
  rw [he] at hh
  omega

def records (K N : Nat) (e : KeyedJoin.Entry) : Result (List Window) :=
  let ws:=allWindows K N e.formula
  let out:=CountedProjection.map (fun p=>
    (KeyedJoin.encode N (e.key*K+p.1) p.2,12)) ws.1
  (out.1,ws.2+out.2+1)

theorem records_value (K N : Nat) (e : KeyedJoin.Entry) :
    (records K N e).1=KeyedJoin.records K N e := by
  simp only [records,CountedProjection.map_value,allWindows_value,KeyedJoin.records]

theorem records_work (K N : Nat) (e : KeyedJoin.Entry) :
    (records K N e).2≤40*K*(measure e.formula+1)+5 := by
  have h:=allWindows_work K N e.formula
  have hm:=Nat.mul_le_mul_left K (length_le_measure e.formula)
  unfold records
  dsimp only
  rw [CountedProjection.map_plain_steps,allWindows_value,ExponentIntervals.allWindows_length]
  have he : 40*K*(measure e.formula+1)=
      24*K*(measure e.formula+1)+16*(K*measure e.formula)+16*K := by
    simp only [Nat.mul_add,Nat.mul_one,Nat.mul_assoc]
    omega
  rw [he]
  omega

def prepare (K N : Nat) (es : List KeyedJoin.Entry) : Result (List Window) :=
  CountedProjection.flatMap (records K N) es

theorem prepare_value (K N : Nat) (es : List KeyedJoin.Entry) :
    (prepare K N es).1=KeyedJoin.prepare K N es := by
  simp only [prepare,CountedProjection.flatMap_value,records_value,KeyedJoin.prepare]

theorem prepare_work (K N : Nat) (es : List KeyedJoin.Entry) (B : Nat)
    (hb : ∀e,e∈es→measure e.formula≤B) :
    (prepare K N es).2≤es.length*(41*K*(B+1)+7)+1 := by
  have h:=flatMap_bound (records K N) es (40*K*(B+1)+5) (K*B)
    (fun e he=>Nat.le_trans (records_work K N e)
      (Nat.add_le_add_right (Nat.mul_le_mul_left (40*K) (Nat.add_le_add_right (hb e he) 1)) 5))
    (fun e he=>by
      rw [records_value,KeyedJoin.records_length]
      exact Nat.mul_le_mul_left K (Nat.le_trans (length_le_measure _) (hb e he)))
  apply Nat.le_trans h
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  have he : 41*K*(B+1)=40*K*(B+1)+K*B+K := by
    simp only [Nat.mul_add,Nat.mul_one,Nat.mul_assoc]
    omega
  omega

end REWB.PeriodicConstruction
