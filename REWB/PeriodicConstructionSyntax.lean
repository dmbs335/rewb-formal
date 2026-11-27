import REWB.PeriodicConstructionFormula

/-! Traversal bounds independent of the numeric affine coefficients.
This is the relevant measure for clipping a physical progression:
the period q is a coefficient, not an iteration count. Integer
arithmetic is charged as a primitive, consistently with the projection
ledger. These bounds apply to the actual counted window constructors. -/
namespace REWB.PeriodicConstruction.Syntax
open REWB.AffineProjection REWB.PeriodicConstruction

def aff : Aff→Nat
  | .lit _ => 1
  | .var i => i+2
  | .add a b => aff a+aff b+1
  | .scale _ a => aff a+1

def atom : Atom→Nat
  | .le a | .dvd _ a => aff a+1

def conj : Conj→Nat
  | [] => 0
  | a::as => atom a+conj as+1

def formula : AffineProjection.Formula→Nat
  | [] => 0
  | C::Cs => conj C+formula Cs+1

theorem eval_work (env : List Int) (a : Aff) :
    (CountedProjection.eval env a).2≤aff a := by
  induction a with
  | lit _ => exact Nat.le_refl _
  | var i => exact Nat.add_le_add_right (read_bound env i) 1
  | add a b ia ib => exact Nat.add_le_add_right (Nat.add_le_add ia ib) 1
  | scale _ a ih => exact Nat.add_le_add_right ih 1

theorem split_work (a : Aff) : (CountedProjection.split a).2≤2*aff a := by
  induction a with
  | lit _ => simp [CountedProjection.split,aff]
  | var i => cases i <;> simp [CountedProjection.split,aff] <;> omega
  | add a b ia ib =>
    simp only [CountedProjection.split,aff,Nat.mul_add]
    omega
  | scale _ a ih =>
    simp only [CountedProjection.split,aff,Nat.mul_add]
    omega

theorem length_le_formula (F : AffineProjection.Formula) : F.length≤formula F := by
  induction F with
  | nil => exact Nat.le_refl _
  | cons C Cs ih => simp only [List.length_cons,formula]; omega

theorem applyAtom_work (K r : Nat) (I : ExponentIntervals.Window) (a : Atom) :
    (PeriodicConstruction.applyAtom K r I a).2≤13*atom a := by
  cases a with
  | le a =>
    have hs:=split_work a
    have he:=eval_work [(r:Int)] a
    simp only [PeriodicConstruction.applyAtom,atom,Nat.mul_add]
    omega
  | dvd m a =>
    have he:=eval_work [(r:Int)] a
    simp only [PeriodicConstruction.applyAtom,atom,Nat.mul_add]
    omega

theorem clipConj_work (K r : Nat) (I : ExponentIntervals.Window) (C : Conj) :
    (PeriodicConstruction.clipConj K r I C).2≤14*conj C+1 := by
  induction C generalizing I with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
    have ha:=applyAtom_work K r I a
    have ht:=ih (PeriodicConstruction.applyAtom K r I a).1
    simp only [PeriodicConstruction.clipConj,conj,Nat.mul_add]
    omega

theorem windows_work (K r N : Nat) (F : AffineProjection.Formula) :
    (PeriodicConstruction.windows K r N F).2≤16*formula F+5 := by
  have aux : ∀F : AffineProjection.Formula,
      (CountedProjection.map (PeriodicConstruction.clipConj K r
        (ExponentIntervals.baseWindow K r N)) F).2≤16*formula F+1 := by
    intro F
    induction F with
    | nil => exact Nat.le_refl _
    | cons C Cs ih =>
      have hh:=clipConj_work K r (ExponentIntervals.baseWindow K r N) C
      simp only [CountedProjection.map,formula,Nat.mul_add]
      omega
  have h:=aux F
  unfold PeriodicConstruction.windows
  dsimp only
  omega

theorem allWindows_work (K N : Nat) (F : AffineProjection.Formula) :
    (PeriodicConstruction.allWindows K N F).2≤24*K*(formula F+1)+3 := by
  have hl:=length_le_formula F
  have hc : ∀r, r∈(CountedProjection.range K).1→
      (let ws:=PeriodicConstruction.windows K r N F
       let tagged:=CountedProjection.map (fun I : ExponentIntervals.Window=>((r,I),1)) ws.1
       (tagged.1,ws.2+tagged.2+1)).2≤18*formula F+7 := by
    intro r _
    have h:=windows_work K r N F
    dsimp only
    rw [CountedProjection.map_plain_steps,windows_value,ExponentIntervals.windows_length]
    omega
  have hm : ∀r,r∈(CountedProjection.range K).1→
      (let ws:=PeriodicConstruction.windows K r N F
       let tagged:=CountedProjection.map (fun I : ExponentIntervals.Window=>((r,I),1)) ws.1
       (tagged.1,ws.2+tagged.2+1)).1.length≤formula F := by
    intro r _
    simp only [CountedProjection.map_value,List.length_map,windows_value,
      ExponentIntervals.windows_length]
    exact hl
  have h:=flatMap_bound _ (CountedProjection.range K).1 (18*formula F+7) (formula F) hc hm
  simp only [CountedProjection.range_value,List.length_range] at h
  have hr : (CountedProjection.range K).2=2*K+1 := CountedProjection.rangeFrom_steps 0 K
  unfold PeriodicConstruction.allWindows
  dsimp only
  rw [hr,CountedProjection.range_value]
  have hh:=Nat.mul_le_mul_left K
    (show 18*formula F+7+formula F+2+2≤24*(formula F+1) by omega)
  rw [Nat.mul_add] at hh
  have he : K*(24*(formula F+1))=24*K*(formula F+1) := by ac_rfl
  rw [he] at hh
  omega

def Atoms (F : AffineProjection.Formula) (S : Nat) : Prop :=
  ∀C,C∈F→∀a,a∈C→atom a≤S

theorem conj_bound (C : Conj) (S : Nat) (h : ∀a,a∈C→atom a≤S) :
    conj C≤C.length*(S+1) := by
  induction C with
  | nil => simp [conj]
  | cons a as ih =>
    have ha:=h a List.mem_cons_self
    have ht:=ih (fun b hb=>h b (List.mem_cons_of_mem a hb))
    simp only [conj,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem formula_bound (F : AffineProjection.Formula) (B A S : Nat)
    (hshape : PeriodicConstruction.Formula.Shape F B A) (hatoms : Atoms F S) :
    formula F≤B*(A*(S+1)+1) := by
  have aux : ∀F : AffineProjection.Formula,
      (∀C,C∈F→C.length≤A)→Atoms F S→formula F≤F.length*(A*(S+1)+1) := by
    intro F hshape hatoms
    induction F with
    | nil => simp [formula]
    | cons C Cs ih =>
      have hc:=Nat.le_trans (conj_bound C S (hatoms C List.mem_cons_self))
        (Nat.mul_le_mul_right (S+1) (hshape C List.mem_cons_self))
      have ht:=ih (fun D hd=>hshape D (List.mem_cons_of_mem C hd))
        (fun D hd=>hatoms D (List.mem_cons_of_mem C hd))
      simp only [formula,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  exact Nat.le_trans (aux F hshape.2 hatoms) (Nat.mul_le_mul_right _ hshape.1)

theorem atoms_both (F G : AffineProjection.Formula) (S : Nat)
    (hf : Atoms F S) (hg : Atoms G S) : Atoms (PhaseSolver.both F G) S := by
  intro C hc a ha
  obtain ⟨X,hx,hm⟩:=List.mem_flatMap.mp hc
  obtain ⟨Y,hy,rfl⟩:=List.mem_map.mp hm
  rcases List.mem_append.mp ha with ha|ha
  · exact hf X hx a ha
  · exact hg Y hy a ha

theorem atoms_mono (F : AffineProjection.Formula) (S T : Nat)
    (h : Atoms F S) (hle : S≤T) : Atoms F T :=
  fun C hc a ha=>Nat.le_trans (h C hc a ha) hle

theorem atoms_le (a b : Aff) : Atoms (PhaseSolver.le a b) (aff a+aff b+3) := by
  intro C hc x hx
  simp only [PhaseSolver.le,PhaseSolver.unit,List.mem_singleton] at hc
  subst C
  simp only [List.mem_singleton] at hx
  subst x
  simp only [atom,Aff.sub,aff]
  omega

theorem atoms_descriptor (D : FiniteOrbit.Descriptor) (t : Aff) :
    Atoms (AffineProjection.descriptorFormula D t) (aff t+4) := by
  intro C hc a ha
  rcases List.mem_append.mp hc with hc|hc
  · obtain ⟨k,_,rfl⟩:=List.mem_map.mp hc
    simp only [exactCount,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> simp [atom,Aff.sub,aff] <;> omega
  · obtain ⟨r,_,rfl⟩:=List.mem_map.mp hc
    simp only [progression,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> simp [atom,Aff.sub,aff] <;> omega

end REWB.PeriodicConstruction.Syntax
