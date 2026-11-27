import REWB.ResidualStripScheduleDedup

/-! Arithmetic cut-grid enumeration. Separated maximal strips emit one
direct job. Only overlapping strips enumerate cuts, beginning at their
own first grid quotient; no global grid is rescanned for each strip. -/
namespace REWB.ResidualStripSchedule
open REWB.IndexedGrid REWB.GlobalCoverage

structure Job where
  origin : Strip
  cut : Option Nat
  left : Nat
  right : Nat
  deriving Repr, DecidableEq

def Job.distance (W : Job) : Nat := W.origin.distance
def direct (R : Strip) : Job := ⟨R,none,R.lo,R.hi⟩
def atCut (D : Nat) (R : Strip) (a : Nat) : Job :=
  ⟨R,some a,max R.lo (a*D-R.distance),min R.hi (a*D)⟩

def Eligible (L : Nat) (W : Job) : Prop := W.left<W.right ∧ L≤W.right-W.left
instance (L : Nat) (W : Job) : Decidable (Eligible L W) := inferInstanceAs (Decidable (_∧_))

structure Jobs where
  jobs : List Job := []
  queries : Nat := 0
  probes : Nat := 0
  work : Nat := 1
  deriving Repr

def cutLoop (D L : Nat) (R : Strip) (start : Nat) : Nat→Jobs
  | 0 => {}
  | steps+1 =>
      let W:=atCut D R start
      let tail:=cutLoop D L R (start+1) steps
      if Eligible L W then
        ⟨W::tail.jobs,tail.queries+1,tail.probes+1,tail.work+12⟩
      else ⟨tail.jobs,tail.queries,tail.probes+1,tail.work+9⟩

def cutTail (D L : Nat) (R : Strip) (start : Nat)
    (acc : List Job) (queries probes work : Nat) : Nat→Jobs
  | 0 => ⟨acc.reverse,queries,probes,work+1⟩
  | steps+1 =>
      let W:=atCut D R start
      if Eligible L W then cutTail D L R (start+1) (W::acc) (queries+1) (probes+1) (work+12) steps
      else cutTail D L R (start+1) acc queries (probes+1) (work+9) steps

theorem cutTail_spec (D L : Nat) (R : Strip) (start steps : Nat)
    (acc : List Job) (queries probes work : Nat) :
    cutTail D L R start acc queries probes work steps=
      ⟨acc.reverse++(cutLoop D L R start steps).jobs,
       queries+(cutLoop D L R start steps).queries,
       probes+(cutLoop D L R start steps).probes,work+(cutLoop D L R start steps).work⟩ := by
  induction steps generalizing start acc queries probes work with
  | zero => simp [cutTail,cutLoop]
  | succ steps ih =>
    simp only [cutTail,cutLoop]
    split <;> rw [ih] <;> simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    · congr 1 <;> omega
    · congr 1 <;> omega

def cutLoopTR (D L : Nat) (R : Strip) (start steps : Nat) : Jobs := cutTail D L R start [] 0 0 0 steps

@[csimp] theorem cutLoop_eq_cutLoopTR : cutLoop=cutLoopTR := by
  funext D L R start steps
  simp only [cutLoopTR,cutTail_spec,List.reverse_nil,List.nil_append,Nat.zero_add]

theorem cutLoop_mem (D L : Nat) (R : Strip) (start steps : Nat) (W : Job) :
    W∈(cutLoop D L R start steps).jobs ↔
      ∃a,start≤a ∧ a<start+steps ∧ Eligible L (atCut D R a) ∧ W=atCut D R a := by
  induction steps generalizing start with
  | zero =>
    simp only [cutLoop,List.not_mem_nil,Nat.add_zero]
    constructor
    · intro h; exact False.elim h
    · rintro ⟨a,ha,hb,_⟩; omega
  | succ steps ih =>
    simp only [cutLoop]
    split
    next he =>
      rw [List.mem_cons,ih]
      constructor
      · rintro (hw|⟨a,ha,hb,hE,hW⟩)
        · exact ⟨start,Nat.le_refl _,by omega,he,hw⟩
        · exact ⟨a,by omega,by omega,hE,hW⟩
      · rintro ⟨a,ha,hb,hE,hW⟩
        by_cases h : a=start
        · subst a; exact Or.inl hW
        · exact Or.inr ⟨a,by omega,by omega,hE,hW⟩
    next he =>
      rw [ih]
      constructor
      · rintro ⟨a,ha,hb,hE,hW⟩
        exact ⟨a,by omega,by omega,hE,hW⟩
      · rintro ⟨a,ha,hb,hE,hW⟩
        have h : a≠start := by intro h; subst a; exact he hE
        exact ⟨a,by omega,by omega,hE,hW⟩

theorem cutLoop_counts (D L : Nat) (R : Strip) (start steps : Nat) :
    (cutLoop D L R start steps).queries=(cutLoop D L R start steps).jobs.length ∧
    (cutLoop D L R start steps).queries≤steps ∧
    (cutLoop D L R start steps).probes=steps ∧
    (cutLoop D L R start steps).work≤12*steps+1 := by
  induction steps generalizing start with
  | zero => exact ⟨rfl,Nat.le_refl _,rfl,Nat.le_refl _⟩
  | succ steps ih =>
    have hh:=ih (start+1)
    simp only [cutLoop]
    split <;> simp only [List.length_cons] <;> omega

def gridCount (D : Nat) (R : Strip) : Nat := (R.hi+R.distance)/D-R.lo/D+1

theorem gridCount_bound (D : Nat) (R : Strip) (hD : 0<D) (ho : R.lo≤R.hi) :
    gridCount D R*D≤span R+R.distance+2*D := by
  have hq : R.lo/D≤(R.hi+R.distance)/D :=
    (Nat.le_div_iff_mul_le hD).mpr (Nat.le_trans (Nat.div_mul_le_self R.lo D) (by omega))
  have hm:=Nat.mul_le_mul_right D hq
  have he:=Nat.div_mul_le_self (R.hi+R.distance) D
  have hb:=Nat.mod_add_div R.lo D
  have hr:=Nat.mod_lt R.lo hD
  rw [Nat.mul_comm D (R.lo/D)] at hb
  simp only [gridCount,Nat.add_mul,Nat.one_mul,Nat.sub_mul,span]
  omega

theorem grid_contains (D : Nat) (R : Strip) (a : Nat) (hD : 0<D)
    (ha : R.lo≤a*D) (hb : a*D≤R.hi+R.distance) :
    R.lo/D≤a ∧ a<R.lo/D+gridCount D R := by
  have hl : R.lo/D≤a := by
    exact Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using ha)
  have hr: a≤(R.hi+R.distance)/D := (Nat.le_div_iff_mul_le hD).mpr hb
  simp only [gridCount]
  omega

def one (D L : Nat) (R : Strip) : Jobs :=
  if span R≤R.distance then ⟨[direct R],1,0,8⟩
  else
    let out:=cutLoop D L R (R.lo/D) (gridCount D R)
    {out with work:=out.work+7}

theorem local_direct (D L : Nat) (R : Strip) (hs : span R≤R.distance) :
    (one D L R).jobs=[direct R] := by simp only [one,if_pos hs]

theorem local_cut (D L : Nat) (R : Strip) (hs : R.distance<span R) (W : Job) :
    W∈(one D L R).jobs ↔
      ∃a,R.lo/D≤a ∧ a<R.lo/D+gridCount D R ∧ Eligible L (atCut D R a) ∧ W=atCut D R a := by
  simp only [one,if_neg (by omega : ¬span R≤R.distance),cutLoop_mem]

theorem local_counts (D L : Nat) (R : Strip) :
    (one D L R).queries=(one D L R).jobs.length ∧
    (one D L R).queries≤(one D L R).probes+1 ∧
    (one D L R).work≤12*(one D L R).probes+8 := by
  simp only [one]
  split
  · exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩
  · have hh:=cutLoop_counts D L R (R.lo/D) (gridCount D R)
    dsimp only
    omega

theorem local_probe_mass (D L : Nat) (R : Strip) (hD : 0<D) (ho : R.lo≤R.hi) :
    (one D L R).probes*D≤2*span R+2*D := by
  simp only [one]
  split
  · dsimp only; omega
  · have hh:=gridCount_bound D R hD ho
    have he:=cutLoop_counts D L R (R.lo/D) (gridCount D R) |>.2.2.1
    dsimp only
    rw [he]
    omega

end REWB.ResidualStripSchedule
