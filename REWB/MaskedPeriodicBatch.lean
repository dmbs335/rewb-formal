import REWB.MaskedPeriodicBatchQueryCost
import REWB.MaskedRunEnumerationCost

/-! The actual all-source periodic branch. A shared text cut index and
pattern modulus are prepared once. The complete owner-based enumerator
supplies the cubic runs; each run gets one immutable target-mask prefix
array and one full-input suffix map. Source answers are unioned into a
separate output array. No supplied run list or query-answer oracle occurs
at the public `solve` entry point.
-/
namespace REWB.MaskedPeriodic.Batch
open REWB.Spec REWB.Periodic REWB.RunGeometry
open REWB.MaskedProgression REWB.MaskedCut REWB.MaskedCut.DFAIndex
variable {α : Type} {σ : Nat}

def span (R : Bounds) : Nat := R.hi-R.lo+1

def totalSpan : List Bounds → Nat
  | [] => 0
  | R::Rs => span R+totalSpan Rs

def one (b c e : DFA α) (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (idx : Index.Tree (jointEnum b c e)) (n : Nat) (source target : Array Bool)
    (R : Bounds) (out : State) : State :=
  let counts:=MaskedProgression.build target R.lo (span R) (prepared.K*R.period)
  let tail:=Text.prepareTail b c e idx R.hi n
  scan (fun s=>Text.query b c e prepared idx tail.map s R.hi R.period counts.counts R.lo)
    source (span R) R.lo
    {out with preparationWork:=out.preparationWork+counts.slots+counts.arithmetic+
      tail.products+tail.visits+5}

def runs (b c e : DFA α) (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (idx : Index.Tree (jointEnum b c e)) (n : Nat) (source target : Array Bool) :
    List Bounds → State → State
  | [],out => out
  | R::Rs,out => runs b c e prepared idx n source target Rs
      (one b c e prepared idx n source target R out)

theorem one_size (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (idx : Index.Tree (jointEnum b c e)) (n : Nat) (source target : Array Bool)
    (R : Bounds) (out : State) :
    (one b c e prepared idx n source target R out).hits.size=out.hits.size := by
  unfold one
  rw [scan_size]

theorem runs_size (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (idx : Index.Tree (jointEnum b c e)) (n : Nat) (source target : Array Bool)
    (Rs : List Bounds) (out : State) :
    (runs b c e prepared idx n source target Rs out).hits.size=out.hits.size := by
  induction Rs generalizing out with
  | nil => rfl
  | cons R Rs ih => rw [runs,ih,one_size]

theorem one_read (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w : Word α) (fallback : α) (source target : Array Bool) (R : Bounds)
    (hr : R.Valid (ArrayText.read w.toArray fallback) w.length) (out : State) (i : Nat) :
    readMask (one b c e prepared (DFAIndex.build b c e w).1 w.length source target R out).hits i=true ↔
      readMask out.hits i=true ∨
        (R.lo≤i ∧ i≤R.hi ∧ i<out.hits.size ∧ readMask source i=true ∧
          Text.FullWitness b c e w i R.hi R.period target R.lo (span R)) := by
  unfold one
  rw [scan_read]
  dsimp only
  have hlo:=hr.1
  constructor
  · rintro (hold|⟨hs,hend,hi,hm,ha⟩)
    · exact Or.inl hold
    · have hw:=(Text.query_full_run_correct b c e prepared w fallback R.lo R.hi R.period i
        target R.lo (span R) hr hs).mp ha
      exact Or.inr ⟨hs,by unfold span at hend; omega,hi,hm,hw⟩
  · rintro (hold|⟨hs,hend,hi,hm,hw⟩)
    · exact Or.inl hold
    · exact Or.inr ⟨hs,by unfold span; omega,hi,hm,
        (Text.query_full_run_correct b c e prepared w fallback R.lo R.hi R.period i
          target R.lo (span R) hr hs).mpr hw⟩

theorem runs_read (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w : Word α) (fallback : α) (source target : Array Bool) (Rs : List Bounds)
    (hvalid : ∀ R,R∈Rs → R.Valid (ArrayText.read w.toArray fallback) w.length)
    (out : State) (i : Nat) :
    readMask (runs b c e prepared (DFAIndex.build b c e w).1 w.length source target Rs out).hits i=true ↔
      readMask out.hits i=true ∨
        ∃ R,R∈Rs ∧ R.lo≤i ∧ i≤R.hi ∧ i<out.hits.size ∧ readMask source i=true ∧
          Text.FullWitness b c e w i R.hi R.period target R.lo (span R) := by
  induction Rs generalizing out with
  | nil => simp [runs]
  | cons R Rs ih =>
    rw [runs,ih (fun S hS=>hvalid S (List.mem_cons_of_mem R hS)),
      one_read b c e prepared w fallback source target R (hvalid R List.mem_cons_self),one_size]
    constructor
    · rintro ((hold|hR)|⟨S,hS,hrest⟩)
      · exact Or.inl hold
      · exact Or.inr ⟨R,List.mem_cons_self,hR⟩
      · exact Or.inr ⟨S,List.mem_cons_of_mem R hS,hrest⟩
    · rintro (hold|⟨S,hS,hrest⟩)
      · exact Or.inl (Or.inl hold)
      · rcases List.mem_cons.mp hS with he|hS
        · subst S
          exact Or.inl (Or.inr hrest)
        · exact Or.inr ⟨S,hS,hrest⟩

structure Result where
  output : State
  enumerationWork : Nat
  indexProducts : Nat
  deriving Repr

def solve (b c e : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : Result :=
  let prepared:=preparePattern b.stateCount c.stateCount e.stateCount
  let idx:=DFAIndex.build b c e text.toList
  let found:=MaskedOrdered.Owner.enumerateAuto text fallback
  let out:=runs b c e prepared idx.1 text.size source target found.runs
    {hits:=Array.replicate (text.size+1) false,preparationWork:=text.size+1}
  ⟨out,found.work,idx.2⟩

/-- The within-run witness class: an actual least-period maximal run,
two nonoverlapping equal captures of length at least twice its period,
the three original DFA conditions, and an arbitrary marked target. -/
def Covered (b c e : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (target : Array Bool) (s : Nat) : Prop :=
  ∃ R,R.Valid (ArrayText.read text fallback) text.size ∧ R.lo≤s ∧
    Text.FullWitness b c e text.toList s R.hi R.period target R.lo (span R)

theorem covered_bounds (b c e : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (target : Array Bool) (s : Nat) (R : Bounds)
    (hr : R.Valid (ArrayText.read text fallback) text.size) (hs : R.lo≤s)
    (hw : Text.FullWitness b c e text.toList s R.hi R.period target R.lo (span R)) :
    s≤R.hi ∧ s<text.size+1 ∧ 3*R.period≤R.hi-R.lo := by
  obtain ⟨L,k,hL,hgap,hend,_⟩:=hw
  have hn:=hr.2.1
  omega

theorem solve_size (b c e : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (solve b c e text fallback source target).output.hits.size=text.size+1 := by
  unfold solve
  rw [runs_size,Array.size_replicate]

theorem solve_correct (b c e : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (s : Nat) :
    readMask (solve b c e text fallback source target).output.hits s=true ↔
      readMask source s=true ∧ Covered b c e text fallback target s := by
  have hv : ∀ R,R∈(MaskedOrdered.Owner.enumerateAuto text fallback).runs →
      R.Valid (ArrayText.read text.toList.toArray fallback) text.toList.length := by
    intro R hR
    simpa using ((MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mp hR).1
  have hz : readMask (Array.replicate (text.size+1) false) s=false := by
    simp only [readMask,Array.getElem?_replicate]
    split <;> rfl
  unfold solve
  have he:=runs_read b c e (preparePattern b.stateCount c.stateCount e.stateCount)
    text.toList fallback source target (MaskedOrdered.Owner.enumerateAuto text fallback).runs hv
    {hits:=Array.replicate (text.size+1) false,preparationWork:=text.size+1} s
  simp only [Array.length_toList] at he
  rw [he]
  simp only [hz,Bool.false_eq_true,false_or,Array.size_replicate]
  constructor
  · rintro ⟨R,hR,hs,_,_,hm,hw⟩
    exact ⟨hm,R,((MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mp hR).1,hs,hw⟩
  · rintro ⟨hm,R,hr,hs,hw⟩
    have hb:=covered_bounds b c e text fallback target s R hr hs hw
    exact ⟨R,(MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mpr ⟨hr,hb.2.2⟩,
      hs,hb.1,hb.2.1,hm,hw⟩

theorem covered_sound (b c e : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (target : Array Bool) (s : Nat) (h : Covered b c e text fallback target s) :
    maskedStart b c e text.toList (readMask target) s := by
  obtain ⟨R,hr,_,L,k,_,hgap,hend,he,hB,hC,hE,hm⟩:=h
  have hn:=hr.2.1
  refine ⟨s+L,s+k*R.period,s+k*R.period+L,by omega,hgap,by omega,?_,hm.2.2,he,hB,hC,?_⟩
  · simpa using Nat.le_trans hend hn
  · rwa [Text.suffix_slice]

theorem solve_sound (b c e : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (s : Nat)
    (h : readMask (solve b c e text fallback source target).output.hits s=true) :
    readMask source s=true ∧ maskedStart b c e text.toList (readMask target) s := by
  have hh:=(solve_correct b c e text fallback source target s).mp h
  exact ⟨hh.1,covered_sound b c e text fallback target s hh.2⟩

end REWB.MaskedPeriodic.Batch
