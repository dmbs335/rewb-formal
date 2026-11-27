import REWB.ShortOuterBand

/-! Insertion provenance and its measured cost for the actual backwards
short-factor schedule.  Key bounds are proved for the constructed key
array; they are not a supplied occurrence or equality oracle. -/
namespace REWB.ShortOuter.Band
open REWB.BoundaryApplication
variable {σ : Nat}

def KeyBound (keys : Keys.Index σ) : Prop :=
  ∀p len,p≤keys.length → len<keys.width → Keys.get keys p len<keys.registry.next

theorem build_keyBound (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) :
    KeyBound (Keys.build text fallback limit) := fun p len hp hl=>
  Keys.get_bound text fallback limit p len hp hl

def TargetAt (keys : Keys.Index σ) (suffix : OneUseRange.FarAggregate.Index)
    (p len rank : Nat) : Prop :=
  (p+len≤keys.length ∧ Suffix.get suffix (p+len)=true) ∧ Keys.get keys p len=rank

def insertMark (marked : Nat→Nat→Prop) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x count : Nat) : Nat→Nat→Prop :=
  fun r p=>marked r p ∨ (p=x ∧ ∃len,len<count ∧ TargetAt keys suffix x len r)

def marks (keys : Keys.Index σ) (suffix : OneUseRange.FarAggregate.Index)
    (floor : Nat) : Nat→Nat→Prop :=
  fun r p=>floor≤p ∧ ∃len,len<keys.width ∧ TargetAt keys suffix p len r

theorem insertOne_good (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (marked : Nat→Nat→Prop) (x len : Nat)
    (st : State G.stateCount) (hk : KeyBound keys) (hx : x≤keys.length) (hl : len<keys.width)
    (hsize : st.cells.size=keys.registry.next) (hgood : Sweep.Good G w marked x st.cells) :
    Sweep.Good G w (fun r p=>marked r p ∨ (p=x ∧ TargetAt keys suffix x len r)) x
      (insertOne G (Range.build G w) keys suffix x len st).cells := by
  cases st with
  | mk cells bits touches work =>
    simp only [insertOne]
    split
    · rename_i hc
      apply (Sweep.update_good G w marked x (Keys.get keys x len) true cells
        (by rw [hsize]; exact hk x len hx hl) hgood).congr
      intro r p
      simp only [Sweep.added,TargetAt,hc,true_and]
      constructor
      · rintro (hp|⟨hr,hp⟩)
        · exact Or.inl hp
        · exact Or.inr ⟨hp,hr.symm⟩
      · rintro (hp|⟨hp,hr⟩)
        · exact Or.inl hp
        · exact Or.inr ⟨hr.symm,hp⟩
    · rename_i hc
      apply hgood.congr
      intro r p
      simp only [TargetAt,hc,false_and,and_false,or_false]

theorem inserts_good (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (marked : Nat→Nat→Prop) (x count : Nat)
    (st : State G.stateCount) (hk : KeyBound keys) (hx : x≤keys.length) (hc : count≤keys.width)
    (hsize : st.cells.size=keys.registry.next) (hgood : Sweep.Good G w marked x st.cells) :
    Sweep.Good G w (insertMark marked keys suffix x count) x
      (inserts G (Range.build G w) keys suffix x count st).cells := by
  induction count generalizing st marked with
  | zero =>
    apply hgood.congr
    intro r p
    simp [insertMark]
  | succ count ih =>
    rw [inserts]
    have hone:=insertOne_good G w keys suffix marked x count st hk hx (by omega) hsize hgood
    have hh:=ih (fun r p=>marked r p ∨ (p=x ∧ TargetAt keys suffix x count r))
      (insertOne G (Range.build G w) keys suffix x count st) (by omega)
      (by simpa using hsize) hone
    apply hh.congr
    intro r p
    simp only [insertMark]
    constructor
    · rintro ((hp|⟨hpx,ht⟩)|⟨hpx,len,hl,ht⟩)
      · exact Or.inl hp
      · exact Or.inr ⟨hpx,count,by omega,ht⟩
      · exact Or.inr ⟨hpx,len,by omega,ht⟩
    · rintro (hp|⟨hpx,len,hl,ht⟩)
      · exact Or.inl (Or.inl hp)
      · by_cases he : len=count
        · subst len
          exact Or.inl (Or.inr ⟨hpx,ht⟩)
        · exact Or.inr ⟨hpx,len,by omega,ht⟩

theorem inserts_stage (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x : Nat) (st : State G.stateCount)
    (hk : KeyBound keys) (hx : x≤keys.length) (hsize : st.cells.size=keys.registry.next)
    (hgood : Sweep.Good G w (marks keys suffix (x+1)) x st.cells) :
    Sweep.Good G w (marks keys suffix x) x
      (inserts G (Range.build G w) keys suffix x keys.width st).cells := by
  apply (inserts_good G w keys suffix _ x keys.width st hk hx (Nat.le_refl _) hsize hgood).congr
  intro r p
  simp only [insertMark,marks]
  constructor
  · rintro (⟨hp,hm⟩|⟨rfl,hm⟩)
    · exact ⟨by omega,hm⟩
    · exact ⟨Nat.le_refl _,hm⟩
  · rintro ⟨hp,hm⟩
    by_cases he : p=x
    · subst p
      exact Or.inr ⟨rfl,hm⟩
    · exact Or.inl ⟨by omega,hm⟩

theorem insertOne_bounds (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (marked : Nat→Nat→Prop) (x len : Nat)
    (st : State G.stateCount) (hk : KeyBound keys) (hx : x≤keys.length) (hl : len<keys.width)
    (hsize : st.cells.size=keys.registry.next) (hgood : Sweep.Good G w marked x st.cells) :
    (insertOne G (Range.build G w) keys suffix x len st).touches≤st.touches+1 ∧
    (insertOne G (Range.build G w) keys suffix x len st).work≤
      st.work+Sweep.stepBudget G.stateCount w.length+8 := by
  cases st with
  | mk cells bits touches work =>
    simp only [insertOne]
    split
    · have hh:=Sweep.update_work G w marked x (Keys.get keys x len) true cells
        (by rw [hsize]; exact hk x len hx hl) hgood
      exact ⟨Nat.le_refl _,by dsimp only; omega⟩
    · exact ⟨by dsimp only; omega,by dsimp only; omega⟩

theorem inserts_bounds (G : DFA (Fin σ)) (w : Word (Fin σ)) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (marked : Nat→Nat→Prop) (x count : Nat)
    (st : State G.stateCount) (hk : KeyBound keys) (hx : x≤keys.length) (hc : count≤keys.width)
    (hsize : st.cells.size=keys.registry.next) (hgood : Sweep.Good G w marked x st.cells) :
    (inserts G (Range.build G w) keys suffix x count st).touches≤st.touches+count ∧
    (inserts G (Range.build G w) keys suffix x count st).work≤
      st.work+count*(Sweep.stepBudget G.stateCount w.length+8) := by
  induction count generalizing st marked with
  | zero => simp [inserts]
  | succ count ih =>
    rw [inserts]
    have hone:=insertOne_good G w keys suffix marked x count st hk hx (by omega) hsize hgood
    have hb:=insertOne_bounds G w keys suffix marked x count st hk hx (by omega) hsize hgood
    have hh:=ih (fun r p=>marked r p ∨ (p=x ∧ TargetAt keys suffix x count r))
      (insertOne G (Range.build G w) keys suffix x count st) (by omega)
      (by simpa using hsize) hone
    rw [Nat.add_mul,Nat.one_mul]
    exact ⟨by omega,by omega⟩

end REWB.ShortOuter.Band
