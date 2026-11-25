import REWB.MaskedMutableProgressionBatchBuild

/-! Direct run-ID updates. The executable loop traverses only the cached
affected-ID list and performs one array lookup/update per ID. Previous
row snapshots and all untouched trees are shared. -/
namespace REWB.MaskedMutableProgression.Batch

def RowsValid (rows : Array Index) : Prop :=
  ∀(id : Nat) (idx : Index),rows[id]?=some idx→idx.Valid

def RowsHeight (rows : Array Index) (H : Nat) : Prop :=
  ∀(id : Nat) (idx : Index),rows[id]?=some idx→idx.levels≤H

def Same (old next : Index) : Prop :=
  next.base=old.base ∧ next.len=old.len ∧ next.step=old.step ∧ next.levels=old.levels

theorem Same.refl (idx : Index) : Same idx idx := ⟨rfl,rfl,rfl,rfl⟩
theorem Same.trans {a b c : Index} (hab : Same a b) (hbc : Same b c) : Same a c :=
  ⟨hbc.1.trans hab.1,hbc.2.1.trans hab.2.1,hbc.2.2.1.trans hab.2.2.1,hbc.2.2.2.trans hab.2.2.2⟩
theorem Same.erase (idx : Index) (p : Nat) : Same idx (erase idx p).index :=
  ⟨erase_base idx p,erase_len idx p,erase_step idx p,erase_levels idx p⟩
theorem Same.sized {old next : Index} (hh : Same old next) (hs : old.LogSized) : next.LogSized := by
  unfold Index.LogSized
  rw [hh.2.2.2,hh.2.1]
  exact hs

structure RowsErased where
  rows : Array Index
  work : Nat := 0
  visits : Nat := 0
  deriving Repr

def eraseOne (p id : Nat) (out : RowsErased) : RowsErased :=
  match out.rows[id]? with
  | none => {out with work:=out.work+3,visits:=out.visits+1}
  | some idx =>
    let r:=erase idx p
    ⟨out.rows.setIfInBounds id r.index,out.work+r.work+6,out.visits+1⟩

def updateRows (p : Nat) (ids : List Nat) (rows : Array Index) : RowsErased :=
  ids.foldl (fun out id=>eraseOne p id out) ⟨rows,1,0⟩

theorem eraseOne_size (p id : Nat) (out : RowsErased) :
    (eraseOne p id out).rows.size=out.rows.size := by
  unfold eraseOne
  split <;> simp [Array.size_setIfInBounds]

theorem eraseOne_visits (p id : Nat) (out : RowsErased) :
    (eraseOne p id out).visits=out.visits+1 := by
  unfold eraseOne; split <;> rfl

theorem eraseOne_all (p id : Nat) (out : RowsErased) (P : Index→Prop)
    (hold : ∀(j : Nat) (idx : Index),out.rows[j]?=some idx→P idx)
    (herase : ∀idx,P idx→P (erase idx p).index) :
    ∀(j : Nat) (idx : Index),(eraseOne p id out).rows[j]?=some idx→P idx := by
  intro j idx hj
  unfold eraseOne at hj
  cases he : out.rows[id]? with
  | none => simp only [he] at hj; exact hold j idx hj
  | some old =>
    simp only [he] at hj
    have hid:=(Array.getElem?_eq_some_iff.mp he).1
    by_cases hji : id=j
    · subst j
      rw [Array.getElem?_setIfInBounds_self_of_lt hid] at hj
      have hh:=Option.some.inj hj
      rw [←hh]
      exact herase old (hold id old he)
    · rw [Array.getElem?_setIfInBounds_ne hji] at hj
      exact hold j idx hj

theorem eraseOne_valid (p id : Nat) (out : RowsErased) (hv : RowsValid out.rows) :
    RowsValid (eraseOne p id out).rows :=
  eraseOne_all p id out Index.Valid hv (fun idx hi=>erase_valid idx hi p)

theorem eraseOne_height (p id : Nat) (out : RowsErased) (H : Nat) (hh : RowsHeight out.rows H) :
    RowsHeight (eraseOne p id out).rows H :=
  eraseOne_all p id out (fun idx=>idx.levels≤H) hh (fun idx hi=>by dsimp only; rw [erase_levels]; exact hi)

theorem eraseOne_work (p id : Nat) (out : RowsErased) (H : Nat) (hh : RowsHeight out.rows H) :
    (eraseOne p id out).work≤out.work+(12*H+19) := by
  unfold eraseOne
  cases he : out.rows[id]? with
  | none => simp only [he]; omega
  | some idx =>
    have hi:=hh id idx he
    have hw:=erase_work idx p
    simp only [he]
    omega

theorem eraseOne_lookup (p id j : Nat) (out : RowsErased) (old : Index)
    (hj : out.rows[j]?=some old) (hv : old.Valid) :
    ∃next,(eraseOne p id out).rows[j]?=some next ∧ Same old next ∧ next.Valid ∧
      ∀x,next.Live x ↔ old.Live x ∧ (j=id→x≠p) := by
  unfold eraseOne
  cases he : out.rows[id]? with
  | none =>
    have hne : j≠id := by intro h; subst j; rw [he] at hj; contradiction
    simp only [he]
    refine ⟨old,hj,Same.refl old,hv,?_⟩
    intro x; simp only [hne,false_implies,and_true]
  | some idx =>
    simp only [he]
    by_cases hji : j=id
    · subst j
      have ho : idx=old := Option.some.inj (he.symm.trans hj)
      subst idx
      have hid:=(Array.getElem?_eq_some_iff.mp hj).1
      refine ⟨(erase old p).index,Array.getElem?_setIfInBounds_self_of_lt hid,
        Same.erase old p,erase_valid old hv p,?_⟩
      intro x
      rw [erase_live old hv p x]
      simp only [true_implies]
      exact and_comm
    · refine ⟨old,?_,Same.refl old,hv,?_⟩
      · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hji)]
        exact hj
      · intro x; simp only [hji,false_implies,and_true]

theorem fold_update_size (p : Nat) (ids : List Nat) (out : RowsErased) :
    (ids.foldl (fun out id=>eraseOne p id out) out).rows.size=out.rows.size := by
  induction ids generalizing out with
  | nil => rfl
  | cons id ids ih => rw [List.foldl_cons,ih,eraseOne_size]

theorem fold_update_valid (p : Nat) (ids : List Nat) (out : RowsErased) (hv : RowsValid out.rows) :
    RowsValid (ids.foldl (fun out id=>eraseOne p id out) out).rows := by
  induction ids generalizing out with
  | nil => exact hv
  | cons id ids ih => rw [List.foldl_cons]; exact ih _ (eraseOne_valid p id out hv)

theorem fold_update_height (p : Nat) (ids : List Nat) (out : RowsErased)
    (H : Nat) (hh : RowsHeight out.rows H) :
    RowsHeight (ids.foldl (fun out id=>eraseOne p id out) out).rows H := by
  induction ids generalizing out with
  | nil => exact hh
  | cons id ids ih => rw [List.foldl_cons]; exact ih _ (eraseOne_height p id out H hh)

theorem fold_update_counters (p : Nat) (ids : List Nat) (out : RowsErased)
    (H : Nat) (hh : RowsHeight out.rows H) :
    (ids.foldl (fun out id=>eraseOne p id out) out).visits=out.visits+ids.length ∧
    (ids.foldl (fun out id=>eraseOne p id out) out).work≤out.work+ids.length*(12*H+19) := by
  induction ids generalizing out with
  | nil => simp
  | cons id ids ih =>
    have hi:=ih (eraseOne p id out) (eraseOne_height p id out H hh)
    have hw:=eraseOne_work p id out H hh
    rw [List.foldl_cons]
    rw [eraseOne_visits] at hi
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    exact ⟨by omega,by omega⟩

theorem fold_update_lookup (p : Nat) (ids : List Nat) (out : RowsErased)
    (hv : RowsValid out.rows) (j : Nat) (old : Index) (hj : out.rows[j]?=some old) :
    ∃next,(ids.foldl (fun out id=>eraseOne p id out) out).rows[j]?=some next ∧
      Same old next ∧ next.Valid ∧ ∀x,next.Live x ↔ old.Live x ∧ (j∈ids→x≠p) := by
  induction ids generalizing out old with
  | nil =>
    refine ⟨old,hj,Same.refl old,hv j old hj,?_⟩
    intro x; simp
  | cons id ids ih =>
    obtain ⟨mid,hm,hs,hv',hl⟩:=eraseOne_lookup p id j out old hj (hv j old hj)
    obtain ⟨next,hn,hshape,hgood,hlive⟩:=ih (eraseOne p id out) (eraseOne_valid p id out hv) mid hm
    refine ⟨next,hn,hs.trans hshape,hgood,?_⟩
    intro x
    rw [hlive x,hl x]
    constructor
    · rintro ⟨⟨hx,hfirst⟩,htail⟩
      refine ⟨hx,?_⟩
      intro hmem
      rcases List.mem_cons.mp hmem with he|hm
      · exact hfirst he
      · exact htail hm
    · rintro ⟨hx,hall⟩
      exact ⟨⟨hx,fun he=>hall (List.mem_cons.mpr (Or.inl he))⟩,
        fun hm=>hall (List.mem_cons.mpr (Or.inr hm))⟩

theorem updateRows_size (p : Nat) (ids : List Nat) (rows : Array Index) :
    (updateRows p ids rows).rows.size=rows.size := fold_update_size p ids _

theorem updateRows_lookup (p : Nat) (ids : List Nat) (rows : Array Index)
    (hv : RowsValid rows) (j : Nat) (old : Index) (hj : rows[j]?=some old) :
    ∃next,(updateRows p ids rows).rows[j]?=some next ∧ Same old next ∧ next.Valid ∧
      ∀x,next.Live x ↔ old.Live x ∧ (j∈ids→x≠p) :=
  fold_update_lookup p ids _ hv j old hj

theorem updateRows_counters (p : Nat) (ids : List Nat) (rows : Array Index)
    (H : Nat) (hh : RowsHeight rows H) :
    (updateRows p ids rows).visits=ids.length ∧
    (updateRows p ids rows).work≤1+ids.length*(12*H+19) := by
  simpa only [Nat.zero_add] using fold_update_counters p ids ⟨rows,1,0⟩ H hh

end REWB.MaskedMutableProgression.Batch
