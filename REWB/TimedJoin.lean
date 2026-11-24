import REWB.DFACut

/-! A cross-cut batch join respects the chronological C-gap constraint
    of P1. All source ends are on/before the cut and all target starts
    are on/after it. The original exact word key is refined by a finite
    DFA state at the cut. This avoids carrying a separate C scan for
    every source-target pair. -/
namespace REWB.TimedJoin
open REWB.AffineProjection
open REWB.KeyedJoin (Entry)
open REWB.Spec (slice)
variable {α : Type}

structure TimedEntry where
  pos : Nat
  entry : Entry
  deriving Repr

def color (d : DFA α) (e : Entry) (q : Fin d.stateCount) : Entry :=
  ⟨e.key*d.stateCount+q.val,e.formula⟩

theorem color_key_iff (d : DFA α) (e f : Entry) (q r : Fin d.stateCount) :
    (color d e q).key=(color d f r).key ↔ e.key=f.key ∧ q=r := by
  constructor
  · intro h
    have he := KeyedJoin.pack_inj d.stateCount e.key f.key q.val r.val q.isLt r.isLt h
    exact ⟨he.1,Fin.ext he.2⟩
  · rintro ⟨he,rfl⟩
    unfold color
    rw [he]

def source (d : DFA α) (I : DFACut.Index d) (e : TimedEntry) : Entry :=
  color d e.entry (DFACut.leftAt d I e.pos)

def target (d : DFA α) (I : DFACut.Index d) (e : TimedEntry) : List Entry :=
  ((FiniteRelation.finEnum d.stateCount).elems.filter
    (fun q=>DFACut.rightAt d I e.pos q)).map (color d e.entry)

theorem target_mem (d : DFA α) (I : DFACut.Index d) (e : TimedEntry) (E : Entry) :
    E∈target d I e ↔ ∃ q : Fin d.stateCount,
      DFACut.rightAt d I e.pos q=true ∧ color d e.entry q=E := by
  unfold target
  constructor
  · intro h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact ⟨q,(List.mem_filter.mp hq).2,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    exact List.mem_map.mpr ⟨q,List.mem_filter.mpr
      ⟨(FiniteRelation.finEnum d.stateCount).complete q,hq⟩,rfl⟩

def sources (d : DFA α) (I : DFACut.Index d) (es : List TimedEntry) : List Entry :=
  es.map (source d I)

def targets (d : DFA α) (I : DFACut.Index d) (es : List TimedEntry) : List Entry :=
  es.flatMap (target d I)

def Good (K : Nat) (es : List TimedEntry) : Prop :=
  ∀ e,e∈es→ExponentIntervals.Compatible K e.entry.formula

theorem sources_good (d : DFA α) (I : DFACut.Index d) (K : Nat)
    (es : List TimedEntry) (h : Good K es) :
    KeyedJoin.Good K (sources d I es) := by
  intro E hE
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hE
  exact h e he

theorem targets_good (d : DFA α) (I : DFACut.Index d) (K : Nat)
    (es : List TimedEntry) (h : Good K es) :
    KeyedJoin.Good K (targets d I es) := by
  intro E hE
  obtain ⟨e,he,hE⟩ := List.mem_flatMap.mp hE
  obtain ⟨q,hq,rfl⟩ := (target_mem d I e E).mp hE
  exact h e he

def Match (d : DFA α) (w : Word α) (N : Nat) (es fs : List TimedEntry) : Prop :=
  ∃ e,e∈es ∧ ∃ f,f∈fs ∧ e.pos≤f.pos ∧ f.pos≤w.length ∧
    e.entry.key=f.entry.key ∧ d.accepts (slice w e.pos f.pos) ∧
    ∃ m : Nat,m≤N ∧ Satisfies e.entry.formula [(m:Int)] ∧ Satisfies f.entry.formula [(m:Int)]

theorem color_match (d : DFA α) (left right : Word α) (N : Nat) (es fs : List TimedEntry)
    (he : ∀ e,e∈es→e.pos≤left.length)
    (hf : ∀ f,f∈fs→left.length≤f.pos ∧ f.pos≤left.length+right.length) :
    KeyedJoin.Match N (sources d (DFACut.build d left right) es)
      (targets d (DFACut.build d left right) fs) ↔ Match d (left++right) N es fs := by
  let I := DFACut.build d left right
  constructor
  · rintro ⟨E,hE,F,hF,hkey,m,hm,hS,hT⟩
    obtain ⟨e,he',rfl⟩ := List.mem_map.mp hE
    obtain ⟨f,hf',hF⟩ := List.mem_flatMap.mp hF
    obtain ⟨q,hq,rfl⟩ := (target_mem d I f F).mp hF
    obtain ⟨hk,hq'⟩ := (color_key_iff d e.entry f.entry (DFACut.leftAt d I e.pos) q).mp hkey
    have hacc := (DFACut.crossing_accepts d left right e.pos f.pos
      (he e he') (hf f hf').1 (hf f hf').2).mp (by rw [hq']; exact hq)
    exact ⟨e,he',f,hf',Nat.le_trans (he e he') (hf f hf').1,
      by simpa only [List.length_append] using (hf f hf').2,hk,hacc,m,hm,hS,hT⟩
  · rintro ⟨e,he',f,hf',_,_,hkey,hacc,m,hm,hS,hT⟩
    let q := DFACut.leftAt d I e.pos
    have hq : DFACut.rightAt d I f.pos q=true :=
      (DFACut.crossing_accepts d left right e.pos f.pos
        (he e he') (hf f hf').1 (hf f hf').2).mpr hacc
    refine ⟨source d I e,List.mem_map.mpr ⟨e,he',rfl⟩,color d f.entry q,
      List.mem_flatMap.mpr ⟨f,hf',(target_mem d I f _).mpr ⟨q,hq,rfl⟩⟩,
      (color_key_iff d _ _ _ _).mpr ⟨hkey,rfl⟩,m,hm,hS,hT⟩

def cross (d : DFA α) (left right : Word α) (K N : Nat) (es fs : List TimedEntry) : Bool×Nat :=
  let I := DFACut.build d left right
  KeyedJoin.batch K N (sources d I es) (targets d I fs)

theorem cross_correct (d : DFA α) (left right : Word α) (K N : Nat) (es fs : List TimedEntry)
    (hK : 0<K) (hS : Good K es) (hT : Good K fs)
    (he : ∀ e,e∈es→e.pos≤left.length)
    (hf : ∀ f,f∈fs→left.length≤f.pos ∧ f.pos≤left.length+right.length) :
    (cross d left right K N es fs).1=true ↔ Match d (left++right) N es fs :=
  (KeyedJoin.batch_correct _ _ _ _ hK (sources_good _ _ _ _ hS)
    (targets_good _ _ _ _ hT)).trans (color_match d left right N es fs he hf)

def weight : List TimedEntry→Nat
  | [] => 0
  | e::es => e.entry.formula.length+weight es

theorem sources_weight (d : DFA α) (I : DFACut.Index d) (es : List TimedEntry) :
    KeyedJoin.weight (sources d I es)=weight es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change e.entry.formula.length+KeyedJoin.weight (sources d I es)=e.entry.formula.length+weight es
    rw [ih]

private theorem weight_append (xs ys : List Entry) :
    KeyedJoin.weight (xs++ys)=KeyedJoin.weight xs+KeyedJoin.weight ys := by
  induction xs with
  | nil => simp [KeyedJoin.weight]
  | cons x xs ih =>
    simp only [List.cons_append,KeyedJoin.weight,ih,Nat.add_assoc]

theorem target_weight (d : DFA α) (I : DFACut.Index d) (e : TimedEntry) :
    KeyedJoin.weight (target d I e)≤d.stateCount*e.entry.formula.length := by
  have aux : ∀ qs : List (Fin d.stateCount),
      KeyedJoin.weight (qs.map (color d e.entry))=qs.length*e.entry.formula.length := by
    intro qs
    induction qs with
    | nil => simp [KeyedJoin.weight]
    | cons q qs ih =>
      change e.entry.formula.length+KeyedJoin.weight (qs.map (color d e.entry))=
        (qs.length+1)*e.entry.formula.length
      rw [ih,Nat.add_mul,Nat.one_mul]
      omega
  unfold target
  rw [aux]
  have hh := List.length_filter_le (fun q=>DFACut.rightAt d I e.pos q)
    (FiniteRelation.finEnum d.stateCount).elems
  have he : (FiniteRelation.finEnum d.stateCount).elems.length=d.stateCount := by
    simp [FiniteRelation.finEnum]
  rw [he] at hh
  exact Nat.mul_le_mul_right _ hh

theorem targets_weight (d : DFA α) (I : DFACut.Index d) (es : List TimedEntry) :
    KeyedJoin.weight (targets d I es)≤d.stateCount*weight es := by
  induction es with
  | nil => simp [targets,KeyedJoin.weight,weight]
  | cons e es ih =>
    change KeyedJoin.weight (target d I e++targets d I es)≤
      d.stateCount*(e.entry.formula.length+weight es)
    rw [weight_append,Nat.mul_add]
    exact Nat.add_le_add (target_weight d I e) ih

/-- Count the pairs examined by the cross-cut interval sweep. Sorting
    and construction of the cut vectors are not included in this count. -/
theorem cross_cost (d : DFA α) (left right : Word α) (K N : Nat) (es fs : List TimedEntry) :
    (cross d left right K N es fs).2≤K*(weight es+d.stateCount*weight fs) := by
  let I := DFACut.build d left right
  have h := KeyedJoin.batch_cost K N (sources d I es) (targets d I fs)
  rw [sources_weight] at h
  exact Nat.le_trans h (Nat.mul_le_mul_left K (Nat.add_le_add_left (targets_weight d I fs) _))

/-- Decompose all ordered witnesses into the left, right, and crossing
    sets at a boundary. Equal positions are kept together on the right.
    This is the coverage invariant for an offline divide-and-conquer. -/
def before (c : Nat) (es : List TimedEntry) : List TimedEntry :=
  es.filter (fun e=>decide (e.pos<c))

def after (c : Nat) (es : List TimedEntry) : List TimedEntry :=
  es.filter (fun e=>decide (c≤e.pos))

theorem split_cover (d : DFA α) (w : Word α) (N c : Nat) (es fs : List TimedEntry) :
    Match d w N es fs ↔
      Match d w N (before c es) (before c fs) ∨
      Match d w N (after c es) (after c fs) ∨
      Match d w N (before c es) (after c fs) := by
  constructor
  · rintro ⟨e,he,f,hf,horder,hn,hkey,hc,m,hm,hS,hT⟩
    by_cases h1 : e.pos<c
    · by_cases h2 : f.pos<c
      · exact Or.inl ⟨e,List.mem_filter.mpr ⟨he,by simp [h1]⟩,
          f,List.mem_filter.mpr ⟨hf,by simp [h2]⟩,horder,hn,hkey,hc,m,hm,hS,hT⟩
      · exact Or.inr (Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [h1]⟩,
          f,List.mem_filter.mpr ⟨hf,by have : c≤f.pos := by omega; simp [this]⟩,
          horder,hn,hkey,hc,m,hm,hS,hT⟩)
    · have h2 : c≤f.pos := by omega
      have h3 : c≤e.pos := by omega
      exact Or.inr (Or.inl ⟨e,List.mem_filter.mpr ⟨he,by simp [h3]⟩,
        f,List.mem_filter.mpr ⟨hf,by simp [h2]⟩,horder,hn,hkey,hc,m,hm,hS,hT⟩)
  · rintro (⟨e,he,f,hf,rest⟩|⟨e,he,f,hf,rest⟩|⟨e,he,f,hf,rest⟩)
    all_goals exact ⟨e,(List.mem_filter.mp he).1,f,(List.mem_filter.mp hf).1,rest⟩

end REWB.TimedJoin
