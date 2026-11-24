import REWB.TimedJoin

/-! Complete offline chronological join. A boundary is assigned to the
    right child at equality. Each recursive node works on its own text
    and local event coordinates, so neither child rescans the whole text.

    Counters record actual interval tests, input-event visits, and local
    text lengths. They do not charge sorting, integer bit costs, or all
    allocation overhead. -/
namespace REWB.OfflineJoin
open REWB.TimedJoin (TimedEntry Match Good before after weight cross)
open REWB.Spec (slice)
variable {α : Type}

def shift (c : Nat) (e : TimedEntry) : TimedEntry :=
  ⟨e.pos-c,e.entry⟩

def shiftAll (c : Nat) (es : List TimedEntry) : List TimedEntry :=
  es.map (shift c)

theorem shift_weight (c : Nat) (es : List TimedEntry) :
    weight (shiftAll c es)=weight es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change e.entry.formula.length+weight (shiftAll c es)=e.entry.formula.length+weight es
    rw [ih]

theorem shift_good (K c : Nat) (es : List TimedEntry) (h : Good K es) :
    Good K (shiftAll c es) := by
  intro e he
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
  exact h x hx

theorem before_mem (c : Nat) (es : List TimedEntry) (e : TimedEntry) :
    e∈before c es ↔ e∈es ∧ e.pos<c := by
  simp [before]

theorem after_mem (c : Nat) (es : List TimedEntry) (e : TimedEntry) :
    e∈after c es ↔ e∈es ∧ c≤e.pos := by
  simp [after]

theorem before_good (K c : Nat) (es : List TimedEntry) (h : Good K es) :
    Good K (before c es) :=
  fun e he=>h e ((before_mem c es e).mp he).1

theorem after_good (K c : Nat) (es : List TimedEntry) (h : Good K es) :
    Good K (after c es) :=
  fun e he=>h e ((after_mem c es e).mp he).1

theorem split_weight (c : Nat) (es : List TimedEntry) :
    weight (before c es)+weight (after c es)=weight es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases h : e.pos<c
    · have hn : ¬c≤e.pos := by omega
      simp only [before,after,List.filter_cons,decide_true,decide_false,h,hn,if_true,if_false,
        Bool.false_eq_true,weight]
      change e.entry.formula.length+weight (before c es)+weight (after c es)=_
      rw [Nat.add_assoc,ih]
    · have hn : c≤e.pos := by omega
      simp only [before,after,List.filter_cons,decide_true,decide_false,h,hn,if_true,if_false,
        Bool.false_eq_true,weight]
      change weight (before c es)+(e.entry.formula.length+weight (after c es))=_
      omega

theorem split_length (c : Nat) (es : List TimedEntry) :
    (before c es).length+(after c es).length=es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases h : e.pos<c
    · have hn : ¬c≤e.pos := by omega
      simp only [before,after,List.filter_cons,decide_true,decide_false,h,hn,if_true,if_false,
        Bool.false_eq_true,List.length_cons]
      change (before c es).length+1+(after c es).length=es.length+1
      omega
    · have hn : c≤e.pos := by omega
      simp only [before,after,List.filter_cons,decide_true,decide_false,h,hn,if_true,if_false,
        Bool.false_eq_true,List.length_cons]
      change (before c es).length+((after c es).length+1)=es.length+1
      omega

/-- Localize left witnesses to the left text. -/
theorem left_match (d : DFA α) (l r : Word α) (N : Nat)
    (es fs : List TimedEntry)
    (hs : ∀ e,e∈es→e.pos≤l.length) (ht : ∀ f,f∈fs→f.pos≤l.length) :
    Match d (l++r) N es fs ↔ Match d l N es fs := by
  constructor
  · rintro ⟨e,he,f,hf,ho,_,hk,hc,m,hm,hS,hT⟩
    rw [DyadicIndex.slice_left l r e.pos f.pos ho (ht f hf)] at hc
    exact ⟨e,he,f,hf,ho,ht f hf,hk,hc,m,hm,hS,hT⟩
  · rintro ⟨e,he,f,hf,ho,hn,hk,hc,m,hm,hS,hT⟩
    refine ⟨e,he,f,hf,ho,by rw [List.length_append]; omega,hk,?_,m,hm,hS,hT⟩
    rwa [DyadicIndex.slice_left l r e.pos f.pos ho hn]

/-- Localize right witnesses and translate their coordinates. -/
theorem right_match (d : DFA α) (l r : Word α) (N : Nat)
    (es fs : List TimedEntry)
    (hs : ∀ e,e∈es→l.length≤e.pos)
    (ht : ∀ f,f∈fs→l.length≤f.pos) :
    Match d (l++r) N es fs ↔
      Match d r N (shiftAll l.length es) (shiftAll l.length fs) := by
  constructor
  · rintro ⟨e,he,f,hf,ho,hn,hk,hc,m,hm,hS,hT⟩
    rw [List.length_append] at hn
    refine ⟨shift l.length e,List.mem_map.mpr ⟨e,he,rfl⟩,
      shift l.length f,List.mem_map.mpr ⟨f,hf,rfl⟩,?_,?_,hk,?_,m,hm,hS,hT⟩
    · change e.pos-l.length≤f.pos-l.length
      omega
    · change f.pos-l.length≤r.length
      omega
    · exact (by simpa only [shift,DyadicIndex.slice_right l r e.pos f.pos (hs e he) ho] using hc)
  · rintro ⟨E,hE,F,hF,ho,hn,hk,hc,m,hm,hS,hT⟩
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hE
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hF
    have hse := hs e he
    have htf := ht f hf
    change e.pos-l.length≤f.pos-l.length at ho
    change f.pos-l.length≤r.length at hn
    have horder : e.pos≤f.pos := by omega
    refine ⟨e,he,f,hf,horder,by rw [List.length_append]; omega,hk,?_,m,hm,hS,hT⟩
    rw [DyadicIndex.slice_right l r e.pos f.pos hse horder]
    exact hc

structure Result where
  answer : Bool
  tests : Nat
  eventVisits : Nat
  textVisits : Nat
  nodes : Nat
  deriving Repr

def solve (d : DFA α) (K N : Nat) : Nat→Word α→List TimedEntry→List TimedEntry→Result
  | 0,w,es,fs =>
    let z := cross d [] w K N es fs
    ⟨z.1,z.2,es.length+fs.length,w.length,1⟩
  | h+1,w,es,fs =>
    let l := w.take (2^h)
    let r := w.drop (2^h)
    let c := l.length
    let esL := before c es
    let esR := after c es
    let fsL := before c fs
    let fsR := after c fs
    let a := solve d K N h l esL fsL
    let b := solve d K N h r (shiftAll c esR) (shiftAll c fsR)
    let z := cross d l r K N esL fsR
    ⟨a.answer || b.answer || z.1,a.tests+b.tests+z.2,
      es.length+fs.length+a.eventVisits+b.eventVisits,
      w.length+a.textVisits+b.textVisits,
      1+a.nodes+b.nodes⟩

def InRange (h : Nat) (w : Word α) (es : List TimedEntry) : Prop :=
  ∀ e,e∈es→e.pos≤w.length ∧ e.pos<2^h

theorem left_range (h : Nat) (w : Word α) (es : List TimedEntry) :
    InRange h (w.take (2^h)) (before (w.take (2^h)).length es) := by
  intro e he
  have hh := (before_mem _ _ _).mp he
  have hl : (w.take (2^h)).length≤2^h := by rw [List.length_take]; omega
  exact ⟨by omega,by omega⟩

theorem right_range (h : Nat) (w : Word α) (es : List TimedEntry)
    (hs : InRange (h+1) w es) :
    InRange h (w.drop (2^h)) (shiftAll (w.take (2^h)).length
      (after (w.take (2^h)).length es)) := by
  intro e he
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
  obtain ⟨hx,hc⟩ := (after_mem _ _ _).mp hx
  obtain ⟨hn,hpow⟩ := hs x hx
  have hl : (w.take (2^h)).length=min (2^h) w.length := List.length_take
  have hr : (w.drop (2^h)).length=w.length-2^h := List.length_drop
  have hp : 0<2^h := Nat.two_pow_pos h
  rw [Nat.pow_succ] at hpow
  change x.pos-(w.take (2^h)).length≤(w.drop (2^h)).length ∧
    x.pos-(w.take (2^h)).length<2^h
  rw [hl,hr]
  omega

theorem solve_correct (d : DFA α) (K N h : Nat) (w : Word α) (es fs : List TimedEntry)
    (hK : 0<K) (hs : Good K es) (ht : Good K fs)
    (he : InRange h w es) (hf : InRange h w fs) :
    (solve d K N h w es fs).answer=true ↔ Match d w N es fs := by
  induction h generalizing w es fs with
  | zero =>
    change (cross d [] w K N es fs).1=true ↔ _
    have hh := TimedJoin.cross_correct d [] w K N es fs hK hs ht
      (fun e hx=>by have h := (he e hx).2; simp only [Nat.pow_zero] at h; simp; omega)
      (fun f hx=>by have h := (hf f hx).1; simp; exact h)
    simpa only [List.nil_append] using hh
  | succ h ih =>
    let l := w.take (2^h)
    let r := w.drop (2^h)
    let c := l.length
    let esL := before c es
    let esR := after c es
    let fsL := before c fs
    let fsR := after c fs
    have hj : l++r=w := List.take_append_drop _ _
    have hsL : ∀ e,e∈esL→e.pos≤l.length := by
      intro e hx
      have hh := (before_mem c es e).mp hx
      have ht : e.pos<l.length := hh.2
      omega
    have htL : ∀ f,f∈fsL→f.pos≤l.length := by
      intro f hx
      have hh := (before_mem c fs f).mp hx
      have ht : f.pos<l.length := hh.2
      omega
    have hsR : ∀ e,e∈esR→l.length≤e.pos := fun e hx=>((after_mem _ _ _).mp hx).2
    have htR : ∀ f,f∈fsR→l.length≤f.pos := fun f hx=>((after_mem _ _ _).mp hx).2
    have hfr : ∀ f,f∈fsR→l.length≤f.pos ∧ f.pos≤l.length+r.length := by
      intro f hx
      have hh := (hf f ((after_mem _ _ _).mp hx).1).1
      have hlen := congrArg List.length hj
      rw [List.length_append] at hlen
      exact ⟨htR f hx,by omega⟩
    have ha := ih l esL fsL (before_good K c es hs) (before_good K c fs ht)
      (left_range h w es) (left_range h w fs)
    have hb := ih r (shiftAll c esR) (shiftAll c fsR)
      (shift_good K c _ (after_good K c es hs))
      (shift_good K c _ (after_good K c fs ht))
      (right_range h w es he) (right_range h w fs hf)
    have hz := TimedJoin.cross_correct d l r K N esL fsR hK
      (before_good K c es hs) (after_good K c fs ht) hsL hfr
    change ((solve d K N h l esL fsL).answer ||
      (solve d K N h r (shiftAll c esR) (shiftAll c fsR)).answer ||
      (cross d l r K N esL fsR).1)=true ↔ _
    rw [Bool.or_eq_true,Bool.or_eq_true,ha,hb,hz,
      ← left_match d l r N esL fsL hsL htL,
      ← right_match d l r N esR fsR hsR htR,hj,
      TimedJoin.split_cover d w N c es fs]
    constructor
    · rintro ((ha|hb)|hz)
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hz)
    · rintro (ha|hb|hz)
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr hb)
      · exact Or.inr hz

/-- Linear per level in the number of input events, and in the number
    of text characters. The sweep count has the additional fixed
    congruence modulus and DFA-state factors. -/
theorem solve_cost (d : DFA α) (K N h : Nat) (w : Word α) (es fs : List TimedEntry) :
    (solve d K N h w es fs).tests≤(h+1)*(K*(weight es+d.stateCount*weight fs)) ∧
    (solve d K N h w es fs).eventVisits≤(h+1)*(es.length+fs.length) ∧
    (solve d K N h w es fs).textVisits≤(h+1)*w.length ∧
    (solve d K N h w es fs).nodes+1=2^(h+1) := by
  induction h generalizing w es fs with
  | zero =>
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [solve,Nat.zero_add,Nat.one_mul] using TimedJoin.cross_cost d [] w K N es fs
    · simp [solve]
    · simp [solve]
    · rfl
  | succ h ih =>
    let l := w.take (2^h)
    let r := w.drop (2^h)
    let c := l.length
    let el := before c es
    let er := after c es
    let fl := before c fs
    let fr := after c fs
    let a := solve d K N h l el fl
    let b := solve d K N h r (shiftAll c er) (shiftAll c fr)
    let z := cross d l r K N el fr
    have ha := ih l el fl
    have hb := ih r (shiftAll c er) (shiftAll c fr)
    have hwE : weight el+weight er=weight es := split_weight c es
    have hwF : weight fl+weight fr=weight fs := split_weight c fs
    have hlE : el.length+er.length=es.length := split_length c es
    have hlF : fl.length+fr.length=fs.length := split_length c fs
    have hlw : l.length+r.length=w.length := by
      have hh := congrArg List.length (List.take_append_drop (2^h) w)
      simpa only [List.length_append] using hh
    rw [shift_weight,shift_weight] at hb
    simp only [shiftAll,List.length_map] at hb
    have hz := TimedJoin.cross_cost d l r K N el fr
    change a.tests+b.tests+z.2≤(h+1+1)*(K*(weight es+d.stateCount*weight fs)) ∧
      es.length+fs.length+a.eventVisits+b.eventVisits≤(h+1+1)*(es.length+fs.length) ∧
      w.length+a.textVisits+b.textVisits≤(h+1+1)*w.length ∧
      1+a.nodes+b.nodes+1=2^(h+1+1)
    change a.tests≤_ ∧ a.eventVisits≤_ ∧ a.textVisits≤_ ∧ a.nodes+1=_ at ha
    change b.tests≤_ ∧ b.eventVisits≤_ ∧ b.textVisits≤_ ∧ b.nodes+1=_ at hb
    change z.2≤_ at hz
    have hz' : z.2≤K*(weight es+d.stateCount*weight fs) :=
      Nat.le_trans hz (Nat.mul_le_mul_left K (Nat.add_le_add (by omega)
        (Nat.mul_le_mul_left d.stateCount (by omega))))
    have hsums : (h+1)*(K*(weight el+d.stateCount*weight fl))+
      (h+1)*(K*(weight er+d.stateCount*weight fr))=
      (h+1)*(K*(weight es+d.stateCount*weight fs)) := by
      rw [← Nat.mul_add,← Nat.mul_add]
      congr 2
      rw [← hwE,← hwF,Nat.mul_add]
      omega
    have hevents : (h+1)*(el.length+fl.length)+(h+1)*(er.length+fr.length)=
        (h+1)*(es.length+fs.length) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have htext : (h+1)*l.length+(h+1)*r.length=(h+1)*w.length := by
      rw [← Nat.mul_add,hlw]
    refine ⟨?_,?_,?_,?_⟩
    · have hh := Nat.add_le_add ha.1 hb.1
      rw [hsums] at hh
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · have hh := Nat.add_le_add ha.2.1 hb.2.1
      rw [hevents] at hh
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · have hh := Nat.add_le_add ha.2.2.1 hb.2.2.1
      rw [htext] at hh
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · rw [Nat.pow_succ]
      omega

def run (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry) : Result :=
  solve d K N (DyadicIndex.heightFor w.length) w es fs

theorem run_correct (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry)
    (hK : 0<K) (hs : Good K es) (ht : Good K fs)
    (he : ∀ e,e∈es→e.pos≤w.length) (hf : ∀ f,f∈fs→f.pos≤w.length) :
    (run d K N w es fs).answer=true ↔ Match d w N es fs := by
  have hp : w.length<2^(DyadicIndex.heightFor w.length) := by
    unfold DyadicIndex.heightFor
    exact Nat.lt_log2_self (n := w.length)
  exact solve_correct d K N _ w es fs hK hs ht
    (fun e hx=>⟨he e hx,by have hh := he e hx; omega⟩)
    (fun f hx=>⟨hf f hx,by have hh := hf f hx; omega⟩)

end REWB.OfflineJoin
