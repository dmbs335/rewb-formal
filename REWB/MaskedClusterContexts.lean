import REWB.MaskedClusterAP
import REWB.BoundaryApplicationRange

/-! Six actual range-map queries prepare a one-jump cluster cell family.
    The C/E range indices are shared across the whole text. They contain
    materialized maps, not all-map cut relations. A replay tail can be
    queried once at a local reset and then represented by finite actions.
-/
namespace REWB.MaskedCluster
open REWB.MaskedFiniteAction.Maps REWB.Spec
variable {α : Type}

theorem range_map (d : DFA α) (w : Word α) (l r : Nat) (hl : l≤r) (hr : r≤w.length) :
    (BoundaryApplication.Range.query d (BoundaryApplication.Range.build d w) l r).map=
      wordMap d (slice w l r) := by
  apply Vector.ext
  intro i hi
  change (BoundaryApplication.Range.query d (BoundaryApplication.Range.build d w) l r).map.get ⟨i,hi⟩=
    (wordMap d (slice w l r)).get ⟨i,hi⟩
  rw [BoundaryApplication.Range.query_correct d w l r hl hr,wordMap_get]

structure Context (C E : DFA α) where
  before : Map C.stateCount
  leftStep : Map C.stateCount
  rightC : Map C.stateCount
  rightE : Map E.stateCount
  afterC : Map C.stateCount
  afterE : Map E.stateCount

def wordContext (C E : DFA α) (pref V U after : Word α) : Context C E :=
  ⟨wordMap C pref,wordMap C V,wordMap C U,wordMap E U,wordMap C after,wordMap E after⟩

structure ContextResult (C E : DFA α) where
  maps : Context C E
  products : Nat
  visits : Nat
  work : Nat

def contexts (C E : DFA α) (ci : BoundaryApplication.Range.Index C)
    (ei : BoundaryApplication.Range.Index E) (I s H q lo hi O : Nat) : ContextResult C E :=
  let first := s+lo*q
  let last := s+hi*q+H
  let blockStart := s+(H-q)
  let blockEnd := s+H
  let a := BoundaryApplication.Range.query C ci I first
  let b := BoundaryApplication.Range.query C ci s (s+q)
  let c := BoundaryApplication.Range.query C ci blockStart blockEnd
  let d := BoundaryApplication.Range.query E ei blockStart blockEnd
  let e := BoundaryApplication.Range.query C ci last O
  let f := BoundaryApplication.Range.query E ei last O
  ⟨⟨a.map,b.map,c.map,d.map,e.map,f.map⟩,
    a.products+b.products+c.products+d.products+e.products+f.products,
    a.visits+b.visits+c.visits+d.visits+e.visits+f.visits,
    a.work+b.work+c.work+d.work+e.work+f.work+12⟩

theorem contexts_value (C E : DFA α) (w : Word α) (I s H q lo hi O : Nat)
    (hq : q≤H) (hlo : lo≤hi) (hI : I≤s+lo*q) (hO : s+hi*q+H≤O) (hn : O≤w.length) :
    (contexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      I s H q lo hi O).maps=
      wordContext C E (slice w I (s+lo*q)) (slice w s (s+q))
        (slice w (s+(H-q)) (s+H)) (slice w (s+hi*q+H) O) := by
  have hm:=Nat.mul_le_mul_right q hlo
  simp only [contexts,wordContext]
  rw [range_map C w I (s+lo*q) hI (by omega),
    range_map C w s (s+q) (by omega) (by omega),
    range_map C w (s+(H-q)) (s+H) (by omega) (by omega),
    range_map E w (s+(H-q)) (s+H) (by omega) (by omega),
    range_map C w (s+hi*q+H) O hO hn,range_map E w (s+hi*q+H) O hO hn]

theorem contexts_bounds (C E : DFA α) (w : Word α) (I s H q lo hi O : Nat)
    (hq : q≤H) (hlo : lo≤hi) (hI : I≤s+lo*q) (hO : s+hi*q+H≤O) (hn : O≤w.length) :
    (contexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      I s H q lo hi O).products≤6 ∧
    (contexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      I s H q lo hi O).visits≤6*(Nat.log2 w.length+2) := by
  have hm:=Nat.mul_le_mul_right q hlo
  have ha:=BoundaryApplication.Range.query_bounds C w I (s+lo*q) hI (by omega)
  have hb:=BoundaryApplication.Range.query_bounds C w s (s+q) (by omega) (by omega)
  have hc:=BoundaryApplication.Range.query_bounds C w (s+(H-q)) (s+H) (by omega) (by omega)
  have hd:=BoundaryApplication.Range.query_bounds E w (s+(H-q)) (s+H) (by omega) (by omega)
  have he:=BoundaryApplication.Range.query_bounds C w (s+hi*q+H) O hO hn
  have hf:=BoundaryApplication.Range.query_bounds E w (s+hi*q+H) O hO hn
  simp only [contexts]
  constructor <;> omega

theorem contexts_work (C E : DFA α) (w : Word α) (I s H q lo hi O : Nat)
    (hq : q≤H) (hlo : lo≤hi) (hI : I≤s+lo*q) (hO : s+hi*q+H≤O) (hn : O≤w.length) :
    (contexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      I s H q lo hi O).work≤4*C.stateCount+2*E.stateCount+48*(Nat.log2 w.length+2)+18 := by
  have hm:=Nat.mul_le_mul_right q hlo
  have ha:=BoundaryApplication.Range.query_work C w I (s+lo*q) hI (by omega)
  have hb:=BoundaryApplication.Range.query_work C w s (s+q) (by omega) (by omega)
  have hc:=BoundaryApplication.Range.query_work C w (s+(H-q)) (s+H) (by omega) (by omega)
  have hd:=BoundaryApplication.Range.query_work E w (s+(H-q)) (s+H) (by omega) (by omega)
  have he:=BoundaryApplication.Range.query_work C w (s+hi*q+H) O hO hn
  have hf:=BoundaryApplication.Range.query_work E w (s+hi*q+H) O hO hn
  simp only [contexts]
  omega

abbrev Replay (C E : DFA α) := Map C.stateCount×Map E.stateCount

structure ReplayResult (C E : DFA α) where
  maps : Replay C E
  products : Nat
  visits : Nat
  work : Nat

def replay (C E : DFA α) (ci : BoundaryApplication.Range.Index C)
    (ei : BoundaryApplication.Range.Index E) (base L H : Nat) : ReplayResult C E :=
  let c := BoundaryApplication.Range.query C ci (base+L) (base+H)
  let e := BoundaryApplication.Range.query E ei (base+L) (base+H)
  ⟨(c.map,e.map),c.products+e.products,c.visits+e.visits,c.work+e.work+4⟩

theorem replay_value (C E : DFA α) (w : Word α) (base L H : Nat)
    (hLH : L≤H) (hn : base+H≤w.length) :
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      base L H).maps=(wordMap C (slice w (base+L) (base+H)),wordMap E (slice w (base+L) (base+H))) := by
  simp only [replay]
  rw [range_map C w (base+L) (base+H) (by omega) hn,
    range_map E w (base+L) (base+H) (by omega) hn]

theorem replay_bounds (C E : DFA α) (w : Word α) (base L H : Nat)
    (hLH : L≤H) (hn : base+H≤w.length) :
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      base L H).products≤2 ∧
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      base L H).visits≤2*(Nat.log2 w.length+2) ∧
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      base L H).work≤C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6 := by
  have hc:=BoundaryApplication.Range.query_bounds C w (base+L) (base+H) (by omega) hn
  have he:=BoundaryApplication.Range.query_bounds E w (base+L) (base+H) (by omega) hn
  have hc':=BoundaryApplication.Range.query_work C w (base+L) (base+H) (by omega) hn
  have he':=BoundaryApplication.Range.query_work E w (base+L) (base+H) (by omega) hn
  simp only [replay]
  constructor
  · omega
  · constructor <;> omega

end REWB.MaskedCluster
