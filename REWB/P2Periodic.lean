import REWB.PhaseSystem

/-! The small-period P2 branch, with all eight endpoints in one run.
    A fixed eight-phase assignment is solved by existential projection
    of eight block coordinates. The outer-prefix and outer-suffix DFA
    contexts may extend outside this run. -/
namespace REWB.P2Periodic
open REWB.Periodic
open REWB.PhaseSolver
open REWB.AffineProjection
variable {α : Type}

structure Layout (X : Type) where
  p : X
  i : X
  a : X
  j : X
  t : X
  e : X
  k : X
  f : X
  deriving Repr

def Layout.map (g : X→Y) (v : Layout X) : Layout Y :=
  ⟨g v.p,g v.i,g v.a,g v.j,g v.t,g v.e,g v.k,g v.f⟩

def phaseOf (q : Nat) (v : Layout Nat) : Layout Nat := v.map (fun i=>i%q)

def endpoints (ph : Layout Nat) : Layout Endpoint :=
  ⟨(.var 0,ph.p),(.var 1,ph.i),(.var 2,ph.a),(.var 3,ph.j),
    (.var 4,ph.t),(.var 5,ph.e),(.var 6,ph.k),(.var 7,ph.f)⟩

def absolute (q : Nat) (L : Layout Endpoint) (env : List Int) : Layout Nat :=
  L.map (fun a=>a.pos q env)

def envOf (q : Nat) (x : Layout Nat) : List Int :=
  [Int.ofNat (x.p/q),Int.ofNat (x.i/q),Int.ofNat (x.a/q),Int.ofNat (x.j/q),
   Int.ofNat (x.t/q),Int.ofNat (x.e/q),Int.ofNat (x.k/q),Int.ofNat (x.f/q)]

theorem envOf_length (q : Nat) (x : Layout Nat) : (envOf q x).length=8 := rfl

def factor (s : Nat→α) (a b : Nat) : Word α := segment s a (b-a)

theorem factor_split (s : Nat→α) (a b c : Nat) (hab : a≤b) (hbc : b≤c) :
    factor s a c=factor s a b++factor s b c := by
  unfold factor
  have h1 : c-a=(b-a)+(c-b) := by omega
  have h2 : a+(b-a)=b := by omega
  rw [h1,segment_append,h2]

/-- The actual in-run witness. Both outer copies are nonoverlapping.
    The first and second inner occurrences both lie in the first outer
    capture. The run may be strictly inside the full input. -/
def Witness (P : SevenDFA α) (s : Nat→α) (n : Nat) (pre post : Word α)
    (x : Layout Nat) : Prop :=
  x.p≤x.i ∧ x.i≤x.a ∧ x.a≤x.j ∧ x.j≤x.t ∧ x.t≤x.e ∧
  x.e≤x.k ∧ x.k≤x.f ∧ x.f≤n ∧
  P.A.accepts (pre++factor s 0 x.p) ∧
  P.B.accepts (factor s x.p x.i) ∧
  P.C.accepts (factor s x.i x.a) ∧
  P.D.accepts (factor s x.a x.j) ∧
  P.F.accepts (factor s x.t x.e) ∧
  P.G.accepts (factor s x.e x.k) ∧
  P.H.accepts (factor s x.f n++post) ∧
  factor s x.i x.a=factor s x.j x.t ∧
  factor s x.p x.e=factor s x.k x.f

def zeroEndpoint : Endpoint := (.lit 0,0)
def endEndpoint (q n : Nat) : Endpoint := (.lit (Int.ofNat (n/q)),n%q)

theorem zero_valid (q n : Nat) (env : List Int) (hq : 0<q) :
    zeroEndpoint.valid q n env := by
  exact ⟨Int.le_refl _,hq,by simp [Endpoint.pos,zeroEndpoint,Endpoint.coordinate,Endpoint.phase,Endpoint.number,Aff.eval,Coord.pos]⟩

theorem zero_pos (q : Nat) (env : List Int) : zeroEndpoint.pos q env=0 := by
  simp [zeroEndpoint,Endpoint.pos,Endpoint.coordinate,Endpoint.phase,Endpoint.number,Coord.pos,Aff.eval]

theorem end_pos (q n : Nat) (env : List Int) : (endEndpoint q n).pos q env=n := by
  have he : (endEndpoint q n).coordinate env=coord q n := by
    simp [endEndpoint,Endpoint.coordinate,Endpoint.phase,Endpoint.number,Aff.eval,coord]
  unfold Endpoint.pos
  rw [he,coord_pos]

theorem end_valid (q n : Nat) (env : List Int) (hq : 0<q) :
    (endEndpoint q n).valid q n env := by
  refine ⟨Int.ofNat_nonneg _,Nat.mod_lt _ hq,?_⟩
  rw [end_pos]
  exact Nat.le_refl _

def constraints (P : SevenDFA α) (q n : Nat) (pre post : Word α)
    (L : Layout Endpoint) : List (Constraint α) :=
  [.regular (contextual P.A pre []) zeroEndpoint L.p,
   .regular P.B L.p L.i,
   .regular P.C L.i L.a,
   .regular P.D L.a L.j,
   .regular P.F L.t L.e,
   .regular P.G L.e L.k,
   .regular (contextual P.H [] post) L.f (endEndpoint q n),
   .equal L.i L.a L.j L.t,
   .equal L.p L.e L.k L.f]

def Valid (L : Layout Endpoint) (q n : Nat) (env : List Int) : Prop :=
  L.p.valid q n env ∧ L.i.valid q n env ∧ L.a.valid q n env ∧ L.j.valid q n env ∧
  L.t.valid q n env ∧ L.e.valid q n env ∧ L.k.valid q n env ∧ L.f.valid q n env

private theorem plain_cons (q n : Nat) (s : Nat→α) (c : Constraint α)
    (cs : List (Constraint α)) (env : List Int) :
    Plain q n s (c::cs) env ↔ c.plain q n s env ∧ Plain q n s cs env := by
  constructor
  · intro h
    exact ⟨h _ (by simp),fun x hx=>h x (by simp [hx])⟩
  · rintro ⟨hc,hs⟩ x hx
    rcases List.mem_cons.mp hx with he|hm
    · subst x
      exact hc
    · exact hs x hm

private theorem plain_nil (q n : Nat) (s : Nat→α) (env : List Int) :
    Plain q n s [] env := by
  intro c hc
  simp at hc

theorem interval_factor (q : Nat) (s : Nat→α) (a b : Endpoint) (env : List Int) :
    (interval a b env).value q s=factor s (a.pos q env) (b.pos q env) := rfl

theorem plain_iff (P : SevenDFA α) (q n : Nat) (s : Nat→α) (pre post : Word α)
    (L : Layout Endpoint) (env : List Int) (hq : 0<q) :
    Plain q n s (constraints P q n pre post L) env ↔
      Valid L q n env ∧ Witness P s n pre post (absolute q L env) := by
  unfold constraints
  simp only [plain_cons,plain_nil,and_true,Constraint.plain,Ordered,interval_factor,
    zero_pos,end_pos,contextual_accepts,List.append_nil,List.nil_append]
  constructor
  · rintro ⟨⟨⟨_,hp,_⟩,ha⟩,⟨⟨_,hi,hpi⟩,hb⟩,
      ⟨⟨_,haa,hia⟩,hc⟩,⟨⟨_,hj,haj⟩,hd⟩,
      ⟨⟨ht,he,hte⟩,hf⟩,⟨⟨_,hk,hek⟩,hg⟩,
      ⟨⟨hff,_,hfn⟩,hh⟩,
      ⟨_,⟨_,_,hjt⟩,_,hu⟩,⟨_,⟨_,_,hkf⟩,_,hv⟩⟩
    exact ⟨⟨hp,hi,haa,hj,ht,he,hk,hff⟩,
      ⟨hpi,hia,haj,hjt,hte,hek,hkf,hfn,ha,hb,hc,hd,hf,hg,hh,hu,hv⟩⟩
  · rintro ⟨⟨hp,hi,ha,hj,ht,he,hk,hf⟩,hw⟩
    rcases hw with ⟨hpi,hia,haj,hjt,hte,hek,hkf,hfn,hA,hB,hC,hD,hF,hG,hH,hu,hv⟩
    have hz : zeroEndpoint.valid q n env := zero_valid _ _ _ hq
    have hn : (endEndpoint q n).valid q n env := end_valid _ _ _ hq
    have hij : L.i.pos q env≤L.j.pos q env := Nat.le_trans hia haj
    have hpe : L.p.pos q env≤L.e.pos q env :=
      Nat.le_trans hpi (Nat.le_trans hia (Nat.le_trans haj (Nat.le_trans hjt hte)))
    exact ⟨⟨⟨hz,hp,Nat.zero_le _⟩,hA⟩,⟨⟨hp,hi,hpi⟩,hB⟩,
      ⟨⟨hi,ha,hia⟩,hC⟩,⟨⟨ha,hj,haj⟩,hD⟩,
      ⟨⟨ht,he,hte⟩,hF⟩,⟨⟨he,hk,hek⟩,hG⟩,
      ⟨⟨hf,hn,hfn⟩,hH⟩,
      ⟨⟨hi,ha,hia⟩,⟨hj,ht,hjt⟩,hij,hu⟩,
      ⟨⟨hp,he,hpe⟩,⟨hk,hf,hkf⟩,Nat.le_trans hpe hek,hv⟩⟩

/-- A run witness always induces a genuine P2 match of the full input.
    This is sound even for the small/empty capture cases. -/
theorem witness_sound (P : SevenDFA α) (s : Nat→α) (n : Nat)
    (pre post : Word α) (x : Layout Nat) (h : Witness P s n pre post x) :
    MatchesWithin P.nested2 (pre++segment s 0 n++post) 2 := by
  rcases h with ⟨hpi,hia,haj,hjt,hte,hek,hkf,hfn,hA,hB,hC,hD,hF,hG,hH,hu,hv⟩
  have hwhole : segment s 0 n =
      factor s 0 x.p++factor s x.p x.i++factor s x.i x.a++factor s x.a x.j++
        factor s x.j x.t++factor s x.t x.e++factor s x.e x.k++
        factor s x.k x.f++factor s x.f n := by
    change factor s 0 n=_
    rw [factor_split s 0 x.p n (by omega) (by omega),
      factor_split s x.p x.i n hpi (by omega),
      factor_split s x.i x.a n hia (by omega),
      factor_split s x.a x.j n haj (by omega),
      factor_split s x.j x.t n hjt (by omega),
      factor_split s x.t x.e n hte (by omega),
      factor_split s x.e x.k n hek (by omega),
      factor_split s x.k x.f n hkf hfn]
    simp only [List.append_assoc]
  have hbody : factor s x.p x.e =
      factor s x.p x.i++factor s x.i x.a++factor s x.a x.j++
        factor s x.j x.t++factor s x.t x.e := by
    rw [factor_split s x.p x.i x.e hpi (by omega),
      factor_split s x.i x.a x.e hia (by omega),
      factor_split s x.a x.j x.e haj (by omega),
      factor_split s x.j x.t x.e hjt hte]
    simp only [List.append_assoc]
  apply (REWB.Witness.nested2_iff P _).mpr
  refine ⟨pre++factor s 0 x.p,factor s x.p x.i,factor s x.i x.a,
    factor s x.a x.j,factor s x.t x.e,factor s x.e x.k,factor s x.f n++post,
    hA,hB,hC,hD,hF,hG,hH,?_⟩
  rw [hwhole,← hv,hbody,← hu]
  simp only [List.append_assoc]

def solveAt [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (n q : Nat)
    (pre post : Word α) (ph : Layout Nat) : Bool :=
  solveSystem q n s (constraints P q n pre post (endpoints ph)) 8 []

theorem solveAt_correct [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (h : LeastPeriod s n q) (pre post : Word α) (ph : Layout Nat) :
    solveAt P s n q pre post ph=true ↔
      ∃ env : List Int,env.length=8 ∧
        Valid (endpoints ph) q n env ∧
          Witness P s n pre post (absolute q (endpoints ph) env) := by
  rw [solveAt,solveSystem_correct q n s h]
  simp only [List.append_nil,plain_iff P q n s pre post (endpoints ph) _ h.1]

theorem solveAt_sound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (h : LeastPeriod s n q) (pre post : Word α) (ph : Layout Nat)
    (hs : solveAt P s n q pre post ph=true) :
    MatchesWithin P.nested2 (pre++segment s 0 n++post) 2 := by
  obtain ⟨env,_,_,hw⟩ := (solveAt_correct P s n q h pre post ph).mp hs
  exact witness_sound P s n pre post _ hw

theorem canonical_absolute (q : Nat) (x : Layout Nat) :
    absolute q (endpoints (phaseOf q x)) (envOf q x)=x := by
  have aux : ∀ z : Nat, (z/q)*q+z%q=z := by
    intro z
    exact coord_pos q z
  cases x
  simp [absolute,endpoints,phaseOf,Layout.map,Endpoint.pos,Endpoint.coordinate,
    Endpoint.number,Endpoint.phase,envOf,Aff.eval,Coord.pos,aux]

theorem canonical_valid (q n : Nat) (x : Layout Nat) (hq : 0<q)
    (h : x.p≤n ∧ x.i≤n ∧ x.a≤n ∧ x.j≤n ∧ x.t≤n ∧ x.e≤n ∧ x.k≤n ∧ x.f≤n) :
    Valid (endpoints (phaseOf q x)) q n (envOf q x) := by
  have aux : ∀ z : Nat, (z/q)*q+z%q=z := fun z=>coord_pos q z
  have hmod : ∀ z : Nat,z%q<q := fun z=>Nat.mod_lt z hq
  simpa [Valid,endpoints,phaseOf,Layout.map,Endpoint.valid,Endpoint.number,Endpoint.phase,
    Endpoint.coordinate,Endpoint.pos,envOf,Aff.eval,Coord.pos,aux,hmod] using h

/-- Complete for any concrete in-run witness with its actual phases. -/
theorem solveAt_complete [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (h : LeastPeriod s n q) (pre post : Word α) (x : Layout Nat)
    (hw : Witness P s n pre post x) :
    solveAt P s n q pre post (phaseOf q x)=true := by
  apply (solveAt_correct P s n q h pre post _).mpr
  have hn : x.p≤n ∧ x.i≤n ∧ x.a≤n ∧ x.j≤n ∧ x.t≤n ∧ x.e≤n ∧ x.k≤n ∧ x.f≤n := by
    rcases hw with ⟨hpi,hia,haj,hjt,hte,hek,hkf,hfn,_⟩
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,hfn⟩
  refine ⟨envOf q x,envOf_length q x,canonical_valid q n x h.1 hn,?_⟩
  rw [canonical_absolute]
  exact hw

end REWB.P2Periodic
