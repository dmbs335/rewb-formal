import REWB.PeriodicCache

/-! Target projection for P1 with the earlier inner copy outside the target
    periodic interval. For a fixed outer start and target phases the five
    remaining block coordinates are existential, while the inner copy
    exponent is kept free. The source join below retains the actual
    phase word, not merely its length or a DFA equivalence class. -/
namespace REWB.P1Target
open REWB.Periodic
open REWB.PhaseSolver
open REWB.AffineProjection
open REWB.P2Periodic (factor factor_split endEndpoint end_pos end_valid interval_factor)
variable {α : Type}

structure Layout (X : Type) where
  j : X
  t : X
  e : X
  k : X
  f : X
  deriving Repr

def Layout.map (g : X→Y) (L : Layout X) : Layout Y :=
  ⟨g L.j,g L.t,g L.e,g L.k,g L.f⟩

def endpoints (ph : Layout Nat) : Layout Endpoint :=
  ⟨(.var 0,ph.j),(.var 1,ph.t),(.var 2,ph.e),(.var 3,ph.k),(.var 4,ph.f)⟩

def fixed (q p : Nat) : Endpoint := endEndpoint q p

def absolute (q : Nat) (L : Layout Endpoint) (env : List Int) : Layout Nat :=
  L.map (fun a=>a.pos q env)

def Valid (L : Layout Endpoint) (q n : Nat) (env : List Int) : Prop :=
  L.j.valid q n env ∧ L.t.valid q n env ∧ L.e.valid q n env ∧
  L.k.valid q n env ∧ L.f.valid q n env

def Witness (P : SevenDFA α) (s : Nat→α) (n p : Nat) (post : Word α)
    (x : Layout Nat) : Prop :=
  p≤x.j ∧ x.j≤x.t ∧ x.t≤x.e ∧ x.e≤x.k ∧ x.k≤x.f ∧ x.f≤n ∧
  P.D.accepts (factor s p x.j) ∧ P.B.accepts (factor s x.j x.t) ∧
  P.F.accepts (factor s x.t x.e) ∧ P.G.accepts (factor s x.e x.k) ∧
  P.H.accepts (factor s x.f n++post) ∧
  factor s p x.e=factor s x.k x.f

def constraints (P : SevenDFA α) (q n p : Nat) (post : Word α)
    (L : Layout Endpoint) : List (Constraint α) :=
  [.regular P.D (fixed q p) L.j,
   .regular P.B L.j L.t,
   .regular P.F L.t L.e,
   .regular P.G L.e L.k,
   .regular (contextual P.H [] post) L.f (endEndpoint q n),
   .equal (fixed q p) L.e L.k L.f]

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

theorem fixed_valid (q n p : Nat) (env : List Int) (hq : 0<q) (hp : p≤n) :
    (fixed q p).valid q n env := by
  have h := end_valid q p env hq
  exact ⟨h.1,h.2.1,Nat.le_trans h.2.2 hp⟩

theorem plain_iff (P : SevenDFA α) (q n p : Nat) (s : Nat→α) (post : Word α)
    (L : Layout Endpoint) (env : List Int) (hq : 0<q) (hp : p≤n) :
    Plain q n s (constraints P q n p post L) env ↔
      Valid L q n env ∧ Witness P s n p post (absolute q L env) := by
  unfold constraints
  simp only [plain_cons,plain_nil,and_true,Constraint.plain,Ordered,interval_factor,
    fixed,end_pos,contextual_accepts,List.append_nil,List.nil_append]
  constructor
  · rintro ⟨⟨⟨_,hj,hpj⟩,hD⟩,⟨⟨_,ht,hjt⟩,hB⟩,⟨⟨_,he,hte⟩,hF⟩,
      ⟨⟨_,hk,hek⟩,hG⟩,⟨⟨hf,_,hfn⟩,hH⟩,⟨_,⟨_,_,hkf⟩,_,hv⟩⟩
    exact ⟨⟨hj,ht,he,hk,hf⟩,
      ⟨hpj,hjt,hte,hek,hkf,hfn,hD,hB,hF,hG,hH,hv⟩⟩
  · rintro ⟨⟨hj,ht,he,hk,hf⟩,hw⟩
    rcases hw with ⟨hpj,hjt,hte,hek,hkf,hfn,hD,hB,hF,hG,hH,hv⟩
    have hpv := fixed_valid q n p env hq hp
    have hn := end_valid q n env hq
    have hpe : p≤L.e.pos q env := Nat.le_trans hpj (Nat.le_trans hjt hte)
    exact ⟨⟨⟨hpv,hj,hpj⟩,hD⟩,⟨⟨hj,ht,hjt⟩,hB⟩,
      ⟨⟨ht,he,hte⟩,hF⟩,⟨⟨he,hk,hek⟩,hG⟩,⟨⟨hf,hn,hfn⟩,hH⟩,
      ⟨⟨hpv,he,hpe⟩,⟨hk,hf,hkf⟩,Nat.le_trans hpe hek,hv⟩⟩

/-- The first q-block is an exact string key, and rho is kept separately.
    The zero-exponent case is sound as well; the long-copy indexing
    algorithm can impose its own lower bound on m. -/
def keyWord (block : Word α) (rho m : Nat) : Word α :=
  repeatWord block m++block.take rho

private theorem segment_take (s : Nat→α) (a q r : Nat) (hr : r≤q) :
    (segment s a q).take r=segment s a r := by
  induction r generalizing a q with
  | zero => rfl
  | succ r ih =>
    cases q with
    | zero => omega
    | succ q =>
      change s a::(segment s (a+1) q).take r=s a::segment s (a+1) r
      rw [ih _ _ (by omega)]

theorem key_factor (s : Nat→α) (q n : Nat) (h : Period s n q)
    (a b : Endpoint) (env : List Int)
    (ha : a.valid q n env) (hb : b.valid q n env) (ho : a.pos q env≤b.pos q env)
    (hq : 0<q) (m rho : Nat)
    (hm : (countExpr a b).eval env=(m:Int)) (hr : tailLen q a b=rho) :
    factor s (a.pos q env) (b.pos q env)=keyWord (segment s a.phase q) rho m := by
  have hcoord := coordinate_length q (a.coordinate env) (b.coordinate env)
    hq ha.2.1 hb.2.1 ho
  have hcount := count_natural a b q n env ha hb ho
  rw [hm] at hcount
  have hmc : copies (a.coordinate env) (b.coordinate env)=m := by omega
  rw [tail_eq,hr,hmc] at hcoord
  have he := coordinate_factor h (a.coordinate env) (b.coordinate env)
    hq ha.2.1 hb.2.1 ho hb.2.2
  rw [tail_eq,hr,hmc] at he
  change factor s (a.pos q env) (b.pos q env)=segment s a.phase (m*q+rho) at he
  have hbound : a.phase+m*q+rho≤n := by
    have hpos : a.phase≤a.pos q env := by
      change a.phase≤(a.coordinate env).block*q+a.phase
      omega
    have hn := hb.2.2
    have hl := hcoord.2.2
    change b.pos q env-a.pos q env=m*q+rho at hl
    omega
  rw [he]
  unfold keyWord
  rw [segment_append,segment_repeated h a.phase m (by omega),
    ← segment_same_phase h a.phase m rho hbound,segment_take s a.phase q rho (by omega)]

/-- Formula with five local block variables and a sixth free count.
    No independent existential choice is made for individual factors. -/
def formula [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (n q p rho : Nat)
    (post : Word α) (ph : Layout Nat) : Formula :=
  let L := endpoints ph
  if tailLen q L.j L.t=rho then
    both (compileSystem q n s (constraints P q n p post L))
      (eq (countExpr L.j L.t) (.var 5))
  else []

def projection [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (n q p rho : Nat)
    (post : Word α) (ph : Layout Nat) : Formula :=
  project 5 (formula P s n q p rho post ph)

theorem formula_good [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (h : LeastPeriod s n q) (post : Word α) (ph : Layout Nat) :
    FormulaGood (formula P s n q p rho post ph) := by
  unfold formula
  dsimp only
  split
  · exact both_good _ _ (compileSystem_good q n s h _) (eq_good _ _)
  · intro C hC
    simp at hC

theorem formula_correct [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (h : LeastPeriod s n q) (hp : p≤n)
    (post : Word α) (ph : Layout Nat) (env : List Int) :
    Satisfies (formula P s n q p rho post ph) env ↔
      Valid (endpoints ph) q n env ∧
        Witness P s n p post (absolute q (endpoints ph) env) ∧
        tailLen q (endpoints ph).j (endpoints ph).t=rho ∧
        (countExpr (endpoints ph).j (endpoints ph).t).eval env=(Aff.var 5).eval env := by
  unfold formula
  by_cases ht : tailLen q (endpoints ph).j (endpoints ph).t=rho
  · rw [if_pos ht,both_correct,compileSystem_correct q n s h,
      plain_iff P q n p s post (endpoints ph) env h.1 hp,eq_correct]
    simp only [ht,true_and]
    constructor
    · rintro ⟨⟨hv,hw⟩,hc⟩
      exact ⟨hv,hw,hc⟩
    · rintro ⟨hv,hw,hc⟩
      exact ⟨⟨hv,hw⟩,hc⟩
  · rw [if_neg ht]
    constructor
    · rintro ⟨C,hC,_⟩
      simp at hC
    · rintro ⟨_,_,he,_⟩
      exact False.elim (ht he)

private theorem last_read (xs : List Int) (m : Int) :
    ((xs++[m])[xs.length]?).getD 0=m := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

theorem projection_correct [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho m : Nat) (h : LeastPeriod s n q) (hp : p≤n)
    (post : Word α) (ph : Layout Nat) :
    decideFormula (projection P s n q p rho post ph) [(m:Int)]=true ↔
      ∃ xs : List Int, xs.length=5 ∧
        let env := xs++[(m:Int)]
        Valid (endpoints ph) q n env ∧
        Witness P s n p post (absolute q (endpoints ph) env) ∧
        tailLen q (endpoints ph).j (endpoints ph).t=rho ∧
        (countExpr (endpoints ph).j (endpoints ph).t).eval env=(m:Int) := by
  unfold projection
  rw [decideFormula_correct _ _ (project_good _ _ (formula_good P s n q p rho h post ph)),
    project_correct _ _ _ (formula_good P s n q p rho h post ph),prefix_quantify,quantify_env]
  constructor
  · rintro ⟨xs,hxs,hs⟩
    have hv := (formula_correct P s n q p rho h hp post ph _).mp hs
    have hm : (Aff.var 5).eval (xs++[(m:Int)])=(m:Int) := by
      change ((xs++[(m:Int)])[5]?).getD 0=(m:Int)
      rw [← hxs,last_read]
    rw [hm] at hv
    exact ⟨xs,hxs,hv⟩
  · rintro ⟨xs,hxs,hv⟩
    have hm : (Aff.var 5).eval (xs++[(m:Int)])=(m:Int) := by
      change ((xs++[(m:Int)])[5]?).getD 0=(m:Int)
      rw [← hxs,last_read]
    refine ⟨xs,hxs,(formula_correct P s n q p rho h hp post ph _).mpr ?_⟩
    rw [hm]
    exact hv

def SourceOK (P : SevenDFA α) (text u : Word α) : Prop :=
  ∃ a c,text=a++u++c ∧ P.A.accepts a ∧ P.C.accepts c

/-- Reassemble the actual P1 normal form from the projected target
    and an earlier source carrying exactly the same word. -/
theorem join_sound (P : SevenDFA α) (s : Nat→α) (n p : Nat)
    (pre post : Word α) (x : Layout Nat) (u : Word α)
    (ht : Witness P s n p post x)
    (hs : SourceOK P (pre++factor s 0 p) u)
    (hu : u=factor s x.j x.t) :
    MatchesWithin P.nested1 (pre++segment s 0 n++post) 2 := by
  rcases ht with ⟨hpj,hjt,hte,hek,hkf,hfn,hD,hB,hF,hG,hH,hv⟩
  rcases hs with ⟨a,c,hpre,hA,hC⟩
  have hwhole : segment s 0 n=factor s 0 p++factor s p x.j++
      factor s x.j x.t++factor s x.t x.e++factor s x.e x.k++
      factor s x.k x.f++factor s x.f n := by
    change factor s 0 n=_
    rw [factor_split s 0 p n (by omega) (by omega),
      factor_split s p x.j n hpj (by omega),
      factor_split s x.j x.t n hjt (by omega),
      factor_split s x.t x.e n hte (by omega),
      factor_split s x.e x.k n hek (by omega),
      factor_split s x.k x.f n hkf hfn]
    simp only [List.append_assoc]
  have hbody : factor s p x.e=factor s p x.j++factor s x.j x.t++factor s x.t x.e := by
    rw [factor_split s p x.j x.e hpj (by omega),
      factor_split s x.j x.t x.e hjt hte]
    simp only [List.append_assoc]
  apply (REWB.Witness.nested1_iff P _).mpr
  refine ⟨a,u,c,factor s p x.j,factor s x.t x.e,factor s x.e x.k,
    factor s x.f n++post,hA,by rwa [hu],hC,hD,hF,hG,hH,?_⟩
  rw [hwhole,← hv,hbody,← hu]
  simp only [← List.append_assoc]
  rw [hpre]

/-- The join on the exact period word and free exponent cannot create
    a false match. No source-index completeness or amortization is
    assumed by this theorem. -/
theorem projected_join_sound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho m : Nat) (h : LeastPeriod s n q) (hp : p≤n)
    (pre post : Word α) (ph : Layout Nat)
    (ht : decideFormula (projection P s n q p rho post ph) [(m:Int)]=true)
    (hs : SourceOK P (pre++factor s 0 p) (keyWord (segment s ph.j q) rho m)) :
    MatchesWithin P.nested1 (pre++segment s 0 n++post) 2 := by
  obtain ⟨xs,hxs,hv,hw,hr,hm⟩ :=
    (projection_correct P s n q p rho m h hp post ph).mp ht
  let L := endpoints ph
  let env := xs++[(m:Int)]
  have ho : L.j.pos q env≤L.t.pos q env := hw.2.1
  have he := key_factor s q n h.2.1 L.j L.t env hv.1 hv.2.1 ho h.1 m rho hm hr
  exact join_sound P s n p pre post _ _ hw hs he.symm

end REWB.P1Target
