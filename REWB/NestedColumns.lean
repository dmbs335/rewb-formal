import REWB.OuterColumn

/-! Exact endpoint relations for the nested normal forms. This module proves
    semantic reductions, not the running time of the eventual implementation. -/
namespace REWB.NestedColumns
open REWB.Spec (slice)
open REWB.OuterColumn (Common IsMaxCommon Anchored)
variable {α : Type}

private theorem drop_prefix (x y : Word α) :
    (x ++ y).drop x.length = y := by
  induction x with
  | nil => rfl
  | cons c cs ih => exact ih

private theorem take_prefix (x y : Word α) :
    (x ++ y).take x.length = x := by
  induction x with
  | nil => rfl
  | cons c cs ih =>
    change c :: (cs ++ y).take cs.length = c :: cs
    rw [ih]

theorem slice_block (pre block post : Word α) :
    slice (pre ++ block ++ post) pre.length (pre.length + block.length) = block := by
  have h : pre.length + block.length - pre.length = block.length := by omega
  simp only [slice, h, List.append_assoc, drop_prefix, take_prefix]

theorem slice_at (w pre block post : Word α) (l r : Nat)
    (hw : w = pre ++ block ++ post) (hl : l = pre.length)
    (hr : r = pre.length + block.length) :
    slice w l r = block := by
  rw [hw,hl,hr]
  exact slice_block pre block post

theorem slice_full (w : Word α) : slice w 0 w.length = w := by
  simpa using slice_block ([] : Word α) w []

/-- The last capture can close at e and be copied after its G gap. -/
def Outer (P : SevenDFA α) (w : Word α) (p e : Nat) : Prop :=
  ∃ f, Anchored P.G P.H w p e f

/-- Absorb F backwards into the outer-copy condition. -/
def ReadyState (P : SevenDFA α) (w : Word α) (p t : Nat)
    (q : Fin P.F.stateCount) : Prop :=
  ∃ e, t ≤ e ∧ Outer P w p e ∧
    P.F.final (P.F.run q (slice w t e)) = true

def Ready (P : SevenDFA α) (w : Word α) (p t : Nat) : Prop :=
  ReadyState P w p t P.F.initial

theorem ready_iff (P : SevenDFA α) (w : Word α) (p t : Nat) :
    Ready P w p t ↔
      ∃ e, t ≤ e ∧ Outer P w p e ∧ P.F.accepts (slice w t e) := Iff.rfl

theorem readyState_step (P : SevenDFA α) (w : Word α) (p t : Nat)
    (q : Fin P.F.stateCount) :
    ReadyState P w p t q ↔
      (Outer P w p t ∧ P.F.final q = true) ∨
        ReadyState P w p (t+1) (P.F.run q (slice w t (t+1))) := by
  constructor
  · rintro ⟨e,hte,ho,hf⟩
    by_cases h : e = t
    · subst e
      exact Or.inl ⟨ho,by simpa only [OuterColumn.slice_self,DFA.run] using hf⟩
    · have ht : t+1 ≤ e := by omega
      rw [OuterColumn.slice_split w t (t+1) e (by omega) ht, DFA.run_append] at hf
      exact Or.inr ⟨e,ht,ho,hf⟩
  · rintro (⟨ho,hf⟩ | ⟨e,hte,ho,hf⟩)
    · exact ⟨t,Nat.le_refl t,ho,by simpa only [OuterColumn.slice_self,DFA.run] using hf⟩
    · refine ⟨e,by omega,ho,?_⟩
      rw [OuterColumn.slice_split w t (t+1) e (by omega) hte,DFA.run_append]
      exact hf

theorem readyState_terminal (P : SevenDFA α) (w : Word α) (p : Nat)
    (q : Fin P.F.stateCount) :
    ReadyState P w p w.length q ↔ Outer P w p w.length ∧ P.F.final q = true := by
  constructor
  · rintro ⟨e,he,⟨f,hf⟩,hq⟩
    have h1 := hf.2.1
    have h2 := hf.2.2.1
    have heq : e = w.length := by omega
    subst e
    exact ⟨⟨f,hf⟩,by simpa only [OuterColumn.slice_self,DFA.run] using hq⟩
  · rintro ⟨ho,hq⟩
    exact ⟨w.length,Nat.le_refl _,ho,by simpa only [OuterColumn.slice_self,DFA.run] using hq⟩

/-- Absorb the B segment of P2 by a forward seeded DFA scan. -/
def First2 (P : SevenDFA α) (w : Word α) (i t : Nat) : Prop :=
  ∃ p, p ≤ i ∧ Ready P w p t ∧
    P.A.accepts (slice w 0 p) ∧ P.B.accepts (slice w p i)

theorem first2_active (P : SevenDFA α) (w : Word α) (i t : Nat) :
    First2 P w i t ↔
      ∃ q, OuterColumn.Active P.B w
        (fun p q0 => Ready P w p t ∧ P.A.accepts (slice w 0 p) ∧ q0 = P.B.initial)
        i q ∧ P.B.final q = true := by
  constructor
  · rintro ⟨p,hpi,hr,ha,hb⟩
    exact ⟨P.B.run P.B.initial (slice w p i),
      ⟨p,P.B.initial,hpi,⟨hr,ha,rfl⟩,rfl⟩,hb⟩
  · rintro ⟨q,⟨p,q0,hpi,⟨hr,ha,hq⟩,hrun⟩,hf⟩
    subst q0
    refine ⟨p,hpi,hr,ha,?_⟩
    unfold DFA.accepts
    rw [hrun]
    exact hf

/-- Equal-length prefix cancellation for aligned common suffixes. -/
private theorem equal_prefix {x y z v : Word α}
    (h : x ++ y = z ++ v) (hlen : x.length = z.length) : x = z := by
  have hx := congrArg (fun t : Word α => t.take x.length) h
  rw [take_prefix] at hx
  rw [hlen,take_prefix] at hx
  exact hx

theorem aligned_prefix (w : Word α) (a t d k : Nat)
    (hat : a ≤ t) (ht : t ≤ w.length) (hd : Common w a t d) (hk : k ≤ d) :
    slice w (a-d) (a-k) = slice w (t-d) (t-k) := by
  rcases hd with ⟨hda,hdt,he⟩
  have hx := OuterColumn.slice_split w (a-d) (a-k) a (by omega) (by omega)
  have hy := OuterColumn.slice_split w (t-d) (t-k) t (by omega) (by omega)
  apply equal_prefix (hx.symm.trans (he.trans hy))
  rw [OuterColumn.slice_length w (a-d) (a-k) (by omega) (by omega),
    OuterColumn.slice_length w (t-d) (t-k) (by omega) (by omega)]
  omega

def Inner1 (P : SevenDFA α) (w : Word α) (a t : Nat) : Prop :=
  ∃ i p j, i ≤ a ∧ a ≤ p ∧ p ≤ j ∧ j ≤ t ∧
    slice w i a = slice w j t ∧
    P.A.accepts (slice w 0 i) ∧ P.B.accepts (slice w i a) ∧
    P.C.accepts (slice w a p) ∧ P.D.accepts (slice w p j) ∧ Ready P w p t

def Inner2 (P : SevenDFA α) (w : Word α) (a t : Nat) : Prop :=
  ∃ i j, i ≤ a ∧ a ≤ j ∧ j ≤ t ∧
    slice w i a = slice w j t ∧
    First2 P w i t ∧ P.C.accepts (slice w i a) ∧ P.D.accepts (slice w a j)

/-- P2: one marked transition out of D into the capture DFA C. -/
def Anchored2 (P : SevenDFA α) (w : Word α) (a t d : Nat) : Prop :=
  ∃ i, a-d ≤ i ∧ i ≤ a ∧ First2 P w i t ∧
    P.D.final (P.D.run (P.D.run P.D.initial (slice w a (t-d)))
      (slice w (a-d) i)) = true ∧ P.C.accepts (slice w i a)

theorem inner2_iff_anchored (P : SevenDFA α) (w : Word α) (a t d : Nat)
    (hat : a ≤ t) (ht : t ≤ w.length) (hd : IsMaxCommon w a t d) :
    Inner2 P w a t ↔ Anchored2 P w a t d := by
  constructor
  · rintro ⟨i,j,hia,haj,hjt,he,hm,hc,hgap⟩
    have hlen := congrArg List.length he
    rw [OuterColumn.slice_length w i a hia (by omega),
      OuterColumn.slice_length w j t hjt ht] at hlen
    have hji : j = t-(a-i) := by omega
    have hc' : Common w a t (a-i) := by
      refine ⟨by omega,by omega,?_⟩
      have hi : a-(a-i) = i := by omega
      rw [hi,← hji]
      exact he
    have hk := hd.2 (a-i) hc'
    have hg := (OuterColumn.common_transport w a t d (a-i) hat ht hd.1 hk).2
    have hi : a-(a-i) = i := by omega
    rw [hi,← hji] at hg
    exact ⟨i,by omega,hia,hm,by simpa only [DFA.accepts,hg,DFA.run_append] using hgap,hc⟩
  · rintro ⟨i,hlo,hia,hm,hgap,hc⟩
    have hk : a-i ≤ d := by omega
    let j := t-(a-i)
    obtain ⟨⟨_,hn,he⟩,hg⟩ :=
      OuterColumn.common_transport w a t d (a-i) hat ht hd.1 hk
    have hi : a-(a-i) = i := by omega
    rw [hi] at he hg
    refine ⟨i,j,hia,by dsimp [j]; omega,by dsimp [j]; omega,he,hm,hc,?_⟩
    unfold DFA.accepts
    rw [show j = t-(a-i) from rfl,hg,DFA.run_append]
    exact hgap

/-- P1: transport the varying A prefix onto the second equal copy. -/
def Anchored1 (P : SevenDFA α) (w : Word α) (a t d : Nat) : Prop :=
  ∃ p j, a ≤ p ∧ p ≤ j ∧ t-d ≤ j ∧ j ≤ t ∧
    Ready P w p t ∧ P.C.accepts (slice w a p) ∧ P.D.accepts (slice w p j) ∧
    P.A.final (P.A.run (P.A.run P.A.initial (slice w 0 (a-d)))
      (slice w (t-d) j)) = true ∧ P.B.accepts (slice w j t)

theorem inner1_iff_anchored (P : SevenDFA α) (w : Word α) (a t d : Nat)
    (hat : a ≤ t) (ht : t ≤ w.length) (hd : IsMaxCommon w a t d) :
    Inner1 P w a t ↔ Anchored1 P w a t d := by
  constructor
  · rintro ⟨i,p,j,hia,hap,hpj,hjt,he,ha,hb,hc,hgap,hr⟩
    have hlen := congrArg List.length he
    rw [OuterColumn.slice_length w i a hia (by omega),
      OuterColumn.slice_length w j t hjt ht] at hlen
    have hji : j = t-(a-i) := by omega
    have hi : a-(a-i) = i := by omega
    have hc' : Common w a t (a-i) := by
      refine ⟨by omega,by omega,?_⟩
      rw [hi,← hji]
      exact he
    have hk := hd.2 (a-i) hc'
    have hpref := aligned_prefix w a t d (a-i) hat ht hd.1 hk
    rw [hi,← hji] at hpref
    have haeq : slice w 0 i = slice w 0 (a-d) ++ slice w (t-d) j := by
      rw [OuterColumn.slice_split w 0 (a-d) i (by omega) (by omega),hpref]
    refine ⟨p,j,hap,hpj,by omega,hjt,hr,hc,hgap,?_,?_⟩
    · simpa only [DFA.accepts,haeq,DFA.run_append] using ha
    · rw [← he]
      exact hb
  · rintro ⟨p,j,hap,hpj,hlo,hjt,hr,hc,hgap,ha,hb⟩
    have hda := hd.1.1
    have hdt := hd.1.2.1
    have hk : t-j ≤ d := by omega
    let i := a-(t-j)
    have hj : t-(t-j) = j := by omega
    have hpref := aligned_prefix w a t d (t-j) hat ht hd.1 hk
    have he := (OuterColumn.common_transport w a t d (t-j) hat ht hd.1 hk).1.2.2
    rw [hj] at hpref he
    have hi0 : a-d ≤ i := by dsimp [i]; omega
    have haeq : slice w 0 i = slice w 0 (a-d) ++ slice w (t-d) j := by
      rw [OuterColumn.slice_split w 0 (a-d) i (by omega) hi0]
      exact congrArg (fun s => slice w 0 (a-d) ++ s) hpref
    refine ⟨i,p,j,by dsimp [i]; omega,hap,hpj,hjt,he,?_,?_,hc,hgap,hr⟩
    · simpa only [DFA.accepts,haeq,DFA.run_append] using ha
    · rw [he]
      exact hb

theorem nested1_iff_endpoints (P : SevenDFA α) (w : Word α) :
    MatchesWithin P.nested1 w 2 ↔
      ∃ a t, a ≤ t ∧ t ≤ w.length ∧ Inner1 P w a t := by
  constructor
  · intro h
    rcases (Witness.nested1_iff P w).mp h with ⟨a0,u,c,d,ff,gg,hh,ha,hu,hc,hd,hf,hg,hhok,hw⟩
    let i := a0.length
    let a := a0.length + u.length
    let p := a0.length + u.length + c.length
    let j := a0.length + u.length + c.length + d.length
    let t := a0.length + u.length + c.length + d.length + u.length
    let e := a0.length + u.length + c.length + d.length + u.length + ff.length
    let k := a0.length + u.length + c.length + d.length + u.length + ff.length + gg.length
    let f := a0.length + u.length + c.length + d.length + u.length + ff.length + gg.length + (d ++ u ++ ff).length
    have hn : w.length = a0.length + u.length + c.length + d.length + u.length + ff.length + gg.length + (d ++ u ++ ff).length + hh.length := by
      rw [hw]; simp only [List.length_append]; omega
    have ho : f-(e-p) = k := by
      dsimp [i,a,p,j,t,e,k,f]; simp only [List.length_append]; omega
    have s0 : slice w 0 i = a0 := by
      apply slice_at w ([]) (a0) (u ++ c ++ d ++ u ++ ff ++ gg ++ (d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s1 : slice w i a = u := by
      apply slice_at w (a0) (u) (c ++ d ++ u ++ ff ++ gg ++ (d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s2 : slice w a p = c := by
      apply slice_at w (a0 ++ u) (c) (d ++ u ++ ff ++ gg ++ (d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s3 : slice w p j = d := by
      apply slice_at w (a0 ++ u ++ c) (d) (u ++ ff ++ gg ++ (d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s4 : slice w j t = u := by
      apply slice_at w (a0 ++ u ++ c ++ d) (u) (ff ++ gg ++ (d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s5 : slice w t e = ff := by
      apply slice_at w (a0 ++ u ++ c ++ d ++ u) (ff) (gg ++ (d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s6 : slice w e k = gg := by
      apply slice_at w (a0 ++ u ++ c ++ d ++ u ++ ff) (gg) ((d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s7 : slice w k f = (d ++ u ++ ff) := by
      apply slice_at w (a0 ++ u ++ c ++ d ++ u ++ ff ++ gg) ((d ++ u ++ ff)) (hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s8 : slice w f w.length = hh := by
      apply slice_at w (a0 ++ u ++ c ++ d ++ u ++ ff ++ gg ++ (d ++ u ++ ff)) (hh) ([])
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · rw [hn]; dsimp [i,a,p,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have sv : slice w p e = (d ++ u ++ ff) := by
      rw [OuterColumn.slice_split w p j e (by dsimp [i,a,p,j,t,e,k,f]; omega) (by dsimp [i,a,p,j,t,e,k,f]; omega)]
      rw [OuterColumn.slice_split w j t e (by dsimp [i,a,p,j,t,e,k,f]; omega) (by dsimp [i,a,p,j,t,e,k,f]; omega)]
      rw [s3,s4,s5]; simp only [List.append_assoc]
    have hready : Ready P w p t := by
      apply (ready_iff P w p t).mpr
      refine ⟨e,by dsimp [t,e]; omega,⟨f,?_⟩,?_⟩
      · refine ⟨by dsimp [p,e]; omega,by dsimp [e,f]; omega,
          by rw [hn]; dsimp [f]; omega,by dsimp [p,e,f]; simp only [List.length_append]; omega,?_,?_,?_⟩
        · rw [ho,sv,s7]
        · rw [ho,s6]; exact hg
        · rw [s8]; exact hhok
      · rw [s5]; exact hf
    refine ⟨a,t,by dsimp [a,t]; omega,by rw [hn]; dsimp [t]; omega,?_⟩
    refine ⟨i,p,j,by dsimp [i,a]; omega,by dsimp [a,p]; omega,
      by dsimp [p,j]; omega,by dsimp [j,t]; omega,?_,?_,?_,?_,?_,hready⟩
    · rw [s1,s4]
    · rw [s0]; exact ha
    · rw [s1]; exact hu
    · rw [s2]; exact hc
    · rw [s3]; exact hd
  · rintro ⟨a,t,hat,ht,hi⟩
    rcases hi with ⟨i,p,j,hia,hap,hpj,hjt,he,ha,hb,hc,hd,hr⟩
    rcases (ready_iff P w p t).mp hr with ⟨e,hte,⟨f,ho⟩,hf⟩
    rcases ho with ⟨hpe,hef,hfn,hn,hov,hg,hh⟩
    let k := f-(e-p)
    have hek : e ≤ k := by dsimp [k]; omega
    have hkf : k ≤ f := by dsimp [k]; omega
    have hwhole : w = slice w 0 i ++ slice w i a ++ slice w a p ++ slice w p j ++ slice w j t ++ slice w t e ++ slice w e k ++ slice w k f ++ slice w f w.length := by
      apply (slice_full w).symm.trans
      rw [OuterColumn.slice_split w 0 i w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w i a w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w a p w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w p j w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w j t w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w t e w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w e k w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w k f w.length (by omega) (by omega)]
      simp only [List.append_assoc]
    have hbody : slice w p e = slice w p j ++ slice w j t ++ slice w t e := by
      rw [OuterColumn.slice_split w p j e (by omega) (by omega)]
      rw [OuterColumn.slice_split w j t e (by omega) (by omega)]
      simp only [List.append_assoc]
    change slice w p e = slice w k f at hov
    change P.G.accepts (slice w e k) at hg
    rw [hbody] at hov
    apply (Witness.nested1_iff P w).mpr
    refine ⟨slice w 0 i,slice w i a,slice w a p,slice w p j,slice w t e,
      slice w e k,slice w f w.length,ha,hb,hc,hd,hf,hg,hh,?_⟩
    exact hwhole.trans (by rw [← hov,← he] <;> simp only [List.append_assoc])

theorem nested2_iff_endpoints (P : SevenDFA α) (w : Word α) :
    MatchesWithin P.nested2 w 2 ↔
      ∃ a t, a ≤ t ∧ t ≤ w.length ∧ Inner2 P w a t := by
  constructor
  · intro h
    rcases (Witness.nested2_iff P w).mp h with ⟨a0,b,u,d,ff,gg,hh,ha,hb,hu,hd,hf,hg,hhok,hw⟩
    let p := a0.length
    let i := a0.length + b.length
    let a := a0.length + b.length + u.length
    let j := a0.length + b.length + u.length + d.length
    let t := a0.length + b.length + u.length + d.length + u.length
    let e := a0.length + b.length + u.length + d.length + u.length + ff.length
    let k := a0.length + b.length + u.length + d.length + u.length + ff.length + gg.length
    let f := a0.length + b.length + u.length + d.length + u.length + ff.length + gg.length + (b ++ u ++ d ++ u ++ ff).length
    have hn : w.length = a0.length + b.length + u.length + d.length + u.length + ff.length + gg.length + (b ++ u ++ d ++ u ++ ff).length + hh.length := by
      rw [hw]; simp only [List.length_append]; omega
    have ho : f-(e-p) = k := by
      dsimp [p,i,a,j,t,e,k,f]; simp only [List.length_append]; omega
    have s0 : slice w 0 p = a0 := by
      apply slice_at w ([]) (a0) (b ++ u ++ d ++ u ++ ff ++ gg ++ (b ++ u ++ d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s1 : slice w p i = b := by
      apply slice_at w (a0) (b) (u ++ d ++ u ++ ff ++ gg ++ (b ++ u ++ d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s2 : slice w i a = u := by
      apply slice_at w (a0 ++ b) (u) (d ++ u ++ ff ++ gg ++ (b ++ u ++ d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s3 : slice w a j = d := by
      apply slice_at w (a0 ++ b ++ u) (d) (u ++ ff ++ gg ++ (b ++ u ++ d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s4 : slice w j t = u := by
      apply slice_at w (a0 ++ b ++ u ++ d) (u) (ff ++ gg ++ (b ++ u ++ d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s5 : slice w t e = ff := by
      apply slice_at w (a0 ++ b ++ u ++ d ++ u) (ff) (gg ++ (b ++ u ++ d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s6 : slice w e k = gg := by
      apply slice_at w (a0 ++ b ++ u ++ d ++ u ++ ff) (gg) ((b ++ u ++ d ++ u ++ ff) ++ hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s7 : slice w k f = (b ++ u ++ d ++ u ++ ff) := by
      apply slice_at w (a0 ++ b ++ u ++ d ++ u ++ ff ++ gg) ((b ++ u ++ d ++ u ++ ff)) (hh)
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have s8 : slice w f w.length = hh := by
      apply slice_at w (a0 ++ b ++ u ++ d ++ u ++ ff ++ gg ++ (b ++ u ++ d ++ u ++ ff)) (hh) ([])
      · rw [hw]; simp only [List.append_assoc, List.nil_append, List.append_nil]
      · dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
      · rw [hn]; dsimp [p,i,a,j,t,e,k,f] <;> simp only [List.length_append, List.length_nil] <;> omega
    have sv : slice w p e = (b ++ u ++ d ++ u ++ ff) := by
      rw [OuterColumn.slice_split w p i e (by dsimp [p,i,a,j,t,e,k,f]; omega) (by dsimp [p,i,a,j,t,e,k,f]; omega)]
      rw [OuterColumn.slice_split w i a e (by dsimp [p,i,a,j,t,e,k,f]; omega) (by dsimp [p,i,a,j,t,e,k,f]; omega)]
      rw [OuterColumn.slice_split w a j e (by dsimp [p,i,a,j,t,e,k,f]; omega) (by dsimp [p,i,a,j,t,e,k,f]; omega)]
      rw [OuterColumn.slice_split w j t e (by dsimp [p,i,a,j,t,e,k,f]; omega) (by dsimp [p,i,a,j,t,e,k,f]; omega)]
      rw [s1,s2,s3,s4,s5]; simp only [List.append_assoc]
    have hready : Ready P w p t := by
      apply (ready_iff P w p t).mpr
      refine ⟨e,by dsimp [t,e]; omega,⟨f,?_⟩,?_⟩
      · refine ⟨by dsimp [p,e]; omega,by dsimp [e,f]; omega,
          by rw [hn]; dsimp [f]; omega,by dsimp [p,e,f]; simp only [List.length_append]; omega,?_,?_,?_⟩
        · rw [ho,sv,s7]
        · rw [ho,s6]; exact hg
        · rw [s8]; exact hhok
      · rw [s5]; exact hf
    refine ⟨a,t,by dsimp [a,t]; omega,by rw [hn]; dsimp [t]; omega,?_⟩
    refine ⟨i,j,by dsimp [i,a]; omega,by dsimp [a,j]; omega,
      by dsimp [j,t]; omega,?_,⟨p,by dsimp [p,i]; omega,hready,?_,?_⟩,?_,?_⟩
    · rw [s2,s4]
    · rw [s0]; exact ha
    · rw [s1]; exact hb
    · rw [s2]; exact hu
    · rw [s3]; exact hd
  · rintro ⟨a,t,hat,ht,hi⟩
    rcases hi with ⟨i,j,hia,haj,hjt,he,⟨p,hpi,hr,ha,hb⟩,hc,hd⟩
    rcases (ready_iff P w p t).mp hr with ⟨e,hte,⟨f,ho⟩,hf⟩
    rcases ho with ⟨hpe,hef,hfn,hn,hov,hg,hh⟩
    let k := f-(e-p)
    have hek : e ≤ k := by dsimp [k]; omega
    have hkf : k ≤ f := by dsimp [k]; omega
    have hwhole : w = slice w 0 p ++ slice w p i ++ slice w i a ++ slice w a j ++ slice w j t ++ slice w t e ++ slice w e k ++ slice w k f ++ slice w f w.length := by
      apply (slice_full w).symm.trans
      rw [OuterColumn.slice_split w 0 p w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w p i w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w i a w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w a j w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w j t w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w t e w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w e k w.length (by omega) (by omega)]
      rw [OuterColumn.slice_split w k f w.length (by omega) (by omega)]
      simp only [List.append_assoc]
    have hbody : slice w p e = slice w p i ++ slice w i a ++ slice w a j ++ slice w j t ++ slice w t e := by
      rw [OuterColumn.slice_split w p i e (by omega) (by omega)]
      rw [OuterColumn.slice_split w i a e (by omega) (by omega)]
      rw [OuterColumn.slice_split w a j e (by omega) (by omega)]
      rw [OuterColumn.slice_split w j t e (by omega) (by omega)]
      simp only [List.append_assoc]
    change slice w p e = slice w k f at hov
    change P.G.accepts (slice w e k) at hg
    rw [hbody] at hov
    apply (Witness.nested2_iff P w).mpr
    refine ⟨slice w 0 p,slice w p i,slice w i a,slice w a j,slice w t e,
      slice w e k,slice w f w.length,ha,hb,hc,hd,hf,hg,hh,?_⟩
    exact hwhole.trans (by rw [← hov,← he] <;> simp only [List.append_assoc])

theorem nested1_reduced [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    MatchesWithin P.nested1 w 2 ↔
      ∃ a t, a ≤ t ∧ t ≤ w.length ∧
        Anchored1 P w a t (OuterColumn.maxCommon w a t a) := by
  rw [nested1_iff_endpoints]
  constructor
  · rintro ⟨a,t,hat,ht,hi⟩
    exact ⟨a,t,hat,ht,(inner1_iff_anchored P w a t _ hat ht
      (OuterColumn.maxCommon_isMax w a t)).mp hi⟩
  · rintro ⟨a,t,hat,ht,hi⟩
    exact ⟨a,t,hat,ht,(inner1_iff_anchored P w a t _ hat ht
      (OuterColumn.maxCommon_isMax w a t)).mpr hi⟩

theorem nested2_reduced [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    MatchesWithin P.nested2 w 2 ↔
      ∃ a t, a ≤ t ∧ t ≤ w.length ∧
        Anchored2 P w a t (OuterColumn.maxCommon w a t a) := by
  rw [nested2_iff_endpoints]
  constructor
  · rintro ⟨a,t,hat,ht,hi⟩
    exact ⟨a,t,hat,ht,(inner2_iff_anchored P w a t _ hat ht
      (OuterColumn.maxCommon_isMax w a t)).mp hi⟩
  · rintro ⟨a,t,hat,ht,hi⟩
    exact ⟨a,t,hat,ht,(inner2_iff_anchored P w a t _ hat ht
      (OuterColumn.maxCommon_isMax w a t)).mpr hi⟩

end REWB.NestedColumns
