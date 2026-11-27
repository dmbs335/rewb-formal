import REWB.ResidualCachedDispatch
import REWB.IndexedGridAccounting
import Lean

/-! Kernel-checked polynomial envelopes for the concrete cache budgets.
The proof elaborator at the end only builds applications of the lemmas
in this file. It neither executes a matcher nor supplies a cost oracle.
Coefficients contain fixed-pattern data only; the text length, block
width, grid count and logarithmic height have separate degrees. -/
namespace REWB.ResidualCached.Growth

def height (n : Nat) : Nat := (n+2).log2+1

def scale (n s a b c d : Nat) : Nat :=
  (n+2)^a*(s+1)^b*(n/s+2)^c*(height n)^d

def Bound (n s value a b c d coefficient : Nat) : Prop :=
  value≤coefficient*scale n s a b c d

theorem scale_mono (n s a b c d a' b' c' d' : Nat)
    (ha : a≤a') (hb : b≤b') (hc : c≤c') (hd : d≤d') :
    scale n s a b c d≤scale n s a' b' c' d' := by
  apply Nat.mul_le_mul
  · apply Nat.mul_le_mul
    · exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) ha) (Nat.pow_le_pow_right (by omega) hb)
    · exact Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le (n/s+1))) hc
  · exact Nat.pow_le_pow_right (by unfold height; omega) hd

theorem weaken {n s x a b c d k a' b' c' d' : Nat} (h : Bound n s x a b c d k)
    (ha : a≤a') (hb : b≤b') (hc : c≤c') (hd : d≤d') : Bound n s x a' b' c' d' k :=
  Nat.le_trans h (Nat.mul_le_mul_left k (scale_mono n s a b c d a' b' c' d' ha hb hc hd))

theorem constant (n s x : Nat) : Bound n s x 0 0 0 0 x := by simp [Bound,scale]
theorem input (n s : Nat) : Bound n s n 1 0 0 0 1 := by simp [Bound,scale]
theorem width (n s : Nat) : Bound n s s 0 1 0 0 1 := by simp [Bound,scale]
theorem slots (n s : Nat) : Bound n s (n/s) 0 0 1 0 1 := by simp [Bound,scale]

theorem log0 (n s : Nat) : Bound n s n.log2 0 0 0 1 1 := by
  have hh:=CountedJoin.log2_mono (show n≤n+2 by omega)
  simp only [Bound,scale,Nat.pow_zero,Nat.pow_one,Nat.one_mul,height]
  omega

theorem log1 (n s : Nat) : Bound n s (n+1).log2 0 0 0 1 1 := by
  have hh:=CountedJoin.log2_mono (show n+1≤n+2 by omega)
  simp only [Bound,scale,Nat.pow_zero,Nat.pow_one,Nat.one_mul,height]
  omega

theorem log2 (n s : Nat) : Bound n s (n+2).log2 0 0 0 1 1 := by
  simp only [Bound,scale,Nat.pow_zero,Nat.pow_one,Nat.one_mul,height]
  omega

theorem doubledLog (n s : Nat) : Bound n s (2*(n+2)).log2 0 0 0 1 2 := by
  have hh:=Nat.mul_lt_mul_of_pos_left (Nat.lt_log2_self (n:=n+2)) (by decide : 0<2)
  have he : 2*2^((n+2).log2+1)=2^((n+2).log2+1+1) := by
    conv => rhs; rw [Nat.pow_succ]
    exact Nat.mul_comm _ _
  rw [he] at hh
  have hl:=(Nat.log2_lt (by omega : 2*(n+2)≠0)).mpr hh
  simp only [Bound,scale,Nat.pow_zero,Nat.pow_one,Nat.one_mul,height]
  omega

theorem ranks (σ n s : Nat) : Bound n s (RankIndex.width σ n) 0 0 0 1 (σ+2) := by
  simpa only [Bound,scale,Nat.pow_zero,Nat.pow_one,Nat.one_mul,height,IndexedGridAccounting.height]
    using IndexedGridAccounting.width_le σ n

theorem add {n s x y a b c d e f g h k l : Nat}
    (hx : Bound n s x a b c d k) (hy : Bound n s y e f g h l) :
    Bound n s (x+y) (max a e) (max b f) (max c g) (max d h) (k+l) := by
  have hx':=weaken hx (Nat.le_max_left a e) (Nat.le_max_left b f) (Nat.le_max_left c g) (Nat.le_max_left d h)
  have hy':=weaken hy (Nat.le_max_right a e) (Nat.le_max_right b f) (Nat.le_max_right c g) (Nat.le_max_right d h)
  change x+y≤(k+l)*scale n s (max a e) (max b f) (max c g) (max d h)
  rw [Nat.add_mul]
  exact Nat.add_le_add hx' hy'

theorem mul {n s x y a b c d e f g h k l : Nat}
    (hx : Bound n s x a b c d k) (hy : Bound n s y e f g h l) :
    Bound n s (x*y) (a+e) (b+f) (c+g) (d+h) (k*l) := by
  have hh:=Nat.mul_le_mul hx hy
  simpa only [Bound,scale,Nat.pow_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

theorem power {n s x a b c d k : Nat} (hx : Bound n s x a b c d k) (m : Nat) :
    Bound n s (x^m) (a*m) (b*m) (c*m) (d*m) (k^m) := by
  have hh:=Nat.pow_le_pow_left hx m
  simpa only [Bound,scale,Nat.mul_pow,←Nat.pow_mul] using hh

theorem minimumLeft {n s x y a b c d k : Nat} (hx : Bound n s x a b c d k) :
    Bound n s (min x y) a b c d k := Nat.le_trans (Nat.min_le_left _ _) hx

theorem minimumRight {n s x y a b c d k : Nat} (hy : Bound n s y a b c d k) :
    Bound n s (min x y) a b c d k := Nat.le_trans (Nat.min_le_right _ _) hy

theorem polynomial_log (n x k e : Nat) (hx : x≤k*(n+2)^e) :
    x.log2≤(k+e+2)*height n := by
  have hk : k<2^(k+1) := Nat.lt_of_lt_of_le (Nat.lt_log2_self (n:=k))
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right (Nat.log2_le_self k) 1))
  have hn : (n+2)^e≤(2^(height n))^e := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_log2_self (n:=n+2))) e
  have hp:=Nat.mul_lt_mul_of_lt_of_le hk hn (Nat.pow_pos (Nat.pow_pos (by decide : 0<2)))
  rw [←Nat.pow_mul,←Nat.pow_add] at hp
  by_cases hz : x=0
  · simp [hz]
  · have hl:=(Nat.log2_lt hz).mpr (Nat.lt_of_le_of_lt hx hp)
    rw [Nat.mul_comm (height n) e] at hl
    have hH : 1≤height n := by unfold height; omega
    have hc:=Nat.mul_le_mul_left (k+1) hH
    simp only [Nat.mul_one,Nat.add_mul] at hc ⊢
    omega

theorem logarithm {n s x a d k : Nat} (hx : Bound n s x a 0 0 d k) :
    Bound n s x.log2 0 0 0 1 (k*2^d+a+d+2) := by
  have hH : height n≤2*(n+2) := by have hh:=Nat.log2_le_self (n+2); unfold height; omega
  have hh:=Nat.pow_le_pow_left hH d
  have scaled:=Nat.mul_le_mul_left (k*(n+2)^a) hh
  have hp : x≤(k*2^d)*(n+2)^(a+d) := by
    simp only [Bound,scale,Nat.pow_zero,Nat.mul_one] at hx
    have hm:=Nat.le_trans hx (by simpa only [Nat.mul_assoc] using scaled)
    simpa only [Nat.mul_pow,Nat.pow_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hm
  have hl:=polynomial_log n x (k*2^d) (a+d) hp
  simpa only [Bound,scale,Nat.pow_zero,Nat.pow_one,Nat.one_mul,Nat.add_assoc] using hl

theorem sum {n s m a b c d : Nat} (f coefficients : Fin m→Nat)
    (h : ∀i,Bound n s (f i) a b c d (coefficients i)) :
    Bound n s (List.ofFn f).sum a b c d (List.ofFn coefficients).sum := by
  induction m with
  | zero => simp [List.ofFn_zero,Bound]
  | succ m ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.sum_cons,List.sum_cons]
    have ht:=ih (fun i=>f i.succ) (fun i=>coefficients i.succ) (fun i=>h i.succ)
    change f 0+(List.ofFn fun i=>f i.succ).sum≤
      (coefficients 0+(List.ofFn fun i=>coefficients i.succ).sum)*scale n s a b c d
    rw [Nat.add_mul]
    exact Nat.add_le_add (h 0) ht

open Lean Meta Elab Tactic

private structure Certificate where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  coefficient : Lean.Expr
  proof : Lean.Expr

private def numerical (a b c d : Nat) (proof : Lean.Expr) : MetaM Certificate := do
  let raw:=(← inferType proof).getAppArgs
  unless raw.size=8 do throwError "unexpected growth certificate {proof}"
  return ⟨a,b,c,d,raw[7]!,proof⟩

private partial def certify (n s : Lean.Expr) (value : Lean.Expr) (fuel : Nat) (forLog := false) : MetaM Certificate := do
  if fuel=0 then throwError "growth proof exhausted its unfolding limit at {value}"
  let value←instantiateMVars value
  let value:=value.headBeta
  if !(value.containsFVar n.fvarId!) && !(value.containsFVar s.fvarId!) then
    return ←numerical 0 0 0 0 (←mkAppM ``constant #[n,s,value])
  if value==n then return ←numerical 1 0 0 0 (←mkAppM ``input #[n,s])
  if value==s then return ←numerical 0 1 0 0 (←mkAppM ``width #[n,s])
  let head:=value.getAppFn.constName?
  let args:=value.getAppArgs
  if head==some ``RankIndex.width && args.size=2 then
    if (←isDefEq args[1]! n) then
      return ←numerical 0 0 0 1 (←mkAppM ``ranks #[args[0]!,n,s])
  if (head==some ``Nat.div || head==some ``HDiv.hDiv) && args.size≥2 then
    if (←isDefEq args[args.size-2]! n) && (←isDefEq args.back! s) then
      return ←numerical 0 0 1 0 (←mkAppM ``slots #[n,s])
  if head==some ``Nat.log2 && args.size=1 then
    let x:=args[0]!
    if (←isDefEq x n) then return ←numerical 0 0 0 1 (←mkAppM ``log0 #[n,s])
    let n1←mkAppM ``Nat.add #[n,mkNatLit 1]
    let n2←mkAppM ``Nat.add #[n,mkNatLit 2]
    if (←isDefEq x n1) then return ←numerical 0 0 0 1 (←mkAppM ``log1 #[n,s])
    if (←isDefEq x n2) then return ←numerical 0 0 0 1 (←mkAppM ``log2 #[n,s])
    let doubled←mkAppM ``Nat.mul #[mkNatLit 2,n2]
    if (←isDefEq x doubled) then return ←numerical 0 0 0 1 (←mkAppM ``doubledLog #[n,s])
    let poly←certify n s x (fuel-1) true
    if poly.b != 0 || poly.c != 0 then throwError "logarithm retains an unbounded width/grid at {value}"
    return ←numerical 0 0 0 1 (←mkAppM ``logarithm #[poly.proof])
  if (head==some ``Nat.min || head==some ``Min.min) && args.size≥2 then
    let chosen←certify n s (if forLog then args.back! else args[args.size-2]!) (fuel-1) forLog
    let name:=if forLog then ``minimumRight else ``minimumLeft
    let proof←mkAppOptM name #[some n,some s,some args[args.size-2]!,some args.back!,
      none,none,none,none,none,some chosen.proof]
    return ←numerical chosen.a chosen.b chosen.c chosen.d proof
  if (head==some ``Nat.add || head==some ``HAdd.hAdd || head==some ``Nat.mul || head==some ``HMul.hMul) && args.size≥2 then
    let x←certify n s args[args.size-2]! (fuel-1) forLog
    let y←certify n s args.back! (fuel-1) forLog
    if head==some ``Nat.add || head==some ``HAdd.hAdd then
      return ←numerical (max x.a y.a) (max x.b y.b) (max x.c y.c) (max x.d y.d)
        (←mkAppM ``add #[x.proof,y.proof])
    return ←numerical (x.a+y.a) (x.b+y.b) (x.c+y.c) (x.d+y.d)
      (←mkAppM ``mul #[x.proof,y.proof])
  if (head==some ``Nat.pow || head==some ``HPow.hPow) && args.size≥2 then
    let .lit (.natVal m):=(←whnf args.back!) | throwError "nonconstant growth power at {value}"
    let x←certify n s args[args.size-2]! (fuel-1) forLog
    return ←numerical (x.a*m) (x.b*m) (x.c*m) (x.d*m) (←mkAppM ``power #[x.proof,mkNatLit m])
  if head==some ``List.sum && args.size≥1 then
    let list:=args.back!
    if list.getAppFn.constName?==some ``List.ofFn then
      let f:=list.getAppArgs.back!
      let ft←whnf (←inferType f)
      if let .forallE name domain _ _:=ft then
        return ←withLocalDeclD name domain fun i=>do
          let result←certify n s (mkApp f i) (fuel-1) forLog
          let coefficients←mkLambdaFVars #[i] result.coefficient
          let proofs←mkLambdaFVars #[i] result.proof
          numerical result.a result.b result.c result.d (←mkAppM ``sum #[f,coefficients,proofs])
  if value.isLet then
    return ←certify n s (←zetaReduce value) (fuel-1) forLog
  if let some expanded←unfoldDefinition? value then
    return ←certify n s expanded (fuel-1) forLog
  let reduced←whnf value
  unless reduced==value do return ←certify n s reduced (fuel-1) forLog
  throwError "unsupported growth atom {value}"

elab "residual_growth" : tactic => withMainContext do
  let goal←getMainGoal
  let target←instantiateMVars (←goal.getType)
  unless target.getAppFn.constName?==some ``Bound do throwError "expected a Growth.Bound goal"
  let args:=target.getAppArgs
  let n:=args[0]!
  let s:=args[1]!
  let result←certify n s args[2]! 400
  if let .mvar coefficientGoal:=args[7]! then
    if result.coefficient.containsFVar n.fvarId! || result.coefficient.containsFVar s.fvarId! then
      throwError "text-dependent coefficient in growth proof"
    coefficientGoal.assign result.coefficient
  else
    unless (←isDefEq args[7]! result.coefficient) do
      throwError "coefficient mismatch; inferred {result.coefficient}"
  let mut proofs:=#[]
  for (got,want) in [(result.a,args[3]!),(result.b,args[4]!),(result.c,args[5]!),(result.d,args[6]!)] do
    let some limit←getNatValue? want | throwError "nonconstant target growth degree"
    if limit<got then throwError "growth degree {got} exceeds target {limit}"
    let mut bound←mkAppM ``Nat.le_refl #[mkNatLit got]
    for _ in [:limit-got] do
      bound←mkAppM ``Nat.le.step #[bound]
    proofs:=proofs.push bound
  let proof←mkAppM ``weaken (#[result.proof]++proofs)
  goal.assign proof
  replaceMainGoal []

end REWB.ResidualCached.Growth
