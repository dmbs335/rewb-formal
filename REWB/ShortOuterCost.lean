import REWB.ShortOuterDispatch

/-! A compact n*b^2 times logarithms envelope for the concrete ledgers.
The text-dependent logarithm also contains a fixed DFA-state multiplier;
all coefficients are explicit pattern/alphabet constants. -/
namespace REWB.ShortOuter.Cost
variable {σ : Nat}

def mass (n b : Nat) : Nat := (n+1)*((b+1)*(b+1))

theorem mass_bounds (n b : Nat) :
    1≤mass n b ∧ n+1≤mass n b ∧ (n+1)*b≤mass n b ∧ (n+1)*(b*b)≤mass n b := by
  have hs : 1≤(b+1)*(b+1) := Nat.mul_le_mul (show 1≤b+1 by omega) (show 1≤b+1 by omega)
  have hb : b≤(b+1)*(b+1) := by
    have h:=Nat.mul_le_mul_left (b+1) (show 1≤b+1 by omega)
    simp only [Nat.mul_one] at h
    omega
  have hbb : b*b≤(b+1)*(b+1) := Nat.mul_le_mul (by omega) (by omega)
  have hn:=Nat.mul_le_mul_left (n+1) hs
  simp only [Nat.mul_one] at hn
  exact ⟨by change 1≤(n+1)*((b+1)*(b+1)); omega,hn,
    Nat.mul_le_mul_left (n+1) hb,Nat.mul_le_mul_left (n+1) hbb⟩

def joinConstant (k : Nat) : Nat := 10*(k+1)+Join.coefficient k*(k+8)+4

theorem join_envelope (k n e f S : Nat) (hS : 1≤S) (hn : n+1≤S) (he : e≤S) (hf : f≤S) :
    Join.ceiling k n e f≤joinConstant k*S*(n.log2+2)*(((k+1)*S).log2+1) := by
  let z:=e+k*f
  let Z:=(k+1)*S
  let H:=n.log2+2
  let J:=Z.log2+1
  have hH : 1≤H := by dsimp [H]; omega
  have hJ : 1≤J := by dsimp [J]; omega
  have hz : z≤Z := by
    have h:=Nat.add_le_add he (Nat.mul_le_mul_left k hf)
    dsimp [z,Z]
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have hl : z.log2+1≤J := Nat.add_le_add_right (CountedJoin.log2_mono hz) 1
  have hsort : 10*z*(z.log2+1)≤10*(k+1)*S*J := by
    have h:=Nat.mul_le_mul (Nat.mul_le_mul_left 10 hz) hl
    simpa only [Z,Nat.mul_assoc] using h
  have hbase : z+e+f+n+4*(n+1)≤(k+8)*S := by
    have h4:=Nat.mul_le_mul_left 4 hn
    dsimp [Z] at hz
    simp only [Nat.add_mul,Nat.one_mul] at hz ⊢
    omega
  have hcoef:=Nat.mul_le_mul_left (Join.coefficient k) hbase
  have hjcoef:=Nat.mul_le_mul_left (Join.coefficient k*((k+8)*S)) hJ
  simp only [Nat.mul_one] at hjcoef
  have hbody : 10*z*(z.log2+1)+Join.coefficient k*(z+e+f+n+4*(n+1))≤
      (10*(k+1)+Join.coefficient k*(k+8))*S*J := by
    have hsum:=Nat.add_le_add hsort (Nat.le_trans hcoef hjcoef)
    simpa only [Nat.add_mul,Nat.mul_assoc] using hsum
  have hscaled:=Nat.mul_le_mul_left H hbody
  have hsH : S≤S*H := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left S hH
  have hHs : H≤S*H := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right H hS
  have hsJ : S*H≤S*H*J := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (S*H) hJ
  have hover : n+n.log2+4≤4*(S*H*J) := by
    have h2 : 2≤H := by dsimp [H]; omega
    have hpos : 1≤S*H*J := by omega
    have hlog : n.log2+2≤S*H*J := Nat.le_trans hHs hsJ
    omega
  have hall:=Nat.add_le_add hscaled hover
  have hleft : H*(10*z*(z.log2+1)+Join.coefficient k*(z+e+f+n+4*(n+1)))+
      (n+n.log2+4)=Join.ceiling k n e f := by
    simp only [Join.ceiling,z,H,Nat.add_assoc]
  rw [hleft] at hall
  have hright : H*((10*(k+1)+Join.coefficient k*(k+8))*S*J)+4*(S*H*J)=
      joinConstant k*S*H*J := by
    let C:=10*(k+1)+Join.coefficient k*(k+8)
    calc
      H*(C*S*J)+4*(S*H*J)=C*S*H*J+4*S*H*J := by
        congr 1 <;> simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      _=(C+4)*S*H*J := by simp only [Nat.add_mul]
      _=joinConstant k*S*H*J := rfl
  rw [hright] at hall
  exact hall

def preparationConstant (P : SevenDFA (Fin σ)) : Nat :=
  10*σ+100*P.G.stateCount+100*P.H.stateCount+100*P.F.stateCount+1000

theorem prepare_envelope (P : SevenDFA (Fin σ)) (n L : Nat) :
    prepareBudget P n L≤preparationConstant P*mass n (min L (n+1))*(n.log2+2) := by
  simp only [prepareBudget,Band.budget,Band.stageBudget,Keys.stepBudget,Sweep.stepBudget,
    preparationConstant,mass]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc,
    Nat.mul_comm,Nat.mul_left_comm]
  simp only [Nat.reduceMul,←Nat.mul_assoc]
  omega

theorem p1_event_envelope (n b : Nat) :
    P1.sourceBudget n b+P1.targetBudget n b+n+5≤110*mass n b := by
  simp only [P1.sourceBudget,P1.targetBudget,mass,Nat.mul_add,Nat.add_mul,
    Nat.mul_one,Nat.one_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  simp only [Nat.reduceMul,←Nat.mul_assoc]
  omega

theorem p2_event_envelope (b : Nat) :
    P2.sourceBudget b+P2.targetBudget b+3*b+13≤110*((b+1)*(b+1)) := by
  simp only [P2.sourceBudget,P2.targetBudget,Nat.mul_add,Nat.add_mul,
    Nat.mul_one,Nat.one_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  simp only [Nat.reduceMul,←Nat.mul_assoc]
  omega

theorem lift_scale (c S h H J : Nat) (hh : h≤H) (hJ : 1≤J) :
    c*S*h≤c*S*H*J := by
  have h1:=Nat.mul_le_mul_left (c*S) hh
  have h2:=Nat.mul_le_mul_left (c*S*H) hJ
  simp only [Nat.mul_one] at h2
  exact Nat.le_trans h1 h2

def envelope (P : SevenDFA (Fin σ)) (k n L : Nat) : Nat :=
  let S:=mass n (min L (n+1))
  (preparationConstant P+joinConstant k+200)*S*((n+1).log2+2)*(((k+1)*S).log2+1)

theorem p1_budget (P : SevenDFA (Fin σ)) (n L : Nat) :
    P1.budget P n L≤envelope P P.C.stateCount n L := by
  let b:=min L (n+1)
  let S:=mass n b
  let H:=(n+1).log2+2
  let J:=((P.C.stateCount+1)*S).log2+1
  have hm:=mass_bounds n b
  have hH : 1≤H := by dsimp [H]; omega
  have hJ : 1≤J := by dsimp [J]; omega
  have hheight : n.log2+2≤H := Nat.add_le_add_right (CountedJoin.log2_mono (by omega)) 2
  have hp:=Nat.le_trans (prepare_envelope P n L)
    (lift_scale (preparationConstant P) S (n.log2+2) H J hheight hJ)
  have hj:=join_envelope P.C.stateCount n ((n+1)*b) ((n+1)*(b*b)) S
    hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  have hj':=Nat.le_trans hj (Nat.mul_le_mul_right J
    (Nat.mul_le_mul_left (joinConstant P.C.stateCount*S) hheight))
  have he0:=p1_event_envelope n b
  have he : P1.sourceBudget n b+P1.targetBudget n b+n+5≤110*S*H*J :=
    Nat.le_trans he0 (by simpa only [Nat.mul_one] using lift_scale 110 S 1 H J hH hJ)
  have hsum:=Nat.add_le_add (Nat.add_le_add hp hj') he
  have hcoef : (preparationConstant P+joinConstant P.C.stateCount+110)*S*H*J≤
      (preparationConstant P+joinConstant P.C.stateCount+200)*S*H*J :=
    Nat.mul_le_mul_right J (Nat.mul_le_mul_right H (Nat.mul_le_mul_right S (by omega)))
  have hr : preparationConstant P*S*H*J+joinConstant P.C.stateCount*S*H*J+110*S*H*J=
      (preparationConstant P+joinConstant P.C.stateCount+110)*S*H*J := by
    simp only [Nat.add_mul]
  rw [hr] at hsum
  have hfinal:=Nat.le_trans hsum hcoef
  change prepareBudget P n L+P1.sourceBudget n b+P1.targetBudget n b+
    Join.ceiling P.C.stateCount n ((n+1)*b) ((n+1)*(b*b))+n+5≤_
  change _≤(preparationConstant P+joinConstant P.C.stateCount+200)*S*H*J
  omega

theorem p2_budget (P : SevenDFA (Fin σ)) (n L : Nat) :
    P2.budget P n L≤envelope P P.D.stateCount n L := by
  let b:=min L (n+1)
  let U:=(b+1)*(b+1)
  let S:=mass n b
  let H:=(n+1).log2+2
  let J:=((P.D.stateCount+1)*S).log2+1
  have hm:=mass_bounds n b
  have hu:=mass_bounds 0 b
  simp only [mass,Nat.zero_add,Nat.one_mul] at hu
  have hU : U≤S := by
    have h:=Nat.mul_le_mul_right U (show 1≤n+1 by omega)
    simpa only [Nat.one_mul] using h
  have hH : 1≤H := by dsimp [H]; omega
  have hJ : 1≤J := by dsimp [J]; omega
  have hheight : n.log2+2≤H := Nat.add_le_add_right (CountedJoin.log2_mono (by omega)) 2
  have hbheight : b.log2+2≤H := Nat.add_le_add_right
    (CountedJoin.log2_mono (Nat.min_le_right L (n+1))) 2
  have hp:=Nat.le_trans (prepare_envelope P n L)
    (lift_scale (preparationConstant P) S (n.log2+2) H J hheight hJ)
  have hbU : b+1≤U := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (b+1) (show 1≤b+1 by omega)
  have hj:=join_envelope P.D.stateCount b (b*b) (b*b) U hu.1 hbU hu.2.2.2 hu.2.2.2
  have hlog : ((P.D.stateCount+1)*U).log2+1≤J := Nat.add_le_add_right
    (CountedJoin.log2_mono (Nat.mul_le_mul_left (P.D.stateCount+1) hU)) 1
  have hjlocal:=Nat.le_trans hj (Nat.mul_le_mul
    (Nat.mul_le_mul_left (joinConstant P.D.stateCount*U) hbheight) hlog)
  have hjbig0:=Nat.mul_le_mul_left (n+1) hjlocal
  have hjbig : (n+1)*Join.ceiling P.D.stateCount b (b*b) (b*b)≤joinConstant P.D.stateCount*S*H*J := by
    simpa only [S,mass,U,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hjbig0
  have he0:=Nat.mul_le_mul_left (n+1) (p2_event_envelope b)
  have he1 : (n+1)*(P2.sourceBudget b+P2.targetBudget b+3*b+13)+7≤117*S := by
    have hh : (n+1)*(110*((b+1)*(b+1)))=110*S := by
      simp only [S,mass,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [hh] at he0
    have h7:=Nat.mul_le_mul_left 7 hm.1
    simp only [Nat.mul_one] at h7
    omega
  have he:=Nat.le_trans he1 (by simpa only [Nat.mul_one] using lift_scale 117 S 1 H J hH hJ)
  have hsum:=Nat.add_le_add (Nat.add_le_add hp hjbig) he
  have hcoef : (preparationConstant P+joinConstant P.D.stateCount+117)*S*H*J≤
      (preparationConstant P+joinConstant P.D.stateCount+200)*S*H*J :=
    Nat.mul_le_mul_right J (Nat.mul_le_mul_right H (Nat.mul_le_mul_right S (by omega)))
  have hr : preparationConstant P*S*H*J+joinConstant P.D.stateCount*S*H*J+117*S*H*J=
      (preparationConstant P+joinConstant P.D.stateCount+117)*S*H*J := by
    simp only [Nat.add_mul]
  rw [hr] at hsum
  have hfinal:=Nat.le_trans hsum hcoef
  change prepareBudget P n L+(n+1)*(P2.blockBudget P b+5)+7≤_
  change _≤(preparationConstant P+joinConstant P.D.stateCount+200)*S*H*J
  simp only [P2.blockBudget,Nat.mul_add,Nat.mul_one] at hfinal ⊢
  omega

theorem p1_work (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (L : Nat) :
    (P1.solve P text fallback L).work≤envelope P P.C.stateCount text.size L :=
  Nat.le_trans (P1.solve_work P text fallback L) (p1_budget P text.size L)

theorem p2_work (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (L : Nat) :
    (P2.solve P text fallback L).work≤envelope P P.D.stateCount text.size L :=
  Nat.le_trans (P2.solve_work P text fallback L) (p2_budget P text.size L)

end REWB.ShortOuter.Cost
