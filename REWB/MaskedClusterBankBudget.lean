import REWB.MaskedClusterBankCorrect

/-! Actual bank preparation counters. Pattern catalog and action-table
    construction, finite-orbit/formula construction, shared text indices,
    immutable-mask arrays, and global repair/deletion scheduling retain
    their explicitly separate accounting obligations.
-/
namespace REWB.MaskedCluster
variable {α : Type}

def denseBankBudget (C E : DFA α) (K : Nat) : Nat :=
  (2*ReplayMaps.count C.stateCount E.stateCount)*
    (C.stateCount+E.stateCount+
      4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(rowBudget C E K+1)))+
      (2*(1+C.stateCount+E.stateCount))*((2*(1+C.stateCount+E.stateCount))*11)+7)

def pointBankBudget (C E : DFA α) : Nat :=
  (2*ReplayMaps.count C.stateCount E.stateCount)*
    (C.stateCount+E.stateCount+4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*21))+
      (2*(1+C.stateCount+E.stateCount))*((2*(1+C.stateCount+E.stateCount))*11)+7)

theorem compileDenseBank_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (s q m L H next incoming : Nat) (enabled : Bool) (source target : Array Bool)
    (sourceCounts targetCounts : Array Nat) (base : Nat) (window : SourceWindow)
    (hq : q≤H) (hm : 0<m) (hLH : L≤H) (hpen : s+(m-1)*q+H≤next)
    (hsep : s+m*q<next) (hnext : next≤w.length) (hbound : s+m*q+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) :
    (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m L H next incoming enabled source target sourceCounts targetCounts base window).2≤
        2*denseRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
          denseBankBudget C E prepared.K+3 := by
  have a:=prepareRows_work C E w s q m H next incoming enabled hq hm hpen hsep hnext hbound hin
  have b:=(replay_bounds C E w s L H hLH (by omega)).2.2
  have c:=denseBank_work C E book prepared
    (prepareRows C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m H next incoming enabled).1
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) s L H).maps
    source target sourceCounts targetCounts base window
  simp only [compileDenseBank,denseBankBudget]
  omega

theorem compilePointBank_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount) (w : Word α)
    (s L H next incoming : Nat) (enabled : Bool) (source target : Array Bool) (window : SourceWindow)
    (hLH : L≤H) (hsep : s<next) (hnext : next≤w.length) (hbound : s+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s L H next incoming enabled source target window).2≤
        2*pointRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
          pointBankBudget C E+3 := by
  have a:=preparePointRows_work C E w s H next incoming enabled hsep hnext hbound hin
  have b:=(replay_bounds C E w s L H hLH hbound).2.2
  have c:=pointBank_work C E book
    (preparePointRows C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s H next incoming enabled).1
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) s L H).maps
    source target window
  simp only [compilePointBank,pointBankBudget]
  omega

end REWB.MaskedCluster
