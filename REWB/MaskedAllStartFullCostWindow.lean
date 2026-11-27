import REWB.MaskedAllStartFullCostQuery
import REWB.MaskedAllStartFullCostClip
import REWB.MaskedTraversalAggregateReporting

/-! Measured query composition on the actual persistent aggregate. The
existing counted matrix region/closing scans are reused, while bank
clipping and the shared joint-cut query execute their full construction
counterparts. Both the original WindowResult and its old ledger survive
exactly, so the established query semantics and global amortization apply.
-/
namespace REWB.MaskedAllStart.FullCost.Query
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {α : Type} {C E : DFA α} {h : Nat}

def bandUnits (out : BandResult) : Nat :=
  out.aggregateWork+out.closureProbes+out.cutProducts+out.cutVisits+out.cutProbes+out.arithmetic

def band (B C E : DFA α) (idx : Cut.Shared B C E) (tree : BankTree C E h)
    (sourceLo sourceHi representative lengthLo lengthHi old : Nat) : Bank.Result BandResult :=
  let ⟨product,productWork⟩:=region tree sourceLo sourceHi
  let ⟨finalBank,closureWork⟩:=close C E product
  let ⟨out,cutWork⟩:=cut B C E idx finalBank representative lengthLo lengthHi old 0 0
  (⟨out.answer,productWork,closureWork,out.products,out.visits,out.tupleProbes,out.arithmetic+3⟩,
    productWork+closureWork+cutWork+3)

theorem band_value (B C E : DFA α) (idx : Cut.Shared B C E) (tree : BankTree C E h)
    (sourceLo sourceHi representative lengthLo lengthHi old : Nat) :
    (band B C E idx tree sourceLo sourceHi representative lengthLo lengthHi old).1=
      queryBand B C E idx tree sourceLo sourceHi representative lengthLo lengthHi old := by
  simp only [band,queryBand,cut_value]

theorem band_work (B C E : DFA α) (idx : Cut.Shared B C E) (tree : BankTree C E h)
    (sourceLo sourceHi representative lengthLo lengthHi old : Nat)
    (ht : PeriodicConstruction.Cut.Tiny idx.tree) :
    (band B C E idx tree sourceLo sourceHi representative lengthLo lengthHi old).2≤
      cutCoefficient B.stateCount C.stateCount E.stateCount*
        bandUnits (band B C E idx tree sourceLo sourceHi representative lengthLo lengthHi old).1 := by
  have hcut:=cut_work B C E idx (close C E (region tree sourceLo sourceHi).1).1
    representative lengthLo lengthHi old 0 0 ht
  have hs:=Nat.mul_le_mul_right ((region tree sourceLo sourceHi).2+
      (close C E (region tree sourceLo sourceHi).1).2+3)
    (cutCoefficient_pos B.stateCount C.stateCount E.stateCount)
  simp only [band,bandUnits,cutUnits,Nat.mul_add,Nat.one_mul] at hcut hs ⊢
  omega

def window (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h)
    (capacity : Nat) (tree : BankTree C E h)
    (lo hi representative lengthLo lengthHi old : Nat) : Bank.Result WindowResult :=
  let ⟨clipped,clipWork⟩:=Clipping.window env st partition capacity old lo hi tree
  if clipped.update.ready then
    let ⟨out,bandWork⟩:=band B C E idx clipped.update.tree clipped.lower hi representative lengthLo lengthHi old
    (⟨out,clipped.work+2,clipped.update.calls,1⟩,clipWork+bandWork+2)
  else (⟨rejectedBand,clipped.work+2,clipped.update.calls,0⟩,clipWork+2)

theorem window_value (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h)
    (capacity : Nat) (tree : BankTree C E h) (lo hi representative lengthLo lengthHi old : Nat) :
    (window B C E idx env st partition capacity tree lo hi representative lengthLo lengthHi old).1=
      queryWindow B C E idx env st partition capacity tree lo hi representative lengthLo lengthHi old := by
  simp only [window,queryWindow,Clipping.window_value,band_value]
  split <;> rfl

def coefficient (B C E : DFA α) (K : Nat) : Nat :=
  cutCoefficient B.stateCount C.stateCount E.stateCount+2*Bank.extra C E K+1

theorem coefficient_pos (B C E : DFA α) (K : Nat) : 1≤coefficient B C E K := by
  unfold coefficient
  omega

theorem window_work (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h)
    (capacity : Nat) (tree : BankTree C E h) (lo hi representative lengthLo lengthHi old : Nat)
    (ht : PeriodicConstruction.Cut.Tiny idx.tree) :
    (window B C E idx env st partition capacity tree lo hi representative lengthLo lengthHi old).2≤
      coefficient B C E env.prepared.K*
        Reporting.queryUnits (window B C E idx env st partition capacity tree lo hi representative lengthLo lengthHi old).1 := by
  have hclip:=Clipping.window_extra env st partition capacity old lo hi tree
  have hc:=Nat.mul_le_mul_right (Clipping.window env st partition capacity old lo hi tree).1.work
    (coefficient_pos B C E env.prepared.K)
  have hconst : 2*Bank.extra C E env.prepared.K+2≤coefficient B C E env.prepared.K*2 := by
    unfold coefficient
    omega
  have hband:=band_work B C E idx (Clipping.window env st partition capacity old lo hi tree).1.update.tree
    (Clipping.window env st partition capacity old lo hi tree).1.lower hi representative lengthLo lengthHi old ht
  have hb:=Nat.mul_le_mul_right
    (bandUnits (band B C E idx (Clipping.window env st partition capacity old lo hi tree).1.update.tree
      (Clipping.window env st partition capacity old lo hi tree).1.lower hi representative lengthLo lengthHi old).1)
    (show cutCoefficient B.stateCount C.stateCount E.stateCount≤coefficient B C E env.prepared.K by
      unfold coefficient; omega)
  simp only [window]
  split
  · simp only [Reporting.queryUnits,bandUnits,Nat.mul_add,Nat.one_mul] at hband hb hc ⊢
    omega
  · simp only [Reporting.queryUnits,rejectedBand,Nat.add_zero,Nat.mul_add,Nat.one_mul] at hc ⊢
    omega

def ask (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) : Nat→Nat→Bank.Result (Bool×Nat) :=
  fun lo hi=>
    let ⟨out,work⟩:=window B C E idx env st partition capacity tree lo hi base lengthLo lengthHi old
    ((out.band.answer,Reporting.queryUnits out),work)

theorem ask_value (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old lo hi : Nat) :
    (ask B C E idx env st partition capacity tree base lengthLo lengthHi old lo hi).1=
      Reporting.ask B C E idx env st partition capacity tree base lengthLo lengthHi old lo hi := by
  simp only [ask,Reporting.ask,window_value]

theorem ask_work (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old lo hi : Nat)
    (ht : PeriodicConstruction.Cut.Tiny idx.tree) :
    (ask B C E idx env st partition capacity tree base lengthLo lengthHi old lo hi).2≤
      coefficient B C E env.prepared.K*
        (ask B C E idx env st partition capacity tree base lengthLo lengthHi old lo hi).1.2 :=
  window_work B C E idx env st partition capacity tree lo hi base lengthLo lengthHi old ht

end REWB.MaskedAllStart.FullCost.Query
