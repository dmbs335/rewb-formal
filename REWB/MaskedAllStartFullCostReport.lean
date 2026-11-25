import REWB.MaskedAllStartFullCostBank
import REWB.MaskedReporting

/-! A cost-bearing execution of the exact interval reporter. One query
returns its original answer/counter together with its expanded primitive
work; both are read from that one returned value. Negative visits and
list concatenation are retained in the constructed ledger. The generic
query lemmas are for subsequent concrete window-query instantiation.
-/
namespace REWB.MaskedAllStart.FullCost.Report

abbrev Query := Nat→Nat→Bank.Result (Bool×Nat)

def report (ask : Query) : Nat→Nat→Bank.Result MaskedReporting.Result
  | 0,lo=>
    let ⟨⟨hit,oldWork⟩,queryWork⟩:=ask lo (lo+1)
    if hit then (⟨[lo],1,1,oldWork,0⟩,queryWork+20)
    else (⟨[],0,1,oldWork,0⟩,queryWork+20)
  | h+1,lo=>
    let ⟨⟨hit,oldWork⟩,queryWork⟩:=ask lo (lo+2^(h+1))
    if hit then
      let ⟨a,aWork⟩:=report ask h lo
      let ⟨b,bWork⟩:=report ask h (lo+2^h)
      (⟨a.starts++b.starts,a.count+b.count,1+a.calls+b.calls,
          oldWork+a.queryWork+b.queryWork,a.copies+b.copies+a.count⟩,
        queryWork+aWork+bWork+a.count+20)
    else (⟨[],0,1,oldWork,0⟩,queryWork+20)

theorem report_value (ask : Query) (h lo : Nat) :
    (report ask h lo).1=MaskedReporting.report (fun l r=>(ask l r).1) h lo := by
  induction h generalizing lo with
  | zero=>simp only [report,MaskedReporting.report]; split <;> rfl
  | succ h ih=>
    simp only [report,MaskedReporting.report,ih]
    split <;> rfl

def oldUnits (r : MaskedReporting.Result) : Nat := r.queryWork+r.copies+20*r.calls

theorem report_work (ask : Query) (coefficient : Nat) (hc : 1≤coefficient)
    (hq : ∀l r,(ask l r).2≤coefficient*(ask l r).1.2) (h lo : Nat) :
    (report ask h lo).2≤coefficient*oldUnits (report ask h lo).1 := by
  rw [report_value]
  induction h generalizing lo with
  | zero=>
    have hh:=hq lo (lo+1)
    have hs:=Nat.mul_le_mul_left 20 hc
    simp only [report,MaskedReporting.report,oldUnits,Nat.mul_one,Nat.add_zero,Nat.mul_add] at hs ⊢
    split <;> dsimp only <;> omega
  | succ h ih=>
    have hh:=hq lo (lo+2^(h+1))
    have ha:=ih lo
    have hb:=ih (lo+2^h)
    have hs:=Nat.mul_le_mul_right
      ((MaskedReporting.report (fun l r=>(ask l r).1) h lo).count+20) hc
    simp only [report,MaskedReporting.report]
    split
    · simp only [report_value,oldUnits,Nat.mul_add,Nat.mul_one,Nat.one_mul] at ha hb hs ⊢
      omega
    · have hz:=Nat.mul_le_mul_left 20 hc
      simp only [oldUnits,Nat.mul_one,Nat.add_zero,Nat.mul_add] at hz ⊢
      omega

end REWB.MaskedAllStart.FullCost.Report
