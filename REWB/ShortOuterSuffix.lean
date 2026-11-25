import REWB.OneUseRangeFarAggregateSound

/-! Actual suffix acceptance bits, sharing the proved materialized
backwards DFA pass.  Only the physical end is marked. -/
namespace REWB.ShortOuter.Suffix
open REWB.OneUseRange.FarAggregate
open REWB.Spec (slice)
variable {α : Type}

def terminalBits (n : Nat) : Array Bool := (Array.replicate n false).push true

theorem terminalBits_value (n i : Nat) : bit (terminalBits n) i=true ↔ i=n := by
  simp only [bit,terminalBits,Array.getElem?_push,Array.size_replicate]
  split
  · simp_all
  · rw [Array.getElem?_replicate]
    split <;> simp_all

def build (H : DFA α) (text : Array α) : Index×Nat :=
  let idx:=OneUseRange.FarAggregate.build H text (terminalBits text.size)
  (idx,idx.work+text.size+4)

def get (idx : Index) (p : Nat) : Bool := (query idx p).1

theorem get_correct (H : DFA α) (text : Array α) (p : Nat) (hp : p≤text.size) :
    get (build H text).1 p=true ↔ H.accepts (slice text.toList p text.size) := by
  rw [get,build,query_correct]
  simp only [terminalBits_value]
  constructor
  · rintro ⟨i,_,_,rfl,hA⟩
    exact hA
  · intro hA
    exact ⟨text.size,hp,Nat.le_refl _,rfl,hA⟩

theorem build_work (H : DFA α) (text : Array α) :
    (build H text).2≤(6*H.stateCount+11)*(text.size+1) := by
  simp only [build,OneUseRange.FarAggregate.build_work_exact,Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.mul_comm]
  omega

end REWB.ShortOuter.Suffix
