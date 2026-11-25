import REWB.OneUseRangeFarAggregateSound

/-! Kernel-evaluated regressions for the materialized endpoint aggregate.
The reset transition is noninjective for both letters. -/
namespace REWB.OneUseRange.FarAggregate.Regression

def any : DFA Bool := ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>true⟩
def lastTrue : DFA Bool :=
  ⟨2,⟨0,by decide⟩,fun _ c=>if c then ⟨1,by decide⟩ else ⟨0,by decide⟩,
    fun q=>decide (q.val=1)⟩

theorem empty_accepts : (query (build any #[] #[true]) 0).1=true := by decide
theorem empty_rejects : (query (build lastTrue #[] #[true]) 0).1=false := by decide
theorem empty_mask : (query (build any #[] #[]) 0).1=false := by decide
theorem endpoint_epsilon : (query (build any #[false,true] #[false,false,true]) 2).1=true := by decide
theorem endpoint_rejects :
    (query (build lastTrue #[false,true] #[false,false,true]) 2).1=false := by decide
theorem past_endpoint : (query (build any #[true] #[true,true,true]) 2).1=false := by decide
theorem short_row : (query (build any #[false,true,false] #[true]) 1).1=false := by decide

theorem noninjective_rows :
    (build lastTrue #[false,true,false] #[false,false,true,false]).answers =
      #[false,false,true,true] := by decide

theorem prefix_coordinates :
    (query (build lastTrue ([false,true,false,true].take 2).toArray #[false,false,true]) 0).1=true := by
  decide

theorem exact_counter :
    (build lastTrue #[false,true,false] #[false,false,true,false]).work=67 := by decide

theorem query_counter :
    (query (build lastTrue #[false,true,false] #[false,false,true,false]) 1).2=4 := by decide

theorem zero_semantics (A : DFA α) (bits : Array Bool) :
    (query (build A (#[] : Array α) bits) 0).1=(bit bits 0 && A.final A.initial) :=
  query_empty A bits

end REWB.OneUseRange.FarAggregate.Regression
