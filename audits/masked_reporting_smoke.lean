import REWB.MeasuredMaskQuery

/-! Executable smoke for the measured scan query and reporting traversal.
    Run after `lake build REWB.MeasuredMaskQuery` with:
    `lake env lean --run audits/masked_reporting_smoke.lean`. -/

def main : IO Unit := do
  let result := REWB.MeasuredMaskQuery.SharedTargetRegression.result
  IO.println s!"shared target: starts={result.starts}, count={result.count}, calls={result.calls}, queryWork={result.queryWork}, copies={result.copies}, total={REWB.MaskedReporting.totalWork result}"
  let empty := REWB.MeasuredMaskQuery.all #[]
  IO.println s!"empty mask: starts={empty.starts}, calls={empty.calls}, queryWork={empty.queryWork}, copies={empty.copies}, total={REWB.MaskedReporting.totalWork empty}"

#print axioms REWB.MaskedReporting.report_correct
#print axioms REWB.MaskedReporting.report_calls
#print axioms REWB.MaskedReporting.report_totalWork
#print axioms REWB.MaskedReporting.reportMasked_exhausts
#print axioms REWB.MeasuredMaskQuery.query_correct
#print axioms REWB.MeasuredMaskQuery.all_totalWork
#print axioms REWB.MeasuredMaskQuery.SharedTargetRegression.query_spec
#print axioms REWB.MeasuredMaskQuery.SharedTargetRegression.execution
