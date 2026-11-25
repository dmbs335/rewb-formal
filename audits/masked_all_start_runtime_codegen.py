#!/usr/bin/env python3
"""Check the pinned Lean compiler's concrete public execution routing.

Run after `lake build REWB.MaskedAllStart`.  This is a generated-code
regression check, separate from the kernel equality proofs.  It rules
out the observed second Reporting.run call in Execute.band; it is not
a general proof of the compiler's allocation or ownership semantics.
"""
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
IR = ROOT / ".lake/build/ir/REWB"


def body(path: str, symbol: str) -> str:
    code = (IR / path).read_text()
    found = re.search(r"^LEAN_EXPORT lean_object\* " + re.escape(symbol)
                      + r"\([^;]*\) \{", code, re.MULTILINE)
    assert found, f"missing generated function {symbol}"
    start = code.index("{", found.start())
    depth = 0
    for pos in range(start, len(code)):
        depth += (code[pos] == "{") - (code[pos] == "}")
        if depth == 0:
            return code[start:pos + 1]
    raise AssertionError(f"unclosed generated function {symbol}")


runtime = "l_REWB_MaskedTraversalExecute_Runtime_"
old = "l_REWB_MaskedTraversalExecute_"
band = body("MaskedTraversalExecuteRuntime.c", runtime + "band___rarg")
assert "l_REWB_MaskedTraversalAggregate_Reporting_run" not in band
# The two calls are in the mutually exclusive owned/shared branches of
# the repair-result record. Neither branch retains the input store for
# a second transaction. Exact call count is pinned to Lean 4.19.0.
assert band.count("l_REWB_MaskedTraversalAggregate_Collect_run___rarg(") == 2

bands = body("MaskedTraversalExecuteRuntime.c", runtime + "bands___rarg")
assert bands.count(runtime + "band___rarg(") == 1
assert old + "band___rarg(" not in bands
edge = body("MaskedTraversalExecuteRuntime.c", runtime + "edge___rarg")
assert edge.count(runtime + "bands___rarg(") == 1
plan = body("MaskedTraversalExecuteRuntime.c", runtime + "plan___rarg")
assert plan.count(runtime + "plan___rarg(") == 2
assert old + "plan___rarg(" not in plan
public = (IR / "MaskedAllStart.c").read_text()
assert re.search(r"= " + runtime + r"plan___rarg\(", public)
assert not re.search(r"= " + old + r"plan___rarg\(", public)

print("public solve → Runtime.plan → Runtime.edge → Runtime.bands → Runtime.band: PASS")
print("Runtime.band: one Collect transaction per ownership branch; no direct Reporting rerun: PASS")
