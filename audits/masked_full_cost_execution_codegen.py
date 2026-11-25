#!/usr/bin/env python3
"""Inspect the actual generated full-cost execution path (Lean 4.19.0).

Run after lake build REWB.MaskedAllStartFullCostExecute.
This first diagnostic checks that full-cost execution does not directly
rerun the original report/collect/erase transactions. It prints exact
call sites and selected complete bodies so ownership branches can be
reviewed before pinning per-path call counts. A syntactic call-site count
alone is deliberately not described as a per-path uniqueness proof.
"""
from pathlib import Path
from collections import Counter
import re

ROOT = Path(__file__).resolve().parents[1]
IR = ROOT / ".lake/build/ir/REWB"


def body(filename: str, symbol: str) -> str:
    code = (IR / filename).read_text()
    found = re.search(r"^LEAN_EXPORT lean_object\* " + re.escape(symbol)
                      + r"\([^;]*\) \{", code, re.MULTILINE)
    assert found, f"missing generated function {symbol} in {filename}"
    start = code.index("{", found.start())
    depth = 0
    for pos in range(start, len(code)):
        depth += (code[pos] == "{") - (code[pos] == "}")
        if depth == 0:
            return code[start:pos + 1]
    raise AssertionError(f"unclosed generated function {symbol}")


PREFIX = "l_REWB_MaskedAllStart_FullCost_"
targets = [
    ("MaskedAllStartFullCostExecuteBand.c", PREFIX + "Execution_band___rarg"),
    ("MaskedAllStartFullCostCollect.c", PREFIX + "Transaction_collect___rarg"),
    ("MaskedAllStartFullCostCollect.c", PREFIX + "Transaction_run___rarg"),
    ("MaskedAllStartFullCostExecute.c", PREFIX + "Execution_bandsLoop___rarg"),
    ("MaskedAllStartFullCostExecute.c", PREFIX + "Execution_edge___rarg"),
    ("MaskedAllStartFullCostExecute.c", PREFIX + "Execution_plan___rarg"),
    ("MaskedAllStartFullCostRepair.c", PREFIX + "Repair_apply___rarg"),
    ("MaskedAllStartFullCostUpdates.c", PREFIX + "Updates_write___rarg"),
    ("MaskedAllStartFullCostErase.c", PREFIX + "Erase_refreshCurrent___rarg"),
]
observed = {}
for filename, symbol in targets:
    generated = body(filename, symbol)
    observed[symbol] = generated
    calls = Counter(re.findall(r"\b(l_REWB_[A-Za-z0-9_]+)\(", generated))
    relevant = {name: count for name, count in sorted(calls.items())
                if ("FullCost" in name or "Reporting" in name or "Collect" in name
                    or "Erase" in name or "bankAction" in name)}
    print("CALLS", symbol, relevant)
    print("OWNERSHIP", symbol, {
        key: generated.count(key + "(")
        for key in ("lean_is_exclusive", "lean_inc", "lean_dec",
                    "lean_array_fset", "lean_array_set")
    })

for suffix in ("Execution_band___rarg", "Transaction_collect___rarg",
               "Transaction_run___rarg"):
    generated = observed[PREFIX + suffix]
    for forbidden in (
        "l_REWB_MaskedTraversalAggregate_Reporting_run",
        "l_REWB_MaskedTraversalAggregate_Collect_run",
        "l_REWB_MaskedTraversalAggregate_eraseMany",
    ):
        assert forbidden not in generated, (suffix, "original transaction call", forbidden)

for suffix in ("Execution_band___rarg", "Transaction_collect___rarg",
               "Transaction_run___rarg", "Updates_write___rarg",
               "Erase_refreshCurrent___rarg"):
    symbol = PREFIX + suffix
    print("BEGIN_GENERATED", symbol)
    print(observed[symbol])
    print("END_GENERATED", symbol)

print("Full-cost generated path: no direct original report/collect/erase rerun: PASS")
print("Per-path transaction uniqueness and ownership: review printed bodies; no general allocation claim.")
