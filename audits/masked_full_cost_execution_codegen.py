#!/usr/bin/env python3
"""Inspect the actual generated full-cost execution path (Lean 4.19.0).

Run after lake build REWB.MaskedAllStartFullCostExecute.
The return-block regression pins the observed acyclic generated control
flow: every return is dominated by exactly one relevant transaction call
in an enclosing lexical block. This distinguishes exclusive ownership
branches from repeated execution. This check is scoped to the generated
functions below; it is not a compiler or general allocation theorem.
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
    ("MaskedAllStartFullCostRepair.c", PREFIX + "Repair_reset___rarg"),
    ("MaskedAllStartFullCostUpdates.c", PREFIX + "Updates_loop___rarg"),
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


def one_enclosing_call_per_return(generated: str, callee: str) -> int:
    # These generated functions have only nested if/else branches and
    # returns. Reject jumps/loops/switches before using lexical dominance.
    assert not re.search(r"\b(?:goto|while|for|switch)\s*(?:\(|[A-Za-z_])", generated)
    stack, calls, returns = [], [], []
    next_block = 0
    token = re.compile(r"[{}]|\breturn\b|\b" + re.escape(callee) + r"\(")
    for match in token.finditer(generated):
        item = match.group()
        if item == "{":
            next_block += 1
            stack.append(next_block)
        elif item == "}":
            assert stack
            stack.pop()
        elif item == "return":
            returns.append((match.start(), tuple(stack)))
        else:
            calls.append((match.start(), tuple(stack)))
    assert not stack and returns and calls
    used = set()
    for position, ancestry in returns:
        matching = [i for i, (before, blocks) in enumerate(calls)
                    if before < position and ancestry[:len(blocks)] == blocks]
        assert len(matching) == 1, (callee, position, "enclosing calls", matching)
        used.update(matching)
    assert len(used) == len(calls), (callee, "unaccounted call site")
    return len(returns)


for caller, callee in (
    ("Execution_band___rarg", PREFIX + "Repair_apply___rarg"),
    ("Execution_band___rarg", PREFIX + "Transaction_collect___rarg"),
    ("Execution_band___rarg", "l_REWB_MaskedFiniteConstruction_bankAction"),
    ("Transaction_collect___rarg", PREFIX + "Transaction_run___rarg"),
    ("Transaction_run___rarg", PREFIX + "Report_report"),
    ("Transaction_run___rarg", PREFIX + "Erase_eraseMany___rarg"),
):
    exits = one_enclosing_call_per_return(observed[PREFIX + caller], callee)
    print("ONE_CALL_PER_RETURN", caller, callee, exits, "PASS")

for suffix in ("Execution_band___rarg", "Transaction_collect___rarg",
               "Transaction_run___rarg", "Updates_write___rarg",
               "Erase_refreshCurrent___rarg", "Repair_apply___rarg",
               "Repair_reset___rarg", "Updates_loop___rarg", "Execution_plan___rarg"):
    symbol = PREFIX + suffix
    print("BEGIN_GENERATED", symbol)
    print(observed[symbol])
    print("END_GENERATED", symbol)

print("Full-cost generated path: no direct original report/collect/erase rerun: PASS")
print("Full-cost return-block transaction uniqueness: PASS")
print("Ownership: printed generated bodies remain a scoped review, not a general allocation claim.")
