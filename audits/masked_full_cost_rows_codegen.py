#!/usr/bin/env python3
"""Inspect generated full-construction row factories (Lean 4.19.0).

Run after lake build REWB.MaskedAllStartFullCostRowsRegression.
No old solver/row/input factory may occur in these new executable
modules. Entry bodies expose the single retained-factory path separately
from proof-only value comparisons and coefficient choices.
"""
from collections import Counter
from pathlib import Path
import re

IR = Path(__file__).resolve().parents[1] / ".lake/build/ir/REWB"


def read_body(code, symbol):
    match = re.search(r"^LEAN_EXPORT lean_object\* " + re.escape(symbol)
                      + r"\([^;]*\) \{", code, re.MULTILINE)
    assert match, symbol
    start = code.index("{", match.start())
    depth = 0
    for end in range(start, len(code)):
        depth += (code[end] == "{") - (code[end] == "}")
        if depth == 0:
            return code[start:end + 1]
    raise AssertionError(symbol)


def entry(code, stem):
    candidates = re.findall(r"^LEAN_EXPORT lean_object\* (" + re.escape(stem)
                            + r"(?:___rarg)?)\([^;]*\) \{", code, re.MULTILINE)
    assert candidates, stem
    return max(candidates, key=len)


targets = [
    ("MaskedAllStartFullCostTable.c", "l_REWB_MaskedAllStart_FullCost_Table_build"),
    ("MaskedAllStartFullCostRows.c", "l_REWB_MaskedAllStart_FullCost_Rows_row"),
    ("MaskedAllStartFullCostRows.c", "l_REWB_MaskedAllStart_FullCost_Rows_prefixRows"),
    ("MaskedAllStartFullCostRows.c", "l_REWB_MaskedAllStart_FullCost_Rows_far"),
    ("MaskedAllStartFullCostRows.c", "l_REWB_MaskedAllStart_FullCost_Rows_forward"),
    ("MaskedAllStartFullCostRows.c", "l_REWB_MaskedAllStart_FullCost_Rows_backward"),
    ("MaskedAllStartFullCostRows.c", "l_REWB_MaskedAllStart_FullCost_Rows_boundary"),
    ("ResidualActualFullCostInputs.c", "l_REWB_ResidualActual_FullCost_P1_inputs"),
    ("ResidualActualFullCostInputs.c", "l_REWB_ResidualActual_FullCost_P2_forwardRows"),
    ("ResidualActualFullCostInputs.c", "l_REWB_ResidualActual_FullCost_P2_backwardRows"),
    ("ResidualActualFullCostInputs.c", "l_REWB_ResidualActual_FullCost_P2_inputs"),
]
codes = {filename: (IR / filename).read_text() for filename, _ in targets}
for filename, code in codes.items():
    for forbidden in (
        r"\bl_REWB_MaskedAllStart_solve(?:___[A-Za-z0-9_]+)?\(",
        r"\bl_REWB_MaskedAllStart_Rows_(?:row|prefixRows|far|forward|backward|boundary)(?:___[A-Za-z0-9_]+)?\(",
        r"\bl_REWB_ResidualActual_P[12]_(?:inputs|forwardRows|backwardRows)(?:___[A-Za-z0-9_]+)?\(",
    ):
        assert not re.search(forbidden, code), (filename, forbidden)

for filename, stem in targets:
    code = codes[filename]
    symbol = entry(code, stem)
    generated = read_body(code, symbol)
    calls = Counter(re.findall(r"\b(l_REWB_[A-Za-z0-9_]+)\(", generated))
    print("ROW_FACTORY_CALLS", symbol, dict(sorted(calls.items())))
    if stem.endswith("_row") or stem.endswith("_Table_build") or stem.endswith("_P2_inputs"):
        print("BEGIN_ROW_GENERATED", symbol)
        print(generated)
        print("END_ROW_GENERATED", symbol)

print("Full-cost rows: no direct old solver or row/input factory calls: PASS")
