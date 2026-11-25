#!/usr/bin/env python3
"""Check the full selected theorem inventory against Lean's actual output."""
from collections import Counter
from pathlib import Path
import re
import sys

if len(sys.argv) != 3:
    raise SystemExit("usage: check-principal-axioms.py SOURCE.lean OUTPUT.log")
source = Path(sys.argv[1]).read_text(encoding="utf-8")
output = Path(sys.argv[2]).read_text(encoding="utf-8")
expected = re.findall(r"^#print axioms\s+(\S+)", source, flags=re.MULTILINE)
reports = re.findall(
    r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    output,
    flags=re.DOTALL,
)
if not expected:
    raise SystemExit("No principal theorem inventory was found.")
if len(set(expected)) != len(expected):
    raise SystemExit("The principal theorem inventory has duplicate entries.")
observed = Counter(name for name, _ in reports)
missing = sorted(set(expected) - set(observed))
extra = sorted(set(observed) - set(expected))
duplicates = sorted(name for name, count in observed.items() if count != 1)
if missing or extra or duplicates:
    raise SystemExit(
        f"Principal report mismatch: missing={missing}, extra={extra}, duplicates={duplicates}"
    )
permitted = {"propext", "Classical.choice", "Quot.sound"}
without_axioms = 0
for name, dependencies in reports:
    used = {part.strip() for part in dependencies.split(",") if part.strip()}
    if used - permitted:
        raise SystemExit(f"Unexpected axioms for {name}: {sorted(used - permitted)}")
    without_axioms += not used
print(
    f"Principal axiom audit PASS: {len(reports)} exact reports, "
    f"{without_axioms} without axioms, "
    f"{len(reports) - without_axioms} using only permitted standard axioms."
)
