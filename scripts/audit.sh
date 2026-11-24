#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../audits"
for f in rewb_*.py; do
  echo "=== $f ==="
  python "$f"
done
