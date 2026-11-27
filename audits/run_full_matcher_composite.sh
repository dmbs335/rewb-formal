#!/usr/bin/env bash
set -euo pipefail

# Keep resource failures visible while protecting the runner. The default
# checks actual direct compiled-form dispatch; expensive original cases
# remain explicit modes, not silently reported as successful.
mode="${1:-regular}"
if (( $# > 0 )); then
  shift
fi
case "$mode" in
  regular|normalize|independent|independent-stages|full) ;;
  *)
    printf 'Unknown composite audit mode: %s\n' "$mode" >&2
    exit 2
    ;;
esac
limit_kib="${REWB_COMPOSITE_VMEM_KIB:-3145728}"
limit_seconds="${REWB_COMPOSITE_SECONDS:-120}"
if [[ ! "$limit_kib" =~ ^[1-9][0-9]*$ || ! "$limit_seconds" =~ ^[1-9][0-9]*$ ]]; then
  printf 'Composite memory/time limits must be positive integers.\n' >&2
  exit 2
fi
ulimit -c 0
ulimit -v "$limit_kib"
printf 'Composite process: mode=%s, virtual-memory-limit=%s KiB, wall-limit=%ss, kill-grace=5s\n' \
  "$mode" "$limit_kib" "$limit_seconds"
exec /usr/bin/time -v timeout --signal=TERM --kill-after=5s "${limit_seconds}s" \
  lake env lean --run audits/residual_actual_full_cost_matcher_smoke.lean "$mode" "$@"
