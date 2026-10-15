#!/bin/sh
# Rebuild everything, print the axioms of every shipped certificate, and replay each library through the kernel
# from scratch (leanchecker --fresh, shipped with Lean 4.35). Writes bench/recheck.log; exits non-zero on any failure.
set -e
cd "$(dirname "$0")"
{
  echo "commit $(git rev-parse --short HEAD)$(git diff --quiet HEAD -- . ':!bench' || echo ' (+uncommitted changes)')"
  lake env lean --version
  lake build 2>&1 | tail -1
  for lib in Cm Refl; do
    f=$(mktemp -t ax).lean
    for m in $lib/*.lean; do echo "import $lib.$(basename "$m" .lean)"; done > "$f"
    for m in $lib/*.lean; do echo "#print axioms $(basename "$m" .lean).countermodel"; done >> "$f"
    echo "== axioms: $lib"; lake env lean "$f"; rm "$f"
  done
  for m in Checker AllShallow AllReflected; do
    s=$(date +%s); lake env leanchecker --fresh $m; echo "== leanchecker --fresh $m: ok in $(( $(date +%s) - s )) s"
  done
} 2>&1 | tee bench/recheck.log
! grep -qE "sorryAx|_native|ofReduceBool|exception|error" bench/recheck.log
