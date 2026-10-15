#!/bin/sh
# Rebuild everything, print the axioms of every shipped certificate, and replay each library through the kernel
# from scratch (leanchecker --fresh, shipped with Lean 4.35). Writes bench/recheck.log; exits non-zero on any failure:
# every step's own exit status is checked (no pipe hides it), and the log is then scanned for unsound axioms.
cd "$(dirname "$0")" || exit 1
log=bench/recheck.log
fail() { echo "FAILED: $1" >> "$log"; cat "$log"; exit 1; }
if git rev-parse --git-dir >/dev/null 2>&1; then
  echo "commit $(git rev-parse --short HEAD)$(git diff --quiet HEAD -- . ':!bench' || echo ' (+uncommitted changes)')" > "$log"
else
  echo "commit: not a git checkout (e.g. restored from the review package; see 01_MANIFEST.json)" > "$log"
fi
lake env lean --version >> "$log" 2>&1 || fail "lean --version"
lake build > bench/recheck-build.tmp 2>&1 || { cat bench/recheck-build.tmp >> "$log"; rm -f bench/recheck-build.tmp; fail "lake build"; }
tail -1 bench/recheck-build.tmp >> "$log"; rm -f bench/recheck-build.tmp
for lib in Cm Refl; do
  f=$(mktemp -t ax).lean
  for m in $lib/*.lean; do echo "import $lib.$(basename "$m" .lean)"; done > "$f"
  for m in $lib/*.lean; do echo "#print axioms $(basename "$m" .lean).countermodel"; done >> "$f"
  echo "== axioms: $lib" >> "$log"
  lake env lean "$f" >> "$log" 2>&1 || { rm -f "$f"; fail "axioms of $lib"; }
  rm -f "$f"
done
for m in Checker AllShallow AllReflected; do
  s=$(date +%s)
  lake env leanchecker --fresh $m >> "$log" 2>&1 || fail "leanchecker --fresh $m"
  echo "== leanchecker --fresh $m: ok in $(( $(date +%s) - s )) s" >> "$log"
done
cat "$log"
if grep -qE "sorryAx|_native|ofReduceBool|exception|error" "$log"; then echo "FAILED: unsound axiom or error in the log"; exit 1; fi
