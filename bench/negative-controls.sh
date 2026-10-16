#!/bin/sh
# Negative controls for the round-4 repairs (whitepaper §6.2.2). Each control must FAIL in the stated way; the script
# records every command, its exit status and the expected status, and exits non-zero if any control behaves otherwise.
# Usage: bench/negative-controls.sh [TPTP_DIR]   (VAMPIRE set; TPTP_DIR, an unpacked TPTP-v9.3.1, enables control 5)
# Writes bench/negative-controls.log.
cd "$(dirname "$0")/.." || exit 1
log=bench/negative-controls.log
bad=0
expect() {  # expect NAME WANT(0|nonzero) command...
  name=$1; want=$2; shift 2
  echo "== $name: $*" >> "$log"
  "$@" >> "$log" 2>&1; got=$?
  if [ "$want" = 0 ]; then
    if [ $got -eq 0 ]; then r=ok; else r=UNEXPECTED; bad=1; fi
  else
    if [ $got -ne 0 ]; then r=ok; else r=UNEXPECTED; bad=1; fi
  fi
  echo "== $name: exit $got (expected $want) $r" >> "$log"
}
echo "commit $(git rev-parse HEAD 2>/dev/null || echo 'not a git checkout'); $(date)" > "$log"

# 1. The regression tests that encode the reviewers' protocols and the other controls (a selection of test_cm.py;
#    the full suite's own run is bench/test-log.txt). They must pass.
expect "round-4 regression tests" 0 python3 -m pytest test_cm.py -v -p no:cacheprovider -k \
  "model_of_part or collide or failing_finder or finder_error or explicit_finder or recorded_vampire or timeout_is or accounted_for or rejected_not_skipped or annotations or fidelity_check or clause_search or every_small_structure or wrong_rewrite or benchmark_records or ablation_keeps or ablation_refuses or malformed_structure"

# 2. recheck.sh must fail when the build cannot run (lake absent).
expect "recheck.sh without lake" nonzero env PATH=/usr/bin:/bin ./recheck.sh

# 3-4. replay.py must fail on a certificate that does not compile, and on one that compiles only with sorry.
tmp=$(mktemp -d)
mkdir -p bench/lean
printf 'namespace NEGFAIL_1\ntheorem countermodel : 1 = 2 := by decide\nend NEGFAIL_1\n' > bench/lean/NEGFAIL+1.decide.lean
printf 'namespace NEGSORRY_1\ntheorem countermodel : 1 = 2 := by sorry\nend NEGSORRY_1\n' > bench/lean/NEGSORRY+1.decide.lean
printf '{"problem": "NEGFAIL+1.p", "method": "shallow", "verdict": "certified", "commit": "control"}\n' > "$tmp/results-final-fail.jsonl"
expect "replay.py, certificate that does not compile" nonzero python3 bench/replay.py "$tmp"
rm "$tmp/results-final-fail.jsonl"
printf '{"problem": "NEGSORRY+1.p", "method": "shallow", "verdict": "certified", "commit": "control"}\n' > "$tmp/results-final-sorry.jsonl"
expect "replay.py, certificate using sorry" nonzero python3 bench/replay.py "$tmp"
cat "$tmp"/replay.log >> "$log" 2>/dev/null
rm -rf "$tmp" bench/lean/NEGFAIL+1.decide.lean bench/lean/NEGSORRY+1.decide.lean

# 5. inputs.py verify must fail on one altered byte of a release file, and pass again when it is restored.
if [ -n "$1" ]; then
  f="$1/Problems/SYN/SYN307-1.p"; cp "$f" "$f.bak"; printf ' ' >> "$f"
  expect "inputs.py verify, one altered byte" nonzero python3 bench/inputs.py verify "$1"
  mv "$f.bak" "$f"
  expect "inputs.py verify, restored" 0 python3 bench/inputs.py verify "$1"
fi

echo "== overall: $([ $bad = 0 ] && echo 'every control behaved as expected' || echo 'SOME CONTROL BEHAVED UNEXPECTEDLY')" >> "$log"
cat "$log"
exit $bad
