# AGENTS.md: working on lean-countermodel

This is for AI coding agents and human contributors. It covers what the code is, how to run it, and the rules that keep its certificates meaning what they say. For results, see `README.md`; for design and evidence, `paper/whitepaper.md`.

## What it does

`cm.py` reads a TPTP problem (`fof`/`cnf`), asks Vampire for a finite model of `axioms ∧ ¬conjecture`, and writes a Lean 4 certificate that Lean's kernel checks. It writes one of two forms:
- **Shallow:** an `inductive T`, and one `theorem c<i>' := by decide` per formula.
- **Reflected:** the problem and model as packed data, checked by the verified evaluator in `Checker.lean`.

What is trusted:
- **Vampire is untrusted.** A wrong model yields no certificate.
- **Lean's kernel is the trusted base.**
- **Reading, rewriting and translating TPTP is trusted code, tested but not verified.** Most real defects have been here. Lean proves exactly the statement it is given, so a statement that lost part of the source is a wrong certificate even though Lean accepts it.

## Layout

| Path | What |
|---|---|
| `cm.py` | The pipeline: `statements` (total record reader) → `problem` (miniscoping rewrite) → `vampire`/`classify` (finder, with the answer decision table and the cache) → `model` (parse Vampire's model) → `emit` (shallow) or `emit_reflect` (reflected) |
| `Checker.lean` | The verified evaluator: `Fm.check_iff`, `sem_iff_sat`, `Model.valid`, `Fm.wf`, `Good`, `countermodel_of_good` |
| `test_cm.py` | 170 tests. It also holds the **independent oracle**: `records`/`raw` (its own record reader), `holds` (brute-force evaluator) and `clause_holds` (clause search) |
| `tests/Boundary.lean` | Kernel-checked boundary cases for the checker |
| `examples/*.p` → `Cm/*.lean`, `Refl/*.lean` | 15 example problems and their generated shallow and reflected certificates. **Generated; tests require them to equal `cm.py`'s output** |
| `AllShallow.lean`, `AllReflected.lean`, `Axioms.lean` | Aggregates used by `recheck.sh` and the axiom tests |
| `ablate.py`, `ablation/` | The assumption-dependency map (the Spinoza case study) |
| `bench.py`, `bench/*.py` | The benchmark harness: `frozen.py` (frozen runs), `replay.py` (fresh kernel replay), `inputs.py` (inputs from the TPTP release), `fidelity.py`, `rewrite_check.py`, `coverage.py`, `compare_parsers.py`, `perf.py`, `negative-controls.sh` |
| `bench/*.jsonl`, `*.json`, `*.log` | **Recorded evidence.** Never edit by hand (see the rules below) |
| `nakamura/` | Certificates compiled against Nakamura's unmodified Lean library (pins Lean 4.13) |
| `evidence/` | Small, committed review evidence (collision certificate, wrong-model rejections, ablation rerun) |
| `paper/` | The whitepaper: section sources in `paper/whitepaper/`, built by `paper/assemble.py`; response letters; package builders |

Git-ignored and regenerable: `bench/problems`, `bench/sources`, `bench/axioms` (from the TPTP release), `bench/vampire-cache`, `bench/lean`, `bench/olean`, `bench/replay`, `.lake/`.

## Setup and commands

```sh
lake build                                   # Lean 4.35.0 via elan (lean-toolchain); no Lean package dependencies
export VAMPIRE=/path/to/vampire              # Vampire 5.1.0
python3 -m pytest test_cm.py -q              # about 30 s; fresh clone: 168 passed, 2 skipped (need corpus and cache)
./recheck.sh                                 # axioms of all 30 shipped certificates + leanchecker --fresh; exit 0
bench/negative-controls.sh [TPTP-v9.3.1]     # every safeguard fails when it should; writes bench/negative-controls.log
python3 paper/assemble.py                    # rebuild paper/whitepaper.md and .pdf (pandoc + Tectonic); fails on any {{placeholder}}
```

## Rules

1. **Never let a record or premise disappear.**
   - Readers must account for the whole input or raise `ValueError` with a reason: `cm.statements` and the oracle's `records`, and also `ablate.py`, which rejects roles outside its language and duplicate names.
   - Never search for structure with a regular expression and skip what doesn't match.
   - Every formula reader checks its closing tokens.
2. **Keep the oracle independent.** Don't import `cm.statements`, `problem`, `lean` or `tokens` into the oracle in `test_cm.py`. It already shares `TOKENS` and `VARS`, a disclosed limitation; don't widen that.
3. **A change to reading, rewriting or emitting needs evidence that it doesn't change meaning:**
   - the full suite;
   - `python3 bench/compare_parsers.py <evaluation commit> OUT.json`, which must show identical record lists, or explain every difference;
   - regenerated `Cm/` and `Refl/` (`python3 cm.py examples/X.p > Cm/X.lean`, and `--reflect` for `Refl/`): commit them, and the tests check equality;
   - `./recheck.sh`.

   If any accepted output changes, the affected benchmark results must be rerun and reported. Don't carry them forward silently.
4. **Finder answers go through `cm.classify`.**
   - Definite answers (model, refutation, give-up) may be cached.
   - Time or memory limits are *no model* and are never cached.
   - Anything else, including a cache entry that doesn't classify as definite, is a *finder error*.
   - Never treat every nonzero exit as an error: Vampire 5.1 reports a timeout with exit 1 and no SZS status.
5. **Recorded evidence is append-only.**
   - `bench/results-final-*.jsonl`, `bench/superseded-*`, `bench/inputs.json`, `bench/perf.jsonl`, `replay-*`, `fidelity*`, `rewrite-check*` and `coverage*` are produced by scripts at a recorded commit.
   - To replace a result, move the old file to a `superseded-<commit>-*` name and rerun from a clean worktree of the commit (see `bench/frozen.py`).
   - Never edit counts by hand.
6. **Strict and native are different claims.** `cm.py` never emits `native_decide`; the harness tries it only after a `decide` timeout and records *certified (native)* separately. Fresh replay covers strict certificates only.
7. **Timing runs need an idle machine.** Check for stray processes (`ps aux | grep -E "python|lean|vampire"`) before a frozen or timing run. Background load has caused a spurious timeout before.
8. **Claims follow evidence.** Before writing a number in the README or paper, read it from the log that produced it. Say *unchecked*, not *passed*, for checks that did not finish, and name them.
9. **Don't publish or push without the maintainers' go-ahead.** The repository has been private during review.

## Adding an example

1. Put the problem in `examples/name.p`.
2. Generate `Cm/name.lean` and `Refl/name.lean` with `cm.py` (and `--reflect`). Then:
   - add `import Cm.name` to `AllShallow.lean` and `import Refl.name` to `AllReflected.lean`, which list their modules explicitly;
   - add the example's import and `#print axioms name.countermodel` line to `Axioms.lean`, following its existing entries. `test_kernel_accepts_with_propext_only` expects one line per example.
3. Run the suite and `./recheck.sh`.

The tests parametrized over `examples/*.p` pick it up automatically.
