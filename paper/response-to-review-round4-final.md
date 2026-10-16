# Follow-up to the final round-4 review: *Lean on Vampire Models*

**To:** the reviewer (Manus AI) · **From:** Michael Jagdeo and Jeff Dumps · **Date:** 16 October 2026

Thank you for executing the package and for the two reproducible defects. Both are the failure you found earlier, a layer up: accepted source information lost without an error. We fixed each on your terms, checked that no accepted output or recorded result changes, and send a small delta (`round4b__*`, base `5f37dd5`).

## 1. Ablation: identities and scope (your §3)

- **Collision-free identities.**
  - Each record now has an internal identifier: its position plus a filename-safe form of its name (`r001_a_b`).
  - Job keys and file paths, including the greedy-minimal scratch file, use that identifier; the report keeps the source names.
  - Two records with the same source name are rejected.
  - Your fixture (`'a-b'`, `a_b`, `'g-h'`, `g_h`) now gives six distinct experiments, six result rows and six distinct problem files: `test_ablation_keeps_every_experiment_distinct`. As in your probe, only the prover verdicts are stubbed.
- **Scope.**
  - Ablation reads only definitions, axioms or hypotheses, and conjectures.
  - Any other role is rejected with its record name and line before an experiment runs; so is a duplicated name.
  - Test: `test_ablation_refuses_records_it_would_otherwise_drop`, covering your `negated_conjecture` case, a `lemma` and a duplicated name.
- **Regression.** The Nakamura register ablation, rerun with real Vampire and Lean, reproduces all 36 verdicts and model sizes and both greedy sets exactly (`evidence/round4b/ablation-rerun-report.json`).

## 2. Finder classification (your §4)

`cm.classify` is an explicit decision table, kept in `cm.py` and described in §3.2 of the paper:

| Class | Answers | Cached? |
|---|---|---|
| Definite | a model (`Satisfiable`/`CounterSatisfiable` with `Satisfiable`); a refutation (`Theorem`/`Unsatisfiable`/`ContradictoryAxioms` with `Refutation`); a give-up (`GaveUp` with `Refutation not found, incomplete strategy`) | yes |
| Resource limit | `Time limit` or `Memory limit`, with no status or `Timeout`/`MemoryOut`/`ResourceOut`; recorded as *no model* | no |
| Finder error | anything else: an SZS `Error`/`InputError`/`OSError`, an unrecognized status or termination reason, no status at all, or an executable that cannot run; raised with exit code and diagnostics | no |

For a finder error, the benchmark records *finder error* and keeps the error line from its start.

**Your fixtures are now regressions** (`test_explicit_finder_errors_are_finder_errors`, 4 cases):
- `SZS status Error`, exit 1;
- `Termination reason: Internal error`, exit 3;
- an error status with an ordinary reason;
- a missing executable.

Each gives *finder error* and caches nothing. The timeout control still gives *no model*, uncached.

**No recorded outcome is affected.** All 401 cached answers classify as definite (`test_recorded_vampire_answers_classify_as_before`). The final ledgers' uncached outcomes are 73 time limits and 9 give-ups, both inside the table.

## 3. Parser and evidence corrections (your §5)

- **Malformed delimiters and empty fields.** Both record readers (`cm.statements` and the oracle's `records`) now match bracket kinds with a stack and reject empty fields. `lean()`, `tokens()` and the oracle's `holds()` also check structure as they read: `)` after a parenthesized formula or argument list; `[`, variables, `]` and `:` for a binder; no early end.
  - Your two cases, plus `p(b]` and `![X: p(X)`, are new record-level rejection fixtures.
  - `(p]`, `p(a]`, `![X] p(X)`, `![X,]: p(X)`, `(p` and `p(a,` are rejected by all three formula readers (`test_formula_readers_reject_malformed_structure`).
- **Valid input is unaffected.** Against the evaluation commit `66c8b32`, all 316 inputs read identically or are rejected by both versions (306 and 10; `bench/parser-comparison-r4b.json`), and the 30 shipped certificates regenerate byte-identically. The benchmark results and replay therefore stand as delivered.
- **Test counts.** The full suite is now 169 tests.
  - In the repository, with the corpus rebuilt: **169 passed**, pytest exit status 0 (`bench/test-log.txt`, which now records pytest's own status).
  - In a tree restored from the packages: 168 passed and 1 skipped, the corpus check, as you observed.
  - `bench/negative-controls.log` runs a selection of 64 tests plus five failure controls, and the paper describes it that way. Appendix A now has the current counts and every round-4 command.
- **The 156 figure** is now a test, `test_small_structure_check_detects_a_wrong_rewrite`, asserting exactly 156 disagreements out of 1,032.
- **Rewrite coverage selector.** It is stated as the 206 certified, native-assisted and Lean-rejected outcomes. `SYO595-1` is outside it and is not a certified result.
- **Versions.** Results come from `66c8b32`, and the released code is later. §6.2.2 lists the post-evaluation changes and the evidence above that they leave accepted outputs unchanged. The timings note keeps 253/253 reflected modules byte-identical, and 40 of 555 shallow modules directly identical, the rest after the stated renaming, which was not re-timed. The duplicated sentence in the abstract is removed.
- **The repository README.** The earlier upload had the package guide under the README's name. This delta carries the actual repository `README.md`. Its manifest records the base `README.md` as delivered in our corrected round-4 upload (SHA-256 `f8ea5c03…2fb2422`, 18,227 bytes) and its current version.

## What does not change

- **Results:** strict certification 71/78, 55/62, 59/67; native-assisted 2, 2, 3.
- **Replay:** all 185 strict certificates passed.
- **Original-formula satisfaction:** 189 of 192, with `NLP219-1`, `NLP179+1` and `NLP186+1` unchecked.
- **Rewrite validation:** bounded, as stated.

Michael Jagdeo and Jeff Dumps
