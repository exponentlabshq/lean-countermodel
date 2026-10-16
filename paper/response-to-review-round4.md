# Response to the artifact-based review: *Lean on Vampire Models*

**To:** the reviewer (Manus AI) · **From:** Michael Jagdeo and Jeff Dumps · **Date:** 15 October 2026

Thank you. You found a real defect in our trusted translation layer, in code we had described as tested. Your protocol showed it precisely, and you separated it carefully from what it does not affect. We reproduced it, fixed it on your route, measured its effect on every reported result, and reran the evaluation. Details follow in the order of your section 6.

## 1. The defect, confirmed and measured

We reproduced both of your inputs: `cm.problem()` returned only `~p(a)` for each. The cause was as you described. The record regular expression *searched* for records instead of *reading* the file, so a record it could not match was skipped, and nothing checked that the whole file had been consumed. The test oracle had copied that regular expression, so it agreed on the weakened problem.

**Its effect on the benchmark.** We first ran a read-only audit, then a full old-versus-new comparison (`bench/compare_parsers.py`, output `bench/parser-comparison.json`):
- **297 of the 316 inputs** (300 benchmark problems, 15 examples, the ablation theory) read identically. That includes NLP263+1, compared as an exact list of 1,026,857 records.
- **10** are rejected by both versions, as before.
- **9 changed.** Each has quoted record names with punctuation (`'EQ-var'`, `'thm.bool.TRUTH'`), and the old reader had silently skipped records in all of them:

| Problem | Sample | Records read before → now | Reported before (round 3) |
|---|---|---|---|
| `COM150+1` | second | 28 → 60 | no model (Vampire read the full file, so this verdict stands) |
| `SWW883+1` | development | 5 → 10 | **certified** |
| `SWW882+1`, `SWW902+1`, `SWW938+1`, `SWW942+1` | second | 5 → 11, 28, 34, 10 | **certified** |
| `SWW865+1`, `SWW889+1`, `SWW921+1` | third | 5 → 18, 44, 13 | **certified** |

**Eight certificates reported in round 3 checked weakened problems.** Each Lean proof is correct for the formulas it states, but those were not all the formulas of the source problem, so they were not the certificates of source problems that we claimed. We withdraw those eight results as reported. The round-3 records are preserved as `bench/superseded-acb343b-{dev,second}.jsonl` and `bench/superseded-30ad4f3-third.jsonl`, and the corrected results are in §4 below.

## 2. The repair: total, fail-closed record reading (your point 1)

`cm.statements` now reads the whole file. Every character must be one of three things:
- whitespace;
- part of a `%` comment;
- part of a complete record `kind(name, role, formula[, annotations]).`.

Anything else rejects the file with its line number before any certificate is generated: stray text, another statement kind, a malformed or unterminated record, a role without assertion meaning (`type`, `unknown`, …), or a `/* */` comment.

The reader:
- respects quoted tokens, whose `%`, commas and parentheses are not syntax;
- allows comments and whitespace between any two tokens;
- tracks nesting depth;
- splits records at top-level commas, so annotations are never read as formulas.

Names may be lower-case words, quoted words with any punctuation, or integers, which is the TPTP grammar you cite. Each record keeps its name, role, line and exact text. `problem()` builds one formula per record, and `ablate.py` now reads records only through `statements`.

## 3. An independent oracle, and your regressions (your points 2 and 3)

**The oracle has its own reader.** `test_cm.records` is written separately: its own lexer (`ORACLE_LEX`) and a token-level matcher that must consume every token. It shares no code with `cm.statements`. The oracle still shares two small helpers with `cm.py`, the in-formula lexer `TOKENS` and the variable collector `VARS`, and the paper says so (§3.10).

**New tests (149 in total, up from 106; all pass, `bench/negative-controls.log`):**
- **Hand-counted fixtures** (`test_every_record_is_accounted_for`, 7 cases): your two files; spaced and commented record syntax; annotations; integer names and punctuated quoted names (`'thm.bool.TRUTH'`, `'it\'s'`); `%` inside a name; and a comment that hides a fake record. `statements`, the oracle and `problem` must each match the hand count.
- **Rejections** (`test_unreadable_records_are_rejected_not_skipped`, 9 cases): both readers refuse each file.
- **Your protocol** (`test_a_model_of_part_of_the_problem_is_rejected`): for each of your files, a one-element model of `~p(a)` only. The oracle rejects it, and Lean rejects both the shallow and the reflected certificate.
- **Rewrite equivalence on small structures:** `test_rewriting_is_equivalent_on_every_small_structure`, the 18 adversarial forms in §4 below.
- **An independent clause-search evaluator,** validated against brute force on every small structure: `test_clause_search_agrees_with_brute_force`.
- **A fidelity-check control:** `test_fidelity_check_flags_a_model_of_part_of_the_problem`. On your wrong model, the source-fidelity check reports NOT FAITHFUL.
- **Your own script.** Run against the repaired code, `reproduce_source_omission.py` stops at its first assertion, because both readers now return two records. Feeding the saved wrong model through the CLI on both paths, Lean rejects all four certificates; `decide` reports that `p(a)` is false.

## 4. The evaluation, rerun (your point 4)

**Version.** All three samples were rerun at commit `66c8b32`, from a separate worktree, with the same 30 s Vampire limit and budgets. One earlier rerun, at `8d46e97`, was stopped after its development sample because it misclassified timeouts (§5 below); its ledger is kept.

**Load.** All three samples were rerun with a background process occupying one CPU core: an orphaned worker of our own parse comparison, found and stopped afterwards. Strict certification totals were unchanged. `ALG310-1` exceeded the native-assisted time limit; background contention may have contributed, but causation was not established. The timeout is retained in the reported outcomes.

| Outcome | Development | Second sample | Third sample |
|---|---|---|---|
| Unsupported input | 3 | 4 | 3 |
| Translator crash before a model outcome | 0 | 0 | 1 (`KRS290-1`) |
| Vampire found no model within 30 s | 19 | 34 | 29 |
| **Models found** | **78** | **62** | **67** |
| **Certified, strict kernel only** | **71** | **55** | **59** |
| Certified with `native_decide` | 2 | 2 | 3 |
| Lean rejected | 5 | 5 | 4 |
| Model found, certificate generation crashed | 0 | 0 | 1 (`SYO595-1`) |
| **Strict, of models found** | **91.0%** | **88.7%** | **88.1%** |
| Full pipeline, strict, of all sampled | 71% | 55% | 59% |
| Full pipeline, strict, of supported inputs | 73.2% | 57.3% | 60.8% |

Each column sums to 100. Every record carries its commit and input SHA-256 (`bench/results-final-*.jsonl`).

**Old to new.** Eight earlier certificates omitted source premises and were withdrawn. The repaired pipeline subsequently certified their complete source problems. Unchanged strict totals do not validate the superseded certificates. One previously native-assisted result timed out in the rerun and is reported as a failure.

| Problem | Sample | Round 3 (weakened problem) | Round 4 (complete problem) |
|---|---|---|---|
| `SWW883+1` | development | certified, 5 of 10 records | certified, 10 records, 2 elements |
| `SWW882+1`, `SWW902+1`, `SWW938+1`, `SWW942+1` | second | certified, 5 records each | certified, 11, 28, 34 and 10 records, 2 elements each |
| `SWW865+1`, `SWW889+1`, `SWW921+1` | third | certified, 5 records each | certified, 18, 44 and 13 records, 3, 2 and 2 elements |
| `ALG310-1` | third | native-assisted (54.8 s) | Lean rejected: native timeout at 60 s |

Of the 300 verdict labels, 299 match round 3; `ALG310-1` is the one that changed. The eight withdrawn problems keep the label *certified*, but it now refers to their complete source problems, with new certificates. Every strict total is unchanged.

**Fresh replay of the strict certificates.** All 185 compiled and passed `leanchecker --fresh` (development 71 in 910 s, including NLP263+1; second 55 in 47 s; third 59 in 55 s; `replay.py` exited 0). Their axioms are `propext` for 182, `propext` and `Quot.sound` for the two reflected certificates, and none for `SYN092-1.003`. The seven native-assisted results are not replayed and stay a separate category. Replay shows the kernel accepts the emitted statements, not that they are faithful to the source.

**Source fidelity, every certified result** (`bench/coverage.md`, generated by `bench/coverage.py`). Each check is reported separately:

| | Strict (185) | Native-assisted (7) |
|---|---|---|
| Original-formula satisfaction (oracle reads the original file) | 184 faithful, 1 unchecked | 5 faithful, 2 unchecked |
| Rewrite agreement (bounded) | 176 agree, 9 unchecked | 4 agree, 3 unchecked |
| Compilation and fresh replay | 185 passed | not replayed |
| Failed | 0 | 0 |

**Three results are unchecked for original-formula satisfaction:** `NLP219-1` (strict), and `NLP179+1` and `NLP186+1` (native-assisted). Their supplementary checks are reported separately and do not close that gap:
- **Record identity:** identical for all three.
- **Rewritten satisfaction:** satisfied for `NLP179+1`; unchecked for the other two.

So the source-fidelity claim covers 189 of the 192 certified results, and the paper says so.

**Rewrite validation.**
- **Adversarial forms:** all 18 cases agree on all 1,032 structures each (18,576 comparisons). A deliberately wrong rewrite disagrees on 156 of the 1,032.
- **Benchmark:** 192 of the 206 problems with a model were checked in full, covering 7,165 rewritten formulas and 364,181 evaluations, with **0 disagreements**. The other 14 are unchecked at 60 s and named in `bench/rewrite-check.jsonl`.

This is exhaustive within the stated finite test space and bounded validation on the benchmark, not a proof of equivalence.

**Timing version.** The timings remain those measured at `62d43d6`. Regenerated with the final code, all 253 reflected modules of NLP263+1 are byte-identical. The shallow modules differ only by the round-4 helper renaming and the `Nonempty T` conjunct: applying exactly that renaming to the timed output makes all 555 byte-identical. The shallow change was not re-timed.

## 5. Failure propagation, input verification, metadata, budgets and name collisions (your point 5)

- **Vampire's status.** An answer with neither an SZS status nor a termination reason raises and is never cached, and the benchmark records it as *finder error*. Our first version of this check required an SZS status and nothing else. Vampire 5.1 reports a timeout as `% Termination reason: Time limit`, with exit 1 and no SZS status, so the development rerun at `8d46e97` labelled its 17 timeouts *finder error*. We stopped that run, kept its partial ledger (`bench/superseded-8d46e97-dev-timeout-misclassified.jsonl`), fixed the rule at `66c8b32`, added a regression (`test_a_timeout_is_a_search_outcome_not_a_failure`), and reran all three samples. Run-dependent statuses (Timeout, MemoryOut, ResourceOut, Error, InputError, OSError) are not cached. All 401 cached answers carry a status (CounterSatisfiable 183, Satisfiable 202, GaveUp 15, Theorem 1), so no recorded outcome rests on a statusless answer. Tests: `test_a_failing_finder_is_not_a_search_outcome` and `test_benchmark_reports_a_failing_finder_as_finder_error` (the benchmark's own classification).
- **Scripts.**
  - `perf.py` counts a run as successful only if every module builds, the axiom audit itself exits 0, and it shows no unsound axiom; any failed run makes the command exit 1.
  - `replay.py` exits 1 if any certificate fails to compile or replay, or uses an axiom outside the standard set.
  - `recheck.sh` checks each step's own exit status, with no pipe hiding it; a negative control with `lake` missing exits 1 and names the failed step.
- **`inputs.py`.** It now has two modes:
  - `verify` rebuilds every input and compares it with the committed manifest, checks the tarball digest against the fixed one, and never rewrites the manifest. Run against the release, it verifies all 300 problems, 65 axiom files and the tarball digest; one altered byte fails it.
  - `record` writes `bench/inputs.candidate.json`.
- **Sampling metadata.** `bench/third-sample.json` now names the four excluded exploratory problems (`BOO059-1`, `MSC018+1`, `PRD003+1`, `PUZ067+1`) and gives the pool size (2,357) and its SHA-256, with the rule that defines it. We checked that the recorded draw reproduces exactly from them.
- **Budgets.** §6.2 now states them as the code applies them:
  - **Shallow:** 60 s with `decide`, then a second 60 s with `native_decide`, reported separately.
  - **One-file reflected:** 60 s.
  - **Modular reflected:** 600 s per module, four Parts in parallel, no overall cap. Only NLP263+1 uses it.
- **Name collisions.** The shallow emitter's helper declarations now carry a prime (`c0'`, `P0'`, `C0'`, `chunk0'`), which no TPTP lower-case word contains; quoted names are always emitted inside their quotes. You are right that `«countermodel»` is the same Lean name as `countermodel`, so quotation marks around the identifier would fix nothing. The repair puts the quote characters *inside* the name: a source symbol `countermodel` (or `'countermodel'`, the same TPTP symbol) becomes the Lean name `«'countermodel'»`, which differs from the public theorem `countermodel`. A quoted source name can't reach a helper name either. A name that isn't a plain lower-case word is emitted with a leading quote character inside the Lean name, and a plain word can't contain a prime, so neither form can equal `c0'`, `P0'`, `C0'` or `chunk0'`. The generated collision certificate is supplied (`evidence/round4/collision.lean`). `#check` shows `collide.c0 = collide.«'countermodel'»` beside the public `collide.countermodel`, and it depends on no axioms. Test: `test_source_symbols_cannot_collide_with_generated_names`, with symbols `c0`, `p0`, `chunk0` and `countermodel` on both paths.
- **Cache provenance.** You are right that the cache files and invocation logs were not supplied, so the no-retry-success inference rests on our records. The paper keeps that qualification.

## 6. The textual corrections from your previous assessment

All eight are now in the paper:
- the third-sample qualification, updated for this rerun;
- the footnote resolving the overlap in the outcome table;
- native-assisted totals per sample;
- `SYO595-1` in the abstract's failure description;
- your "no-model-found" wording;
- the §3.4 heuristic sentence;
- "second and third" for the uniform samples;
- the measured-version qualification next to the 2.7× figure.

The paper now also refers to Nakamura without gendered pronouns, which we should have done from the start.

## What remains trusted

The TPTP-to-Lean translation is still trusted code. It is now total at the record level and tested against an oracle that reads records independently, but it is not verified. The oracle's formula evaluator still shares the in-formula lexer and the variable collector with `cm.py`. Positive ablation results remain uncertified Vampire proofs.

Michael Jagdeo and Jeff Dumps
