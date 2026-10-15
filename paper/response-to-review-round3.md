# Response to the third-round review: *Lean on Vampire Models*

**To:** the reviewer (Manus AI) · **From:** Michael Jagdeo and Jeff Dumps · **Date:** 15 October 2026

Thank you. This round asked the right question about the second sample, and answering it properly led us to a defect we had not seen. We take the four major comments in order, then the consistency corrections.

## Correction first: a defect in our input preprocessing

To answer comment 3, we rebuilt every benchmark input from the official TPTP v9.3.1 release (933,955,664-byte tarball, SHA-256 `8e9462d9443a2250000224cf4f7002a64ea02cbe07fa5cdcdecfd0fe8cd81f03`) and compared it with what we had run.

- **198 of the 200 evaluated inputs matched** the release, except for trailing blank lines left by scraping TPTP's web pages. One of them, `GEO661+1`, also had a double-encoded apostrophe inside a `%` comment.
- **Two did not:** `BOO008-3` (second sample) and `RNG025-9` (development).
  - Each contains an include that the TPTP file comments out, `% include('Axioms/…').`, because the axioms are written inline instead.
  - Our old expander matched the include inside the comment and inlined the axiom file. Only its first line stayed inside the comment, so the axiom file's clauses became part of the problem.
  - The stored inputs therefore had 43 and 40 clauses, against 21 and 25 in the originals.
- **No certificate rested on a misread input.** Both had been recorded as *no model*.
- **The verdicts were nonetheless for the wrong problems.** On the correct input, `RNG025-9` has a 3-element model, which the kernel certifies; it moves from *no model* to *certified* in the development results below. `BOO008-3` likewise has a 2-element model on its correct input and is now certified in the second sample. The defect produced two false *no model* verdicts and no wrong certificate.

Your comment 3 called this preprocessing "trusted, untested". That was accurate, and the defect was there. It is now tested and checked against the release (comment 3).

## 1. The second sample is not an untouched test

**We agree.** Freezing the code during the final run made that run stable, but it could not undo our earlier exposure to the sample. We did both things you offered.

- **Recharacterized.** The paper now calls the 100 problems drawn with seed 20261015 the *second sample*: "initially held out, subsequently used to diagnose and repair implementation defects". Its results are reported as descriptive, not as a test of generalization. The sentence attributing the difference to the finder's yield is replaced with descriptive language close to the wording you suggested.
- **A new sample, frozen before any result, with one disclosed adaptation.**
  - **Drawn before any result.** We drew 100 further problems uniformly, without replacement, with seed 20261016 (`bench/third-sample.json`). The pool was the 2,357 eligible problems in neither earlier set and not among our four exploratory problems.
  - **Committed with the frozen code** (`900818d`), before any result on the sample existed.
  - **Launch 1, at `900818d`.** It stopped on its first development certificate, because a fresh worktree lacked the `bench/lean` directory. No third-sample problem had been reached. `acb343b` creates the directory.
  - **Launch 2, at `acb343b`.**
    - The development and second samples completed and are reported at that commit.
    - The third stopped when `KRS290-1` raised a `RecursionError` that the harness's in-process pre-check did not catch: its formulas nest deeper than Python's recursion limit. No third-sample verdict was written.
    - Before it stopped, the run had executed Vampire on the third-sample problems it reached and may have compiled certificates for some. Those Vampire answers remain in the content-addressed cache; we did not inspect them or any intermediate result.
    - To locate the crash, we reran only the translator's pre-check on the third sample. It showed that `KRS290-1` alone raises the exception. The record is in `bench/superseded-acb343b-third-attempt1.txt`.
  - **The one change after that (`30ad4f3`)** is in the harness: a translator exception is now recorded as *cm.py error* instead of stopping the run. `cm.py`, `Checker.lean`, the dispatch rule, the limits and the inputs are unchanged, so `KRS290-1` is reported as a failure, not repaired.
  - **Launch 3, at `30ad4f3`,** ran the third sample in full. It is reported as recorded.
  - **Our judgement.** Under your criterion, the third sample is not strictly untouched: one fact learned from it led to a harness change. We judge that change neutral for the reported rates, because it turns a crash of the whole run into one recorded failure and no verdict the frozen translator could produce changed. You may weigh it differently, and the record lets you.

| Outcome | Development (100), `acb343b` | Second sample (100), `acb343b` | **Third sample (100), `30ad4f3`** |
|---|---|---|---|
| Unsupported input | 3 | 4 | 3 |
| Translator crash (*cm.py error*) | 0 | 0 | 2 |
| Vampire found no model within 30 s | 19 | 34 | 29 |
| **Models found** | **78** | **62** | **67** |
| **Certified, strict kernel only** | **71** | **55** | **59** |
| Certified with `native_decide` | 2 | 2 | 4 |
| Lean rejected (time or instance-search limits) | 5 | 5 | 3 |
| Model found, certificate not written | 0 | 0 | 1 |
| **Strict, of models found** | **91.0%** | **88.7%** | **88.1%** |
| **Full pipeline, strict, of all sampled** | **71%** | **55%** | **59%** |
| Full pipeline, strict, of supported inputs | 73.2% | 57.3% | 60.8% |

**Reading, in the descriptive terms you proposed.** On the third sample, the frozen implementation strictly certified 59 of the 67 models Vampire found. Its conditional rate (88.1%) is similar to the development set (91.0%) and the second sample (88.7%), though samples of this size cannot establish that the rates are equal. Full-pipeline success differs more, and that difference coincides mainly with the finder's yield within 30 s (78, 62 and 67 models).

**Two new failure classes, reported rather than fixed.** Both are in §6.2.1 and §8.2:
- **`KRS290-1`:** formulas nested past the recursion limit of `cm.py`'s recursive-descent translator.
- **`SYO595-1`:** Vampire found a model, but the problem has more than 2,000 formulas, so `cm.py` emits a multi-module certificate. The benchmark's shallow path does not pass the output directory that output needs, so `cm.py` crashes before writing the certificate. We count it as a found model that was not certified.

## 2. The artifact, and the scope of fresh replay

**Access.** Access did not fail on your side: the repository is private, so its URL returns 404 to anyone outside our organization. The immutable artifact is a `git archive` of the tag `review-2026-10-15-r3`. It is sent with this letter, with its commit and SHA-256 in the cover message, since a file cannot contain its own checksum. It contains:
- the revised manuscript;
- all sources, tests and toolchain files;
- the 30 shipped certificates;
- every raw log: results, superseded runs, timings and replay;
- `bench/inputs.json`, which gives the SHA-256 of the TPTP release tarball and of every original problem, expanded problem and axiom file.

The TPTP inputs themselves (42 MB of originals, 95 MB of axiom files) are not in the archive. `bench/inputs.py` rebuilds them from the public release, and a test checks them byte for byte against the manifest.

**Fresh replay, now for the benchmark certificates as well.** `bench/replay.py` takes every strictly certified benchmark certificate from the frozen run and does three things:
- recompiles it as a module;
- prints `#print axioms` for its `countermodel`;
- replays one aggregate module per sample from scratch with `leanchecker --fresh`, imports included.

`bench/replay.py` recompiled every strictly certified benchmark certificate from the frozen runs as a Lean module, printed `#print axioms` for each `countermodel`, and replayed one aggregate module per sample from scratch with `leanchecker --fresh`, imports included (Lean 4.35, on the same laptop). **All 185 replayed:** development 71 in 896 s, including the million-fact NLP263+1 certificate; second sample 55 in 67 s; third sample 59 in 191 s (`bench/replay.log`, `bench/replay-{dev,second,third}.jsonl`). Axioms: `propext` for 182, `propext` and `Quot.sound` for the two reflected certificates (NLP263+1 and AGT042+1), and none at all for `SYN092-1.003`; the replay script's summary line flagged that last one only because its parser did not recognize Lean's "does not depend on any axioms" message, which the log records (parser fixed afterwards). Native-assisted certificates are not replayed: replay cannot validate their compiled-code axioms, so they stay a separate, weaker category. `leanchecker --fresh` replays through Lean's own kernel; it is not an independent kernel implementation. The paper says so (§6.2.1).

**Version relationship between the timings and the evaluation.** The timings were taken at `62d43d6`, before the input rebuild and the `Nonempty T` change; the evaluation commits are `acb343b` and `30ad4f3`. We regenerated the NLP263+1 certificates with both commits from the same cached Vampire model and compared them file by file (`bench/perf-equivalence.json`). **All 253 reflected modules are byte-identical**, so the reflected timing measured exactly the certificate the final code produces. **554 of the 555 shallow modules are byte-identical**; the exception is `Main.lean`, whose statement gains the `Nonempty T` conjunct and whose proof term gains `⟨T.e1⟩` (three lines). The shallow timing therefore measured a certificate that differs from the final one by that conjunct, which we have not re-timed; we expect its cost to be negligible next to 555 modules, but that is an expectation, not a measurement. The input itself changed only by trailing blank lines (70,340,949 against 70,340,939 bytes). Byte equality establishes identical certificates, not identical timings on a different day.

## 3. Source-fidelity testing, described consistently

**The oracle.** The mutant tests never used `problem(path)`. The text of §3.10 and §4.6 was stale, and we have corrected it. Both §3.10 and §4.6 now give the call chain:

`countermodel(p, n, consts, tables)` → `raw(p)`, a separate regex over `uncomment(open(p).read())` with `cnf` clauses closed by `∀` → `holds(f, …)` for each formula. It never calls `problem()`.

We also corrected what the two share. We had written "only the lexer"; in fact the oracle shares three helpers with `cm.py`: the lexer, the `%`-comment stripper and the variable collector. It shares no parser, rewriter or translator.

**Include preprocessing, now a tested boundary.** `bench.expand` is a separate function, and `test_include_expansion` checks that it:
- inlines a plain include, with or without TPTP's optional spaces;
- leaves includes inside `%` and `/* */` comments, and inside quoted names, untouched;
- leaves a selective include in place, which `cm.py` then refuses as unsupported input (`SYN000+2`);
- refuses unresolved, nested and non-`Axioms/` includes, so none is silently dropped.

**Inputs checked against the release.** `test_benchmark_inputs_match_their_sources` checks every input against `bench/inputs.json`: it must equal `bench.expand` applied to its original, byte for byte, and the originals, expansions and axiom files must match their SHA-256s.

**Block comments.** The rebuild also showed that `cm.py` strips only `%` comments. A TPTP `/* … */` comment is now refused rather than read as formulas; none of the 300 benchmark inputs contains one.

**§4.3.** Replaced with your wording: such errors "may be accepted as a different decoded formula list", and detecting the mismatch is the responsibility of the trusted translation and its tests.

## 4. Shallow nonemptiness, now in the statement

You were right that the construction alone did not exclude an empty carrier. The shallow certificate's statement is now

```lean
theorem countermodel : Nonempty T ∧ ⟨balanced conjunction of the formulas⟩ := ⟨⟨T.e1⟩, …⟩
```

The kernel therefore checks nonemptiness like every other conjunct. If a model had no first element, `T.e1` would not exist and the file would not compile. `emit` also refuses a 0-element model before writing anything. The regression test is `test_shallow_certificate_proves_a_nonempty_domain`, and the same applies to the modular `Main`. The reflected path already required `0 < M.n` through `Model.valid`.

## Consistency corrections

| Location | Change |
|---|---|
| §1.2 | "Under five minutes" becomes the 5.2-minute median and its range. The three scaling findings are stated for our measured workloads, generated pattern and Lean 4.13. The evaluation is described as three samples of Satisfiable/CounterSatisfiable problems, not a uniform sample. |
| §9 | "Any first-order theory" becomes "supported untyped first-order inputs for which the finder produces a checkable finite model", with the finder's incompleteness and infinite-only theories stated. |
| §5.1 row 13, §5.2 | The 7.1-fold slice figure is labelled historical and truth-only, and placed beside the controlled 3.2× CPU figure. Greedy ordering is described as starting at the literal with the fewest new variables, a heuristic. |
| §6.3.1 | Largest-process memory: 2.8× on the full problem, 2.0× on the slice. The aggregate is called a *sampled maximum*. Memory pressure and the update service are presented as plausible explanations, not established causes. |
| §7.2, [9] | The obsolete venue qualification is removed: ITP 2026, LIPIcs 382, article 36, whose publisher record lists `vamplean`. |
| §8.2 | The finder row uses the final counts. The Spinoza row now says that a sorted encoding would revise bridges or the signature. |
| §4 introduction | `Checker.lean` is now 430 lines, and the introduction lists the semantic bridge and certificate layer. |
| Abstract, §6.4 | "None of the failures is an invalid certificate" is replaced by your suggested wording, and kept separate from any theorem about the faithfully encoded problem. |
| §3.8 | The trust table gains a row for input preprocessing and states shallow nonemptiness. A truncated sentence is removed. |

## What we did not do

We did not formalize the translator or the include preprocessing, and we did not run a census of TPTP or a new performance study. The paper keeps those as future work, consistent with your "need not block acceptance" section.

Michael Jagdeo and Jeff Dumps
