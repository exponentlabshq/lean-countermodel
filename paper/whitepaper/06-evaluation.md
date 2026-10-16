## 6. Evaluation and Case Studies

All measurements were taken on one 8 GB, 8-core laptop. Wall-clock times vary by about 2× with system load. Atom counts and verdicts are exact. Lean versions are stated per result.

### 6.1 Case study A: a published Lean formalization (Spinoza's *Ethics*)

**Question.** Nakamura [22] formalizes *Ethics* I in Lean 4 and proves two non-derivability results with hand-built counter-models:

- **S-A12:** A12 does not follow from `StatedAxioms` together with `PSRSubstance`;
- **S-A15:** A15 does not follow from `StatedAxioms` together with plenitude.

Can the tool find these counter-models by itself?

**Method.**

1. **Read** their `Definitions.lean` and `Axioms.lean` at commit 6d4c046.
2. **Transcribe** them into TPTP: primitives become predicates, `def`s become biconditionals, the 8 nontrivial fields of their `StatedAxioms` register become axioms (the register has 12 fields; 4 are `True` placeholders for A3–A6, and the 8 combine stated-axiom content with an exclusivity rider and their bridge axioms A8–A11, so they are not Spinoza's seven axioms one-for-one), the weaker principle is an axiom and the target is the conjecture.
3. **Validate:** the transcription must reproduce their *positive* results first. Weak P5 follows from `StatedAxioms` + `PSRSubstance`, and A15 from `StatedAxioms` + A25 + A26.
4. **Search blind:** run Vampire on their axioms only, without consulting their `A12CounterModel`.
5. **Certify twice:** once on the transcription, and once as instances of their own `EthicaWorld` and `StatedAxioms` classes, checked against their unmodified library (`nakamura/`, pinned to Lean 4.13).

**Results.**

| Claim | Nakamura's model (hand-built) | Ours (automatic) | Checked against their library |
|---|---|---|---|
| S-A12 | 4 elements (`A12CounterModel`) | **2 elements**, 0.1 s | yes; axioms `[propext]` |
| S-A15 | 3 elements (`A15CounterModel`) | **2 elements**, 0.1 s | yes; axioms `[propext]` |

**The models.**

- **S-A12:** two substances that *share* one attribute and *differ* in another. The sufficient-reason principle holds, and A12 fails. This is the shape of the classic objection to *Ethics* I P5.
- **S-A15:** two gods, one lacking an attribute of the other.

**Caveats.** In our models one object can be both a substance and an attribute. That is not an artifact of the encoding: in Nakamura's reconstruction, A10 makes an attribute conceived through itself and A8 identifies that with being in itself, so any attribute *is* a substance. A sorted encoding that kept the two apart would therefore *conflict* with A8 and A10, not just refine them; it would need a revised signature or revised bridges. Also, their definition of God requires at least one attribute, not infinitely many (their source records the stronger cardinality content as a gap). Our smaller models are an automation result within this reconstruction, not evidence of a more faithful reading of Spinoza.

#### 6.1.1 The assumption-dependency map

`ablate.py` asks, for each target proposition, whether it follows from the full register, and then, for each axiom, whether it still follows without it. "Needed" means that removing the axiom yields a finite counter-model, **certified by Lean's kernel**. "Not needed" means Vampire still proves the target; that rests on a Vampire proof, which is not certified here. The definitions of substance, attribute and God are held fixed throughout. The run covers 36 experiments, takes 105 s, and is recorded in `ablation/`.

| Without ↓ / target → | weak P5 | A12 | A15 |
|---|---|---|---|
| *(nothing removed)* | follows | **does not follow** (2-element model) | follows |
| any of the 8 stated axioms | not needed | still does not follow | not needed |
| A22 (sufficient reason for substances) | **needed** (2-element model) | still does not follow | not needed |
| A25 (plenitude) | not needed | still does not follow | **needed** (2-element model) |
| A26 (God is unique) | not needed | still does not follow | **needed** (2-element model) |

**Subset-minimal** sufficient sets (greedy deletion, each step a Vampire proof; this finds *a* minimal set, not necessarily a smallest or the only one, and a Vampire timeout would leave minimality unresolved): weak P5 needs {A22} alone; A15 needs {A25, A26}. These are more than leave-one-out results, since leave-one-out alone cannot show that all individually unneeded axioms can be dropped *together*. They also have direct support upstream: Nakamura's own Lean proofs derive weak P5 from `PSRSubstance` and A15 from the two fields of `PSRPlenitude`, neither using `StatedAxioms` (`ModalForm.lean` at 6d4c046).

**Findings:**

1. **None of the eight nontrivial fields of Nakamura's stated-axiom register is needed for these results.** Relative to the fixed definitions, the logical work is done by the added sufficient-reason principles. This is a precise form of the Bennett–Della Rocca question for this reconstruction.
2. **A12 is irreducible even against the whole register.** Nakamura shows A12 does not follow from `StatedAxioms` + A22. A certified 2-element model shows it also fails with plenitude (A25) and God's uniqueness (A26) added.
3. **The "needed" results confirm Nakamura's positive Lean proofs** (weak P5 from A22; A15 from A25 + A26) and show that each premise in them is necessary. A counter-model shows non-derivability, not full independence. Independence would also need the negation to be non-derivable, which we do not test. Both claims rest on the soundness of first-order logic, not on any internal Lean theorem about consistency.

**Caveats:**

- This is the first-order layer of the register only, not its S5 modal layer.
- "Not needed" rests on uncertified Vampire proofs.
- As in §6.1, the counter-models let one object be both a substance and an attribute, which the register permits.

### 6.2 Case study B: three samples of TPTP

**Question.** Does the tool work on problems nobody chose for it? When it fails, is it ever *wrong*?

**Method.**

1. **Index:** from TPTP's ProblemAndSolutionStatistics, keep the 2,561 fof/cnf problems marked Satisfiable or CounterSatisfiable.
2. **Sample** 100 problems, never hand-picked, but **not a uniform sample overall**. The first 20 came from an earlier picker that chose a random *domain*, then a problem in it, which favors problems from small domains. The last 80 were drawn uniformly from the index. The set was also our **development set**: bugs found on it became fixes and regression tests, and it was rerun after each fix. So results on it measure performance on development-exposed problems. §6.2.1 reports two further uniform samples.
3. **Search:** 30 s of Vampire per problem. Results are cached by content, and timeouts are never cached.
4. **Certify** with hybrid dispatch: reflected when at least 90% of formulas are ground facts, shallow otherwise. **Budgets** (`bench.py`): a shallow certificate gets 60 s for its single file with `decide`; if that times out, a second 60 s attempt with `native_decide`, reported separately as native-assisted. A one-file reflected certificate gets 60 s. A modular reflected certificate gets 600 s for each module (Base, each Part, Main), with four Parts built in parallel and no cap on the total; NLP263+1 is the only problem that used it.

Problems were developed in Fibonacci batches (1, 1, 2, 3, 5, 8). Every bug found became a regression example, and after the last fix every problem was rerun with the final compiler.

**Results (Lean 4.13, shallow; the baseline):**

| Outcome | Problems |
|---|---|
| Certified, strict kernel only | 67 |
| Certified with `native_decide` (also trusts Lean's compiler) | 3 |
| Lean rejected (limits, not wrong models) | 6 |
| Vampire found no model within 30 s | 23 |
| `cm.py` error (NLP263, before the quoted-name fixes) | 1 |

**Inputs.** Every benchmark input is rebuilt from the official TPTP v9.3.1 release (`bench/inputs.py`; tarball SHA-256 in `bench/inputs.json`), with includes expanded by the tested `bench.expand` (§3.8). The rebuild found a defect in the earlier scraped inputs: two of them, `RNG025-9` (development) and `BOO008-3` (second sample), contain an include that the TPTP file comments out (`% include('Axioms/…').`), and the old expander had inlined it, adding the axiom file's clauses to the problem (40 against 25 and 43 against 21 `cnf` lines). Both had been reported as *no model*. On their correct inputs Vampire finds models of 3 and 2 elements, and both are now certified. Two benchmark no-model-found outcomes concerned altered inputs and are superseded by the corrected runs; the defect produced no certificate.

**Results.** The first two columns are development history. The **final** column is the repaired implementation at commit `66c8b32`: validated reflected certificates, fail-closed parsing, primed variables, `Nonempty T` in shallow statements, inputs from the TPTP release, and total record reading (§6.2.2). It was run from a separate git worktree with the same 30 s Vampire limit, and it is the result this paper reports. That rerun was not an idle-machine execution (§6.2.2).

| Outcome | Lean 4.13 (shallow) | Lean 4.35 (hybrid, before review) | **Final, `66c8b32`** |
|---|---|---|---|
| Models found by Vampire | 77 | 77 | 78 |
| **Certified, strict kernel only** | 67 | 70 | **71** |
| Certified with `native_decide` | 3 | 2 | 2 |
| Lean rejected | 6 | 5 | 5 |
| Vampire found no model | 23 | 23 | 19 |
| Unsupported input (rejected by the parser) | — | — | 3 |
| `cm.py` error | 1 | 0 | 0 |
| Method | shallow ×100 | shallow ×98, reflected ×2 | shallow ×95, reflected ×2, none ×3 |
| Median end-to-end per problem | 3 s | 0.65 s (Vampire answers cached) | |

**Strict kernel certification: 71 of the 78 models Vampire found (91.0%).** Two more were certified with `native_decide`, which enlarges the trusted base: 73 of 78 (93.6%) including those. Over all 100 problems, the full pipeline succeeds strictly on 71 (71%). These answer different questions, so all three are reported.

| Development subset | Problems | Models found | Strict kernel | + native | Rejected | No model |
|---|---|---|---|---|---|---|
| First 20 (domain-first picker) | 20 | 17 | 17 (100% of models) | 0 | 0 | 2 (+1 unsupported) |
| Last 80 (uniform from the index) | 80 | 61 | 54 (88.5%) | 2 | 5 | 17 (+2 unsupported) |
| All 100 | 100 | 78 | 71 (91.0%) | 2 | 5 | 19 (+3 unsupported) |

The uniformly drawn 80 certify 88.5% strictly, against 17 of 17 for the domain-first 20. That is a descriptive breakdown, not evidence that the picker caused the difference; the established problem is the non-uniform design itself.

Four verdicts changed between the versions:

- **NLP263+1:** a `cm.py` error on 4.13, certified on 4.35 through the reflective checker (§6.3);
- **HWV048-2:** a 16-element model that overflowed the stack on 4.13 now certifies in 2.7 s. This is consistent with Lean 4.33 bounding kernel recursion by `maxRecDepth`;
- **NLP018-10:** needed `native_decide` on 4.13 and certifies kernel-only on 4.35;
- **RNG025-9:** *no model* on the altered input, certified on the release input (above).

**The failures, each explained.** On Lean 4.35, **all 5 rejections are one family:** deeply nested modal-logic encodings (LCL647, LCL659, LCL673, LCL683, LCL685). They fail in Lean's *typeclass instance search* for `Decidable`, within seconds, because the formulas are nested too deeply. The reflective checker needs no instance search, so it is the natural route for these (§8).

Of the 19 problems with no model in the final run, 10 are rated 1.00 in TPTP: no prover solves them in TPTP's reference evaluations. *No model* means only that none was found within 30 s; it is not a semantic result. **Four earlier "no model" results turned out to be our own gap.** Vampire had answered them by deleting unused predicates without printing a model. The flag `-updr off` recovered three of them, and the fourth (NLP263) became case study C.

#### 6.2.1 The second and third samples

**Second sample: initially held out, then used for debugging.** We drew 100 problems uniformly without replacement from the 2,461 eligible problems not in the development set, with seed 20261015 (`bench/heldout-sample.json`), before any result on them was seen. We then used it: earlier runs on it exposed a crash on `include` (`1a55aef`), two harness defects and a load-induced timeout (`a23fe9c`), and the variable-capture defect in `GEG001+1` (`62d43d6`); the input rebuild then changed `BOO008-3`. Each was fixed before the final run. These are general defects, not tuning to particular problems, but the sample's results did inform the implementation, so **we report the second sample as a descriptive validation sample, not as an untouched test of generalization.** Superseded logs are kept in `bench/superseded-*.jsonl`.

**Third sample: drawn and frozen before any result.** We drew 100 further problems uniformly without replacement, seed 20261016, from the 2,357 eligible problems in neither earlier set nor among four exploratory problems used during development (`bench/third-sample.json`). The list was committed together with the frozen code (`900818d`) before any result on it existed. Two launches did not complete, and both are recorded:

1. At `900818d`, the run stopped on its first development certificate because a fresh worktree lacked an output directory; `acb343b` creates it. No third-sample problem had been reached.
2. At `acb343b`, the development and second samples completed, and the third stopped when `KRS290-1`, whose formulas nest deeper than Python's recursion limit, raised an exception the harness did not catch. No third-sample verdict was written. Before it stopped, the run had already run Vampire on the third-sample problems it reached, and may have compiled certificates for some; the Vampire answers stayed in the content-addressed cache, and we did not inspect them or any intermediate result. To locate the crash, we reran only the translator's pre-check on the third sample; it showed that `KRS290-1` was the only problem raising the exception (`bench/superseded-acb343b-third-attempt1.txt`).

The one change made after that, `30ad4f3`, is in the harness: any translator exception is now recorded as a *cm.py error* instead of stopping the run. `cm.py`, `Checker.lean`, the dispatch rule, the time limits and the inputs did not change, so `KRS290-1` is reported as a failure, not repaired. The third sample was then run in full at `30ad4f3`. It is therefore not strictly untouched: one piece of information from it, that a problem crashes the pre-check, led to a harness change.

**All three samples were then rerun after the round-4 repair** (§6.2.2), which peer review prompted by auditing the code, not by any sample's results. That repair changed what three third-sample inputs mean to the translator. **The reported results are therefore a corrected evaluation on samples that have all been exposed to development**, with the original sampling design retained. On the third sample, selected before its first execution, the solver and translator stayed frozen until the round-4 repair; a harness-only change after an aborted attempt recorded translator exceptions as failures. The completed evaluation strictly certified 59 of 67 found models.

| Outcome | Development (100) | Second sample (100) | **Third sample (100)** |
|---|---|---|---|
| Unsupported input (rejected by the parser) | 3 | 4 | 3 |
| Translator crash before a model outcome (`KRS290-1`) | 0 | 0 | 1 |
| Vampire found no model within 30 s | 19 | 34 | 29 |
| **Models found** | **78** | **62** | **67** |
| **Certified, strict kernel only** | **71** | **55** | **59** |
| Certified with `native_decide` | 2 | 2 | 3 |
| Lean rejected (time or instance-search limits) | 5 | 5 | 4 |
| Model found, certificate generation crashed (`SYO595-1`)¹ | 0 | 0 | 1 |
| **Strict, of models found** | **91.0%** | **88.7%** | **88.1%** |
| Strict or native, of models found | 93.6% | 91.9% | 92.5% |
| **Full pipeline, strict, of all sampled problems** | **71%** | **55%** | **59%** |
| Full pipeline, strict, of supported inputs | 71 of 97 (73.2%) | 55 of 96 (57.3%) | 59 of 97 (60.8%) |

All three samples at commit `66c8b32`. The rows are mutually exclusive and each column sums to 100; models found = strict + native + Lean rejected + generation crash.
¹ `SYO595-1` and `KRS290-1` are the two *cm.py error* records of the third sample: one after a model was found, one before any model outcome. Both stay in the supported-input denominator.

**Reading.** On the third sample, the repaired implementation strictly certified 59 of the 67 models Vampire found (88.1%), against 91.0% on the development set and 88.7% on the second sample. The conditional rates are similar; three samples of this size do not establish that they are equal. Full-pipeline success differs more (71%, 55%, 59%), and that difference coincides mainly with how many problems Vampire found a model for within 30 s (78, 62, 67), not with certification. These are descriptive results; the second and third samples are uniform samples of the eligible problems, while the development set is not.

**Failures, each listed.**

- **Lean rejected.** Development: the five LCL instance-search failures above. Second sample: `LCL649+1.015`, `LCL681+1.010` and `GEG001+1` fail in instance search on deeply nested formulas; `NLP055-1` and `HWV076+1` exceed the 60 s Lean limit. Third sample: `LCL663+1.010` and `LCL649+1.020` fail in instance search; `NLP213+1` exceeds 60 s; and `ALG310-1`, native-assisted in round 3 (54.8 s against the 60 s limit), exceeded the native limit in this rerun.
- **Native-assisted** (seven in all, reported separately from strict certificates). Development: `ALG306-1`, `ALG334-1`. Second: `NLP179+1`, `SWB022+3`. Third: `NLP016+1`, `NLP186+1`, `NLP243+1`.
- **Unsupported input.** Development: `BIO001+1`, `HWV042+1`, `KRS244+1`. Second: `<~>` in `KRS182+1`, `KRS199+1`, `KRS210+1`, and `SYN000+2`, which uses the role `unknown` and a selective include. Third: `<~>` in `KRS224+1`, `KRS249+1`, `HWV105+1`.
- **Translator crashes (third sample).** `KRS290-1`: formula nesting exceeds Python's recursion limit in `cm.py`'s recursive-descent translator. `SYO595-1`: Vampire found a model, but the problem has more than 2,000 formulas, so `cm.py` emits a multi-module certificate, and the benchmark's shallow path calls it without the output directory that requires; it crashes before writing the certificate. Both are limitations of the implementation as evaluated, reported rather than fixed (§8.2).

**Why no model was found.** Two kinds of *no model* outcome occur, and both are search outcomes. Most are timeouts at 30 s: Vampire 5.1 reports `Termination reason: Time limit`. The rest are fast give-ups (`SZS status GaveUp`, "Cannot represent all propositional literals internally"): the problem exceeds the finite-model builder's internal encoding. Of the 82 across the three samples (19, 34 and 29), the TPTP headers say that 18 have no finite model at all (4, 8 and 6: "Has only infinite models", "No finite models", or Infinox's verdict), so no finite-model finder can succeed on them. GRP773-1's smallest model has 64 elements. Nine are encoding give-ups (PLA041-1, SYN832-1; SYO593-1, SYN817-1, KRS281-1; SYN821-1, SYO603+1, SYN864-1, HWV070+1). The other 54 timed out without a documented cause; 28 of them are rated 1.00 by TPTP, meaning no prover solved them in TPTP's reference runs. *No model* means only that none was found within the limit; it is not a semantic result.

#### 6.2.2 Round-4 repair: record omission, and what it changed

**The defect.** Peer review audited the delivered code and showed that `cm.py` found records with a regular expression that *searched* the file. A record it could not match was skipped without error: a quoted name with punctuation, or a comment or whitespace between `fof` and `(`. The test oracle had copied that expression, so it agreed with the translator on the weakened problem. With two contradictory two-record files and a deliberately wrong model of only the surviving record, both certificate paths accepted it. Records are now read by the total, fail-closed `statements` (§3.3), the oracle has its own reader (§3.10), and those two files are regressions that both paths must reject.

**Its effect on the benchmark** (`bench/compare_parsers.py`, `bench/parser-comparison.json`):
- **297 of the 316 inputs read identically.** These are the 300 benchmark problems, the 15 examples and the ablation theory; the 297 include NLP263+1, compared as an exact list of 1,026,857 records.
- **10 are rejected by both versions.**
- **9 changed.** Each has quoted record names with punctuation (`'EQ-var'`, `'thm.bool.TRUTH'`): `COM150+1` (28 → 60 records) and eight SWW problems (5 → 10 to 44). `COM150+1` had been *no model*, which stands, since Vampire read the full file. **Eight earlier certificates omitted source premises and were withdrawn:** `SWW883+1` (development), `SWW882+1`, `SWW902+1`, `SWW938+1`, `SWW942+1` (second), and `SWW865+1`, `SWW889+1`, `SWW921+1` (third). **The repaired pipeline subsequently certified their complete source problems**, each with a 2- or 3-element model. Unchanged strict totals do not validate the superseded certificates. One previously native-assisted result, `ALG310-1`, timed out in the rerun and is reported as a failure.

**Running the rerun.** The first rerun, at `8d46e97`, required an SZS status from Vampire. Vampire 5.1 reports a timeout without one, so that run labelled its 17 development timeouts *finder error*. We stopped it after the development sample and kept the partial ledger (`bench/superseded-8d46e97-dev-timeout-misclassified.jsonl`). `66c8b32` also accepts Vampire's termination reason, and all three samples were rerun there. A row-by-row comparison (`bench/timeout-correction-comparison.json`) finds exactly those 17 rows different, all *finder error* → *no model*; the other 83, including all 71 strict certificates, are identical, and the models-found denominator is 78 in both. All three samples were rerun with a background process occupying one CPU core: an orphaned worker of our own parse comparison, found and stopped afterwards. Strict certification totals were unchanged. `ALG310-1` exceeded the native-assisted time limit; background contention may have contributed, but causation was not established. The timeout is retained in the reported outcomes, and this load qualification does not apply to the controlled timings of §6.3.1.

**Source-fidelity coverage of every certified result** (`bench/coverage.py`, `bench/coverage.md`). Each check is reported separately, and *unchecked* means neither verified nor failed.

For every one of the 192 certified results, the test oracle reads the **original** problem file with its own record reader and evaluates every original formula, by brute force, in the model Lean certified (`bench/fidelity.py`, cap 300 s per problem).

| | Strict (185) | Native-assisted (7) |
|---|---|---|
| Original-formula satisfaction | **184 faithful**, 1 unchecked | 5 faithful, 2 unchecked |
| Rewrite agreement (below) | 176 agree, 9 unchecked | 4 agree, 3 unchecked |
| Compilation and fresh kernel replay | **185 passed** | not replayed (see below) |
| Failed, in any check | **0** | **0** |

Three results are **unchecked** for original-formula satisfaction, because brute-force evaluation of their original formulas did not finish in 300 s:
- `NLP219-1` (development, strict);
- `NLP179+1` (second sample, native-assisted);
- `NLP186+1` (third sample, native-assisted).

For these three, two supplementary checks are reported separately and do **not** establish that the original formulas hold. First, record identity: `cm.statements` and the oracle's reader consume the whole file and agree record by record on kind, name, role and formula tokens (124, 67 and 67 records). Second, satisfaction of the rewritten formulas: the oracle confirmed it for `NLP179+1`, while it was unchecked at 300 s for `NLP219-1` and `NLP186+1`. An independent clause-search evaluator, validated against the brute-force one on every small structure, also did not finish on `NLP219-1` within 10 minutes. **Original-formula satisfaction of these three results therefore remains unchecked, so the source-fidelity claim covers 189 of the 192 certified results.** `bench/coverage.md` lists every exception with all its checks.

**Bounded validation of the rewrite.**
- **Adversarial forms.** On 18 hand-written formulas (15 `fof`, 3 `cnf`) covering independent variables, a shadowed variable name, ∀ moved across ∨, implication flattening, vacuous quantification, ∃ under ∀, equality, negated conjunction, an equivalence that must not be flattened, and transitivity clauses, the original and rewritten formulas agree on every interpretation of the signature (constants `a`, `b`; unary `p`, `q`; binary `r`) over domains of size 1 and 2. That is 8 + 1,024 = 1,032 structures per formula, 18,576 comparisons in all (`test_rewriting_is_equivalent_on_every_small_structure`). A deliberately wrong rewrite (a variable replaced by a constant) disagrees on 156 of the 1,032.
- **Benchmark.** `bench/rewrite_check.py` pairs every source record (read by the oracle) with its rewritten formula, for every problem where a model was found, and compares each rewritten formula with its original on the model, up to 50 one-entry mutations and 10 random structures of the same signature (domains of 1 to 3 elements). Of the 206 problems with a found model, **192 were checked in full**: 7,165 rewritten formulas (out of 1,036,470 formulas in those problems), 364,181 original-against-rewritten evaluations (7,165 on the models, 285,366 on mutations, 71,650 on random structures), **0 disagreements**. **14 are unchecked** at the 60 s cap per problem, because brute-force evaluation of their original formulas is too slow: 9 with strict certificates (`NLP184-1`, `NLP219-1`, `SWB017+3`, `SWB023+3` in development; `NLP192-1`, `NLP199-1`, `SWB007+3` in the second sample; `NLP238-1`, `SWB025+3` in the third), 3 native-assisted (`ALG306-1`, `ALG334-1`, `SWB022+3`) and 2 Lean-rejected (`NLP055-1`, `ALG310-1`) (`bench/rewrite-check.jsonl`).

This is exhaustive within the stated finite test space and bounded validation on the benchmark, not a proof that the rewrite preserves meaning.

**Fresh replay of the strict benchmark certificates.** `bench/replay.py` recompiled every strict certificate of the rerun as a Lean module, printed `#print axioms` for each `countermodel`, and replayed one aggregate module per sample from scratch with `leanchecker --fresh`, imports included (Lean 4.35, same laptop). **All 185 compiled and passed:** development 71 in 910 s, including the million-fact NLP263+1 certificate; second sample 55 in 47 s; third sample 59 in 55 s (`bench/replay.log`, `bench/replay-{dev,second,third}.jsonl`; `replay.py` exited 0). Axioms: `propext` for 182, `propext` and `Quot.sound` for the two reflected certificates (NLP263+1 and AGT042+1), and none for `SYN092-1.003`. The seven native-assisted certificates are not replayed: replay cannot validate their compiled-code axioms, so they stay a separate, weaker category. `leanchecker --fresh` replays through Lean's own kernel; it is not an independent kernel implementation. A successful replay shows that the kernel accepts the emitted statements; it says nothing about whether those statements are faithful to the source, which the fidelity check above addresses.

### 6.3 Case study C: one million facts (NLP263+1)

NLP263+1 is a natural-language knowledge base: **1,026,857 ground facts over 30 predicates and 383,180 constants**, 70 MB of TPTP. Vampire's model has a single element: every constant denotes it. Checking each fact is therefore trivial, and the problem is pure scale.

The first measurements (Lean 4.13 shallow against Lean 4.35 reflected, single runs, under varying load) suggested about 5× in wall time. Peer review rightly called that comparison uncontrolled, and the reflected certificate has since gained validity and well-formedness checks. §6.3.1 replaces it; the old figures remain only in §5.3, labelled as history.

#### 6.3.1 Controlled comparison

`bench/perf.py` at commit `62d43d6`. Lean 4.35.0; Vampire 5.1.0 answers from the cache; Apple M2, 8 cores, 8 GB, macOS 14.4. Each run is a clean build of the generated certificate with **4 parallel Lean workers for both methods**; the checker library is prebuilt and not timed. Shallow and reflected runs alternate, three repetitions each, on an otherwise idle machine (a macOS update service was active in the background). The reflected timings include the validity and well-formedness checks of §4.4.

**Version.** The timings were taken at `62d43d6`. Regenerated with the final evaluation code (`cm.py` as at `66c8b32`) from the same cached Vampire model, **all 253 reflected modules of NLP263+1 are byte-identical** to the timed ones. Of the 555 shallow modules, 40 are byte-identical and 515 differ. They differ only by the round-4 renaming of the emitter's helper declarations (`c_i`, `P_i`, `C_j`, `chunk_j` gain a prime) and, in `Main.lean`, the `Nonempty T` conjunct (§3.5). Applying exactly that renaming to the timed output makes all 555 byte-identical (`bench/perf-equivalence.json`). The reflected timing therefore measured exactly the certificate the final code produces; the shallow timing measured a certificate that differs by those changes, which were not re-timed, and whose cost we have not measured. The rebuilt input differs from the timed one only by trailing blank lines.

| NLP263+1 (1,026,857 facts) | Shallow: median (range) | **Reflected: median (range)** | Ratio of medians |
|---|---|---|---|
| Wall time | 14.1 min (12.6–17.2) | **5.2 min (5.2–5.8)** | 2.7× |
| CPU time | 52.5 min (52.3–55.3) | **20.3 min (20.2–21.0)** | 2.6× |
| Peak memory, largest single process | 1.42 GB (1.28–1.48) | **0.50 GB (0.49–0.51)** | 2.8× |
| Sampled maximum memory, all concurrent Lean processes | 2.67 GB (2.67–2.69) | **1.86 GB (1.85–1.87)** | 1.4× |
| Axioms | none | `propext`, `Quot.sound` | |

| 10,000-fact slice of NLP263+1 | Shallow: median (range) | **Reflected: median (range)** | Ratio of medians |
|---|---|---|---|
| Wall time | 10.9 s (9.8–11.4) | **4.4 s (4.1–4.7)** | 2.5× |
| CPU time | 31.1 s (31.0–32.0) | **9.8 s (9.5–10.0)** | 3.2× |
| Peak memory, largest single process | 0.90 GB (0.82–0.96) | **0.46 GB (0.46–0.46)** | 2.0× |
| Sampled maximum memory, all concurrent Lean processes | 2.02 GB (1.94–2.12) | **1.33 GB (1.32–1.34)** | 1.5× |

**What this supports.** Under matched conditions, reflection certifies this ground-fact workload about **2.5–3× faster**. Its largest single process uses about 2.8× less memory on the full problem (1.42/0.50 GB) and about 2.0× less on the slice (0.90/0.46 GB); summed over concurrent Lean processes, the sampled maximum is only about 1.4–1.5× lower. The speedup is roughly half what the uncontrolled comparison suggested. CPU time varies by under 6% across repetitions, while shallow wall time varies by 37% (12.6–17.2 min). Memory pressure on an 8 GB machine and the background update service are plausible explanations for that spread; we did not record the system measurements that would establish either. Both problems have one-element models, so these are **throughput stress tests**, not evidence about larger domains or quantifier depth, where reflection is slower (§4.5, §8).

*Definitions* (also stored in each record of `bench/perf.jsonl`). Wall time runs from invoking `cm.py` to the end of the final `#print axioms` check; model search is excluded (cached). CPU time is user plus system time over all child processes. Memory is reported two ways: the largest single process's maximum resident set size (`/usr/bin/time -l`, an exact peak per process), and the largest sum of resident set sizes of concurrently running Lean processes, sampled every 0.2 s (a sampled maximum, which can miss a shorter peak). A fresh kernel replay (`leanchecker --fresh`) is timed separately (§3.10), not included.

**How this problem forced the scaling recipe.** It crashed `cm.py`, because of `%` inside a quoted gloss. It then crashed Lean's kernel twice, on a 10,000-long conjunction and on a file with more than about 20,600 declarations. And it exposed a variable-capture hazard, through a constant named `'T'`. Each failure became one of the patterns in §5.

### 6.4 Summary

| | Evidence |
|---|---|
| Generality | Strict certification of 71 of 78 models (development), 55 of 62 (second sample) and 59 of 67 (third sample), at one commit after the round-4 repair; 2, 2 and 3 more native-assisted, reported separately. All three samples have been exposed to development, so these are descriptive results. Uncertified models produced no certificate; two third-sample inputs crashed the translator (§6.2.1) |
| Scale | 1,026,857 facts certified in a median 5.2 min reflected, against 14.1 min shallow, under matched conditions (§6.3.1) |
| Usefulness on real formal work | Automatic, smaller counter-models for a published Lean formalization |
| Trust | Strict certificates use kernel checks and standard axioms only (7 more native-assisted across the three samples, reported separately); reflected certificates prove ordinary first-order satisfaction (§4.4); four real bugs in trusted layers caught by independent checks, and three more found during the review: silent misreading of unsupported syntax; variable capture, which failed closed; and include expansion inside comments, which changed two inputs and made two benchmark no-model-found outcomes concern altered inputs (superseded by the corrected runs). An artifact audit in round 4 found that the record reader could skip a legal record: eight certificates had omitted source premises and were withdrawn; the repaired pipeline certified their complete source problems, and every certified result is now checked against its original source file (§6.2.2) |
