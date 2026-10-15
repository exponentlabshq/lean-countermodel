## 6. Evaluation and Case Studies

All measurements were taken on one 8 GB, 8-core laptop. Wall-clock times vary by about 2× with system load. Atom counts and verdicts are exact. Lean versions are stated per result.

### 6.1 Case study A: a published Lean formalization (Spinoza's *Ethics*)

**Question.** Nakamura [22] formalizes *Ethics* I in Lean 4 and proves two non-derivability results with hand-built counter-models:

- **S-A12:** A12 does not follow from `StatedAxioms` together with `PSRSubstance`;
- **S-A15:** A15 does not follow from `StatedAxioms` together with plenitude.

Can the tool find these counter-models by itself?

**Method.**

1. **Read** his `Definitions.lean` and `Axioms.lean` at commit 6d4c046.
2. **Transcribe** them into TPTP: primitives become predicates, `def`s become biconditionals, the 8 nontrivial fields of his `StatedAxioms` register become axioms (the register has 12 fields; 4 are `True` placeholders for A3–A6, and the 8 combine stated-axiom content with an exclusivity rider and his bridge axioms A8–A11, so they are not Spinoza's seven axioms one-for-one), the weaker principle is an axiom and the target is the conjecture.
3. **Validate:** the transcription must reproduce his *positive* results first. Weak P5 follows from `StatedAxioms` + `PSRSubstance`, and A15 from `StatedAxioms` + A25 + A26.
4. **Search blind:** run Vampire on his axioms only, without consulting his `A12CounterModel`.
5. **Certify twice:** once on the transcription, and once as instances of his own `EthicaWorld` and `StatedAxioms` classes, checked against his unmodified library (`nakamura/`, pinned to Lean 4.13).

**Results.**

| Claim | His model (hand-built) | Ours (automatic) | Checked against his library |
|---|---|---|---|
| S-A12 | 4 elements (`A12CounterModel`) | **2 elements**, 0.1 s | yes; axioms `[propext]` |
| S-A15 | 3 elements (`A15CounterModel`) | **2 elements**, 0.1 s | yes; axioms `[propext]` |

**The models.**

- **S-A12:** two substances that *share* one attribute and *differ* in another. The sufficient-reason principle holds, and A12 fails. This is the shape of the classic objection to *Ethics* I P5.
- **S-A15:** two gods, one lacking an attribute of the other.

**Caveats.** In our models one object can be both a substance and an attribute. That is not an artifact of the encoding: in Nakamura's reconstruction, A10 makes an attribute conceived through itself and A8 identifies that with being in itself, so any attribute *is* a substance. A sorted encoding that kept the two apart would therefore *conflict* with A8 and A10, not just refine them; it would need a revised signature or revised bridges. Also, his definition of God requires at least one attribute, not infinitely many (his source records the stronger cardinality content as a gap). Our smaller models are an automation result within this reconstruction, not evidence of a more faithful reading of Spinoza.

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

### 6.2 Case study B: a uniform sample of TPTP

**Question.** Does the tool work on problems nobody chose for it? When it fails, is it ever *wrong*?

**Method.**

1. **Index:** from TPTP's ProblemAndSolutionStatistics, keep the 2,561 fof/cnf problems marked Satisfiable or CounterSatisfiable.
2. **Sample** 100 problems, never hand-picked, but **not a uniform sample overall**. The first 20 came from an earlier picker that chose a random *domain*, then a problem in it, which favors problems from small domains. The last 80 were drawn uniformly from the index. The set was also our **development set**: bugs found on it became fixes and regression tests, and it was rerun after each fix. So results on it measure performance on development-exposed problems. §6.2.1 reports a separate held-out set.
3. **Search:** 30 s of Vampire per problem. Results are cached by content, and timeouts are never cached.
4. **Certify** with hybrid dispatch: reflected when at least 90% of formulas are ground facts, shallow otherwise. Lean gets 60 s per file.

Problems were developed in Fibonacci batches (1, 1, 2, 3, 5, 8). Every bug found became a regression example, and after the last fix every problem was rerun with the final compiler.

**Results (Lean 4.13, shallow; the baseline):**

| Outcome | Problems |
|---|---|
| Certified, strict kernel only | 67 |
| Certified with `native_decide` (also trusts Lean's compiler) | 3 |
| Lean rejected (limits, not wrong models) | 6 |
| Vampire found no model within 30 s | 23 |
| `cm.py` error (NLP263, before the quoted-name fixes) | 1 |

**Results.** The first two columns are development history. The **final** column is the frozen implementation (commit `51481a4`: validated reflected certificates, fail-closed parsing, primed variables), run from a separate git worktree on an idle machine with the same 30 s Vampire limit and cache; it is the result this paper reports.

| Outcome | Lean 4.13 (shallow) | Lean 4.35 (hybrid, before review) | **Final, frozen `51481a4`** |
|---|---|---|---|
| Models found by Vampire | 77 | 77 | 77 |
| **Certified, strict kernel only** | 67 | 70 | **70** |
| Certified with `native_decide` | 3 | 2 | 2 |
| Lean rejected | 6 | 5 | 5 |
| Vampire found no model | 23 | 23 | 20 |
| Unsupported input (rejected by the parser) | — | — | 3 |
| `cm.py` error | 1 | 0 | 0 |
| Method | shallow ×100 | shallow ×98, reflected ×2 | shallow ×95, reflected ×2, none ×3 |
| Median end-to-end per problem | 3 s | 0.65 s (Vampire answers cached) | |

**Strict kernel certification: 70 of the 77 models Vampire found (90.9%).** Two more were certified with `native_decide`, which enlarges the trusted base: 72 of 77 (93.5%) including those. Over all 100 problems, the full pipeline succeeds strictly on 70 (70%). These answer different questions, so all three are reported.

| Development subset | Problems | Models found | Strict kernel | + native | Rejected | No model |
|---|---|---|---|---|---|---|
| First 20 (domain-first picker) | 20 | 17 | 17 (100% of models) | 0 | 0 | 2 (+1 unsupported) |
| Last 80 (uniform from the index) | 80 | 60 | 53 (88.3%) | 2 | 5 | 18 (+2 unsupported) |
| All 100 | 100 | 77 | 70 (90.9%) | 2 | 5 | 20 (+3 unsupported) |

The uniformly drawn 80 certify 88.3% strictly, against 17 of 17 for the domain-first 20. That is a descriptive breakdown, not evidence that the picker caused the difference; the established problem is the non-uniform design itself.

Three verdicts changed between the versions:

- **NLP263+1:** a `cm.py` error on 4.13, certified on 4.35 through the reflective checker (§6.3);
- **HWV048-2:** a 16-element model that overflowed the stack on 4.13 now certifies in 2.7 s. This is consistent with Lean 4.33 bounding kernel recursion by `maxRecDepth`;
- **NLP018-10:** needed `native_decide` on 4.13 and certifies kernel-only on 4.35.

**The failures, each explained.** On Lean 4.35, **all 5 rejections are one family:** deeply nested modal-logic encodings (LCL647, LCL659, LCL673, LCL683, LCL685). They fail in Lean's *typeclass instance search* for `Decidable`, within seconds, because the formulas are nested too deeply. None is a wrong model. The reflective checker needs no instance search, so it is the natural route for these (§8). The final run's 5 rejections are the same five problems.

Of the 23 problems that were "no model" before review (20 in the final run; the other 3 are now classified as unsupported input), 11 are rated 1.00 in TPTP: no prover solves them in TPTP's reference evaluations. Three more are very large problems on which Vampire gives up, and the rest time out at 30 s. **Four earlier "no model" results turned out to be our own gap.** Vampire had answered them by deleting unused predicates without printing a model. The flag `-updr off` recovered three of them, and the fourth (NLP263) became case study C.

#### 6.2.1 Held-out evaluation with a frozen implementation

To measure generalization rather than development fit, we drew a **new sample of 100 problems uniformly without replacement** from the 2,461 eligible problems not in the development set, with seed 20261015 (`bench/heldout-sample.json` records the seed, the method and the problem list). The sample was drawn before any held-out result was seen. Each problem got 30 s of Vampire, then hybrid dispatch, from the frozen commit `51481a4` in a separate git worktree, with no code changes during the run.

**Version history, kept rather than hidden.** Three earlier attempts at this run are superseded and not reported. A partial run overlapped with a parser change and was discarded. A run frozen at `1a55aef` crashed on the `include` in `SYN000+2`. A run frozen at `a23fe9c` exposed two harness defects (misclassification of unsupported input as *no model*; a Python integer-printing limit) and a timeout caused by our own concurrent jobs. A run at `62d43d6` exposed the variable-capture defect in `GEG001+1` (§8.2). Its verdicts are otherwise identical to the final run, problem for problem. Superseded logs are kept in `bench/superseded-*.jsonl`.

| Outcome | Held-out (100) | Development (100), same commit |
|---|---|---|
| Unsupported input (rejected by the parser) | 4 | 3 |
| Vampire found no model within 30 s | 35 | 20 |
| **Models found** | **61** | **77** |
| **Certified, strict kernel only** | **54** | **70** |
| Certified with `native_decide` | 2 | 2 |
| Lean rejected (resource limits) | 5 | 5 |
| **Strict, of models found** | **88.5%** | **90.9%** |
| Strict or native, of models found | 91.8% | 93.5% |
| **Full pipeline, strict, of all sampled problems** | **54%** | **70%** |
| Full pipeline, strict, of supported inputs | 54 of 96 (56.3%) | 70 of 97 (72.2%) |

**Reading.** Conditional on Vampire finding a model, strict certification generalizes: 88.5% held-out against 90.9% on the development set. The pipeline as a whole does not reach the development figure: Vampire found a model for 61 held-out problems against 77, so full-pipeline success is 54% against 70%. The difference lies in the finder's yield within 30 s, not in certification. *No model* means only that none was found within the limit; it is not a semantic result.

**Held-out failures.** None is an invalid certificate. Three fail in instance search on deeply nested formulas, the same family as all five development failures: `LCL649+1.015`, `LCL681+1.010`, and `GEG001+1` (an existential over several hundred variables). Two exceed the 60 s Lean limit (`NLP055-1`, `HWV076+1`). The two native-assisted problems are `NLP179+1` and `SWB022+3`. The unsupported inputs are three uses of `<~>` (`KRS182+1`, `KRS199+1`, `KRS210+1`) and one `include` (`SYN000+2`).

### 6.3 Case study C: one million facts (NLP263+1)

NLP263+1 is a natural-language knowledge base: **1,026,857 ground facts over 30 predicates and 383,180 constants**, 70 MB of TPTP. Vampire's model has a single element: every constant denotes it. Checking each fact is therefore trivial, and the problem is pure scale.

The first measurements (Lean 4.13 shallow against Lean 4.35 reflected, single runs, under varying load) suggested about 5× in wall time. Peer review rightly called that comparison uncontrolled, and the reflected certificate has since gained validity and well-formedness checks. §6.3.1 replaces it; the old figures remain only in §5.3, labelled as history.

#### 6.3.1 Controlled comparison

`bench/perf.py` at commit `62d43d6`. Lean 4.35.0; Vampire 5.1.0 answers from the cache; Apple M2, 8 cores, 8 GB, macOS 14.4. Each run is a clean build of the generated certificate with **4 parallel Lean workers for both methods**; the checker library is prebuilt and not timed. Shallow and reflected runs alternate, three repetitions each, on an otherwise idle machine (a macOS update service was active in the background). The reflected timings include the validity and well-formedness checks of §4.4.

| NLP263+1 (1,026,857 facts) | Shallow: median (range) | **Reflected: median (range)** | Ratio of medians |
|---|---|---|---|
| Wall time | 14.1 min (12.6–17.2) | **5.2 min (5.2–5.8)** | 2.7× |
| CPU time | 52.5 min (52.3–55.3) | **20.3 min (20.2–21.0)** | 2.6× |
| Peak memory, largest single process | 1.42 GB (1.28–1.48) | **0.50 GB (0.49–0.51)** | 2.8× |
| Peak memory, all concurrent Lean processes | 2.67 GB (2.67–2.69) | **1.86 GB (1.85–1.87)** | 1.4× |
| Axioms | none | `propext`, `Quot.sound` | |

| 10,000-fact slice of NLP263+1 | Shallow: median (range) | **Reflected: median (range)** | Ratio of medians |
|---|---|---|---|
| Wall time | 10.9 s (9.8–11.4) | **4.4 s (4.1–4.7)** | 2.5× |
| CPU time | 31.1 s (31.0–32.0) | **9.8 s (9.5–10.0)** | 3.2× |
| Peak memory, largest single process | 0.90 GB (0.82–0.96) | **0.46 GB (0.46–0.46)** | 2.0× |
| Peak memory, all concurrent Lean processes | 2.02 GB (1.94–2.12) | **1.33 GB (1.32–1.34)** | 1.5× |

**What this supports.** Under matched conditions, reflection certifies this ground-fact workload about **2.5–3× faster** and with about 3× less memory per process, but only about 1.4× less memory in aggregate. That is roughly half the speedup the uncontrolled comparison suggested. CPU time varies by under 6% across repetitions; shallow wall time varies by 37% (12.6–17.2 min), most likely from memory pressure on an 8 GB machine, since CPU time stays flat. Both problems have one-element models, so these are **throughput stress tests**, not evidence about larger domains or quantifier depth, where reflection is slower (§4.5, §8).

*Definitions* (also stored in each record of `bench/perf.jsonl`). Wall time runs from invoking `cm.py` to the end of the final `#print axioms` check; model search is excluded (cached). CPU time is user plus system time over all child processes. Peak memory is reported two ways: the largest single process's maximum resident set size (`/usr/bin/time -l`), and the largest sum of resident set sizes of concurrently running Lean processes, sampled every 0.2 s. A fresh kernel replay (`leanchecker --fresh`) is timed separately (§3.10), not included.

**How this problem forced the scaling recipe.** It crashed `cm.py`, because of `%` inside a quoted gloss. It then crashed Lean's kernel twice, on a 10,000-long conjunction and on a file with more than about 20,600 declarations. And it exposed a variable-capture hazard, through a constant named `'T'`. Each failure became one of the patterns in §5.

### 6.4 Summary

| | Evidence |
|---|---|
| Generality | Strict certification of 70 of 77 models (development) and 54 of 61 (held-out, frozen code); no failure is a wrong model |
| Scale | 1,026,857 facts certified in a median 5.2 min reflected, against 14.1 min shallow, under matched conditions (§6.3.1) |
| Usefulness on real formal work | Automatic, smaller counter-models for a published Lean formalization |
| Trust | Strict certificates use kernel checks and standard axioms only (2 more native-assisted, reported separately); reflected certificates prove ordinary first-order satisfaction (§4.4); four real bugs in trusted layers caught by independent checks, and two more found during the review: silent misreading of unsupported syntax, and variable capture, which failed closed |
