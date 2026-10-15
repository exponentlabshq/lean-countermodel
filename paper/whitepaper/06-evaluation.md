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

Minimal sufficient sets (greedy deletion, each step a Vampire proof): weak P5 needs {A22} alone; A15 needs {A25, A26}. These are more than leave-one-out results, since leave-one-out alone cannot show that all individually unneeded axioms can be dropped *together*. They also have direct support upstream: Nakamura's own Lean proofs derive weak P5 from `PSRSubstance` and A15 from the two fields of `PSRPlenitude`, neither using `StatedAxioms` (`ModalForm.lean` at 6d4c046).

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

**Results (Lean 4.35, hybrid dispatch; final):**

| Outcome | Lean 4.13 (shallow) | **Lean 4.35 (hybrid)** |
|---|---|---|
| Models found by Vampire | 77 | 77 |
| **Certified, strict kernel only** | 67 | **70** |
| Certified with `native_decide` | 3 | 2 |
| Lean rejected | 6 | **5** |
| Vampire found no model | 23 | 23 |
| `cm.py` error | 1 | 0 |
| Method | shallow ×100 | shallow ×98, reflected ×2 |
| Median end-to-end per problem | 3 s | **0.65 s** (Vampire answers cached) |

**Strict kernel certification: 70 of the 77 models Vampire found (90.9%).** Two more were certified with `native_decide`, which enlarges the trusted base: 72 of 77 (93.5%) including those. Over all 100 problems, the full pipeline succeeds strictly on 70 (70%). These answer different questions, so all three are reported.

| Development subset | Problems | Models found | Strict kernel | + native | Rejected | No model |
|---|---|---|---|---|---|---|
| First 20 (domain-first picker) | 20 | 17 | 17 (100% of models) | 0 | 0 | 3 |
| Last 80 (uniform from the index) | 80 | 60 | 53 (88.3%) | 2 | 5 | 20 |
| All 100 | 100 | 77 | 70 (90.9%) | 2 | 5 | 23 |

The domain-first picker flattered the result: the uniformly drawn 80 certify 88.3% strictly.

Three verdicts changed between the versions:

- **NLP263+1:** a `cm.py` error on 4.13, certified on 4.35 through the reflective checker (§6.3);
- **HWV048-2:** a 16-element model that overflowed the stack on 4.13 now certifies in 2.7 s. This is consistent with Lean 4.33 bounding kernel recursion by `maxRecDepth`;
- **NLP018-10:** needed `native_decide` on 4.13 and certifies kernel-only on 4.35.

**The failures, each explained.** On Lean 4.35, **all 5 rejections are one family:** deeply nested modal-logic encodings (LCL647, LCL659, LCL673, LCL683, LCL685). They fail in Lean's *typeclass instance search* for `Decidable`, within seconds, because the formulas are nested too deeply. None is a wrong model. The reflective checker needs no instance search, so it is the natural route for these (§8).

Of the 23 "no model" problems, 11 are rated 1.00 in TPTP: no prover solves them in TPTP's reference evaluations. Three more are very large problems on which Vampire gives up, and the rest time out at 30 s. **Four earlier "no model" results turned out to be our own gap.** Vampire had answered them by deleting unused predicates without printing a model. The flag `-updr off` recovered three of them, and the fourth (NLP263) became case study C.

#### 6.2.1 Held-out evaluation with a frozen implementation

To measure generalization rather than development fit, we froze the implementation (commit `a2c16ab`) and drew a **new sample of 100 problems uniformly without replacement** from the 2,461 eligible problems not in the development set, with seed 20261015 (`bench/heldout-sample.json` records the seed, the method and the problem list). Each problem got 30 s of Vampire, then hybrid dispatch, with no code changes.

{{HELDOUT_TABLE}}

### 6.3 Case study C: one million facts (NLP263+1)

NLP263+1 is a natural-language knowledge base: **1,026,857 ground facts over 30 predicates and 383,180 constants**, 70 MB of TPTP. Vampire's model has a single element: every constant denotes it. Checking each fact is therefore trivial, and the problem is pure scale.

| | Shallow (Lean 4.13) | **Reflected (Lean 4.35)** | Gain |
|---|---|---|---|
| Wall time | 20.7 min | **4.8 min** | 4.3× |
| CPU time | 54 min | 17.5 min | 3.1× |
| Peak memory | 1.64 GB | 0.50 GB | 3.3× |
| Generated Lean | 178 MB | 25 MB | 7× |
| Build output | 2.0 GB | 65 MB | 31× |
| Modules | 555 | 253 | |
| Failed modules | 0 | 0 | |
| Axioms | none | `propext`, `Quot.sound` | |
| Statement | 1,026,857 Lean propositions | `Holds M problem` | |

**Same Lean version.** Shallow on Lean 4.35 took 23.7 min wall, 51 min CPU and 1.46 GB, again with 0 failures and no axioms. Its last two steps overlapped with other work on the machine, which inflated its wall time; its chunk phase alone took 12.8 min, against 4.8 min for the whole reflected build. Under these conditions we **observed** reflection to be about 5× faster in wall time, with about 3× less CPU and 3× less peak memory. That is an observed ratio, not a controlled estimate: runs were single, on a laptop whose wall times vary by about 2× with load. §6.3.1 repeats the comparisons under quiescent load.

*Definitions.* Wall time is the elapsed time of the whole build script, from generating Lean to the final `#print axioms` check, with models taken from Vampire's cache. CPU time is user plus system time over all processes. **Peak memory is the largest single process's maximum resident set size** (`/usr/bin/time -l`), not the total across concurrently running processes: with 3–4 parallel Lean processes, the aggregate is higher.

**How this problem forced the scaling recipe.** It crashed `cm.py`, because of `%` inside a quoted gloss. It then crashed Lean's kernel twice, on a 10,000-long conjunction and on a file with more than about 20,600 declarations. And it exposed a variable-capture hazard, through a constant named `'T'`. Each failure became one of the patterns in §5.

### 6.4 Summary

| | Evidence |
|---|---|
| Generality | 72 of 77 models certified (70 kernel-only) on a 100-problem TPTP sample; no failure is a wrong model |
| Scale | 1,026,857 facts certified in 4.8 min (reflected) |
| Usefulness on real formal work | Automatic, smaller counter-models for a published Lean formalization |
| Trust | Strict certificates use kernel checks and standard axioms only (2 more native-assisted, reported separately); reflected certificates prove ordinary first-order satisfaction (§4.4); four real bugs in trusted layers caught by independent checks, and a fifth class (silent misreading of unsupported syntax) closed after peer review |
