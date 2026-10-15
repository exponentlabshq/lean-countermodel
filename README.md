# lean-countermodel

**Kernel-checked finite counter-models for Lean 4, found by Vampire.**

> To show that some axioms do **not** imply a claim, you exhibit a world where the axioms hold and the claim fails.
> Vampire finds such a world automatically. `cm.py` turns it into a Lean 4 certificate, and Lean's kernel checks it.
> Vampire is untrusted: a model that is ill-formed or falsifies the encoded problem yields no certificate.
> The translation from TPTP into Lean is trusted code, tested against an independent evaluator of the original formulas.

```
python3 cm.py examples/group_comm.p > G.lean && lake env lean G.lean             # one theorem per formula
python3 cm.py --reflect examples/group_comm.p > G.lean && lake env lean G.lean   # through the verified checker
```

**Authors:** Michael Jagdeo, Exponent Labs LLC · Jeff Dumps. **Whitepaper:** [`paper/whitepaper.md`](paper/whitepaper.md) covers the method, data structures, scaling recipe, evaluation and related work.

---

## 1. Results at a glance

| Claim | Evidence |
|---|---|
| **Works on independent problems** | Development set of 100 TPTP problems with status Satisfiable or CounterSatisfiable: Vampire found 77 finite models, and **70 are certified under a strict kernel-only policy (90.9%)**. 2 more use `native_decide` (a larger trusted base), and none of the 5 failures is an invalid certificate. A held-out set, drawn with a fixed seed and checked with frozen code, is in §4.1. |
| **Scales to a million facts** | NLP263+1 (1,026,857 facts, 383,180 constants) is certified in **4.8 min** through the verified checker, against 20.7 min one-theorem-per-formula, on an 8 GB laptop (§4.3) |
| **Beats hand construction on a published Lean project** | It reproduces both of Nakamura's hand-built Spinoza counter-models from his axioms alone, with **2-element** models against his 4 and 3, checked against his own library (§4.2) |
| **Proved semantics** | `Checker.lean` proves, once, that for a valid model (non-empty domain, closed functions) and closed, well-formed formulas, its evaluator agrees with **ordinary first-order satisfaction** on `Fin n`. Reflected certificates conclude exactly that, using only Lean's standard axioms (`propext`, `Quot.sound`). |
| **Tested like it matters** | 80 tests: an independent evaluator of the original formulas, corrupted models, rewrite equivalence, kernel-checked boundary cases (empty domain, out-of-range constants, malformed data), and rejection of unsupported syntax |

## 2. The gap

| Capability | Elsewhere | Lean 4 |
|---|---|---|
| Import proofs from automated provers | Isabelle: Sledgehammer | Lean-auto, LeanHammer, Duper; Vampire proof reconstruction [3] |
| Find concrete counterexamples in fixed types | Isabelle: Quickcheck | `plausible`, Lean Disprove [6] |
| **Find a new finite structure that refutes a claim from abstract axioms, and certify it** | Isabelle: **Nitpick** [5]; HOL4: **HolRefute** [4] (certified replay; unmerged as of Oct 2026); Coq: Goubault-Larrecq's finite models with Coq-checkable proofs, for security-protocol clause sets [7] | **No general automated front end found.** The Equational Theories Project [2] built project-specific machinery for magma laws; other projects build models by hand [1, §4.4] |

This project is a general tool for that last row: any first-order theory in TPTP. It is the converse of [3]: Bodingbauer et al. bring Vampire's *proofs* into Lean; we bring its *models*.

## 3. How it works

| Step | What happens | Trusted? |
|---|---|---|
| **Find** | `vampire -sa fmb -updr off` searches for a finite model of `axioms ∧ ¬conjecture`. Answers are cached by content; timeouts never are. | No |
| **Rewrite** | Formulas are reshaped so checking can prune: miniscoping, flattening and greedy literal order | **Yes**, tested against the original formulas |
| **Compile** | Either **shallow** (an `inductive T`, bitmask tables, one theorem per formula) or **reflected** (the problem as packed data, plus the model as packed tables) | **Yes**, the translation; tested independently |
| **Certify** | Shallow: `decide` per formula. Reflected: `Holds M problem` by `decide +kernel`, using `Checker.lean`'s `check_iff`, proved once. `#eval problem` prints exactly what is certified. | The kernel |

**Hybrid dispatch:** reflection wins on ground facts (7× less CPU on a 10,000-fact slice). One theorem per formula still wins on deeply nested quantifiers. The benchmark uses reflection when at least 90% of formulas are ground facts. Details, the measured design patterns and the negative results are in the whitepaper, §4–5.

## 4. Case studies

### 4.1 TPTP: 100 problems nobody chose for us

From TPTP's ProblemAndSolutionStatistics we kept the **2,561** fof/cnf problems marked Satisfiable or CounterSatisfiable (`bench/eligible.tsv`); these statuses do not guarantee a *finite* model. The 100-problem **development set** is not uniform: the first 20 came from a domain-first picker, the last 80 were drawn uniformly, and the set was used to find and fix bugs. A separate **held-out set** of 100 problems was drawn uniformly with a fixed seed and checked with frozen code: {{HELDOUT_README}}

| Outcome | Lean 4.13 (shallow) | **Lean 4.35 (hybrid)** |
|---|---|---|
| Certified, strict kernel only | 67 | **70** |
| Certified with `native_decide` | 3 | 2 |
| Lean rejected | 6 | **5** |
| Vampire found no model (30 s) | 23 | 23 |
| Median time per problem | 3 s | 0.65 s (Vampire answers cached; not a Lean speedup) |

- **All 5 remaining rejections are one family:** deeply nested modal-logic encodings (LCL6xx), failing in Lean's instance search. None is a wrong model.
- **Of the 23 problems without a model,** 11 are rated 1.00 by TPTP: no prover in its reference evaluations solves them.
- **Three verdicts improved on Lean 4.35:**
  - NLP263+1 (§4.3);
  - HWV048-2, a stack overflow on 4.13, now certified in 2.7 s;
  - NLP018-10, now kernel-only.

### 4.2 Spinoza's *Ethics*: Nakamura's Lean formalization [1]

**The question.** Nakamura formalizes *Ethics* I in Lean 4. His *demote experiments* ask whether a contested axiom of Spinoza's follows from a weaker principle. Two of his published answers are negative:

- **S-A12:** A12 (an attribute belongs to one substance) does not follow from his `StatedAxioms` plus `PSRSubstance`, a principle of sufficient reason requiring distinct substances to differ in some attribute.
- **S-A15:** A15 (every attribute of a substance is an attribute of God) does not follow from `StatedAxioms` plus plenitude.

He proves both with counter-models he built **by hand** ([1] §4.4), with 4 and 3 elements. We asked whether the tool could find them on its own.

**How we got the result.**

| Step | What we did | Check |
|---|---|---|
| 1. Read | His `Definitions.lean`: 13 primitive predicates (`inItself`, `perSeConceived`, `intellectPerceivesAsEssence`, …) and the defined `Substance`, `Attribute` and `IsGod`. His `Axioms.lean`: the 12 `StatedAxioms` fields, 4 of which are `True` placeholders. His sufficient-reason classes. All at commit 6d4c046. | — |
| 2. Transcribe | Into first-order logic: primitives → predicates; `def`s → biconditionals; the 8 nontrivial fields of his `StatedAxioms` register (12 fields, 4 of them `True` placeholders; the 8 mix stated axioms with his bridges A8–A11) → axioms; the weaker principle Σ → axiom; the target → conjecture. See `examples/nakamura_a12.p`. | Each line cites its Lean source |
| 3. Validate | The transcription must reproduce his **positive** results before its negative ones mean anything | It does: weak P5 follows from StatedAxioms + `PSRSubstance`, and A15 from StatedAxioms + A25 + A26 (Z3, unsat cores) |
| 4. Search, blind | `vampire -sa fmb` on each problem. The encoding came from his definitions and axioms only; we had read his `A15CounterModel` earlier, but not his `A12CounterModel`, and the search is automatic either way. | 2-element models in about 0.1 s. Z3 failed on S-A12. |
| 5a. Certify (transcription) | `cm.py` compiles the model; `decide` proves `axioms ∧ ¬conjecture` | `Cm/nakamura_a12.lean`, `Cm/nakamura_a15.lean` |
| 5b. Certify (**his library**) | The same models are compiled into instances of **his own classes**: a finite `T`, `instance : EthicaWorld T` (13 tables), and `instance : StatedAxioms T` (every field by `decide`). Then `theorem result : StatedAxioms T ∧ Σ ∧ ¬A`. | `nakamura/`: builds against a fresh clone of his unmodified library; `#print axioms` gives `[propext]` |

**The models**, with `attribute(a, s)` meaning "a is an attribute of s":

| | Universe | Substances | Attribute relation | Why the target fails |
|---|---|---|---|---|
| **S-A12** | {1, 2} | both | 1 is an attribute of 1; 2 is an attribute of 1 and of 2 | The two substances **share** attribute 2, so A12 fails. They also **differ** in attribute 1, so the sufficient-reason principle still holds. This is the shape of the classic objection to I P5: substances sharing one attribute and differing in another. |
| **S-A15** | {1, 2} | both, and **both are gods** | 1 is an attribute of 1 and 2; 2 is an attribute of 2 only | Attribute 2 belongs to a substance, but not to god 1, so A15 fails. Plenitude holds, since every substance is itself a god. Two gods, as in his model. |

**Results.**

| Claim | His model (by hand) | Ours (automatic) |
|---|---|---|
| S-A12 | 4 elements | **2 elements**, 0.1 s |
| S-A15 | 3 elements | **2 elements**, 0.1 s |

**Caveat on "smaller".** In our models the same objects are both substances and attributes. Nakamura's axioms permit that: attributes are conceived through themselves, and so they count as substances under his definitions. But it is part of why the models are smaller. A sorted encoding that kept substances and attributes apart would test whether 2 elements still suffice.

**Further results in the same framework** (found earlier in this project, with an LLM proposing candidate premises and provers screening them; the counter-models were first written by hand and are now generated by `cm.py`):

| Example | Claim |
|---|---|
| `p14_bridge_weaker` | The P14 bridge H ("every substance shares an attribute with God"), with A14 and a unique god, does not give A15 |
| `p7_needs_a4c`, `p7_needs_b1c`, `p7_needs_b1` | *Ethics* II P7 (the order of ideas is the order of things) needs each of its bridges: the converse of I A4, and two idea–thing bridges |


### 4.3 One million facts: NLP263+1

| | One theorem per formula (Lean 4.13) | **Verified checker (Lean 4.35)** |
|---|---|---|
| Wall time | 20.7 min | **4.8 min** |
| Peak memory | 1.64 GB | **0.50 GB** |
| Generated Lean / build output | 178 MB / 2.0 GB | **25 MB / 65 MB** |
| Statement | 1,026,857 propositions | `Holds M problem` |

This problem forced most of the scaling recipe. On the way it exposed four bugs:
- `%` inside a quoted name was read as a comment;
- a kernel overflow on a 10,000-long conjunction;
- a limit of about 20,600 declarations per file in Lean 4.13;
- a quoted constant `'T'` that could clash with internal names.

## 5. Why trust it

| Check | What it guarantees |
|---|---|
| Lean's kernel | The model satisfies the *stated* formulas |
| An independent Python evaluator | The same verdicts by brute force, independently of any translation into Lean |
| Mutants (one corrupted table entry at a time) | Lean accepts exactly what the evaluator accepts, on both certificate paths |
| Rewrite equivalence | Each rewritten formula agrees with its original on every model and mutant |
| Planted bugs | Each one fails tests: a translation error, a scoping error, a dropped negation, a lost parenthesis, a single-formula edge case |

**A lesson from a real bug:** a flattening rule misread TPTP's `! [X] : A => B` as ∀X (A → B). On three problems, Lean certified a *different statement*. The bug was fixed, regression-tested, and every problem rerun. **What you rewrite is part of what you must trust.**

## 6. Limits

- **No command inside Lean yet;** you write TPTP.
- **Untyped first-order logic only;** unsupported TPTP features are rejected, never misread (whitepaper §8.1 lists them).
- **Reflected checking of deeply nested quantifiers is slow,** so the benchmark dispatches by fact share.
- **Vampire's limits are ours:** 23 of 100 sampled problems had no model within 30 s.

## 7. Reproduce

| | |
|---|---|
| Requirements | Lean 4.35 (elan), Vampire 5.1 (on `PATH`, or set `VAMPIRE`), Python 3.12. `nakamura/` pins Lean 4.13. |
| Tests | `pytest test_cm.py` (80 tests), including `tests/Boundary.lean` |
| Examples | `lake build`, then `lake env lean Axioms.lean` |
| Nakamura | `cd nakamura && lake build && lake env lean Axioms.lean` (clones spinoza-ethica-lean @ 6d4c046, about 11 MB) |
| Benchmark | `python3 bench.py N [WORKERS]`; results in `bench/results*.jsonl` |
| Whitepaper | `python3 paper/assemble.py` builds `paper/whitepaper.md` from `paper/whitepaper/` |
| Formal-philosophy agenda | `paper/philosophy-lean-vampire-research.md` (original) and `paper/formal-philosophy.md` (revised, with results) |

## References

1. Y. Nakamura. *Bennett's Conjecture in Lean 4: Counter-Models for the PSR-Reducibility of Spinoza's Propositions V and XIV.* arXiv:2605.02331, 2026. [github.com/Nakammura/spinoza-ethica-lean](https://github.com/Nakammura/spinoza-ethica-lean)
2. M. Bolan et al. *The Equational Theories Project: Advancing Collaborative Mathematical Research at Scale.* arXiv:2512.07087. [teorth.github.io/equational_theories](https://teorth.github.io/equational_theories/paper.pdf)
3. J. Bodingbauer, M. Hajdu, L. Kovács, A. Polaczek, M. Rawson. *Lean on Vampire Proofs (Short Paper).* ITP 2026, LIPIcs 382, 36:1–36:9. DOI 10.4230/LIPIcs.ITP.2026.36. [github.com/vprover/vamplean](https://github.com/vprover/vamplean)
4. HolRefute: HOL-Theorem-Prover/HOL pull request #2051. [github.com/HOL-Theorem-Prover/HOL/pull/2051](https://github.com/HOL-Theorem-Prover/HOL/pull/2051)
5. J. C. Blanchette, T. Nipkow. *Nitpick: A Counterexample Generator for Higher-Order Logic Based on a Relational Model Finder.* ITP 2010.
6. J. Ondras, C. Freer. *Lean Disprove: Certified Counterexample Search for AI-Assisted Formal Mathematics.* ICML 2026 AI-for-Math workshop.

7. J. Goubault-Larrecq. *Finite Models for Formal Security Proofs.* Journal of Computer Security 18(6): 1247–1299, 2010. DOI 10.3233/JCS-2009-0395.

The full reference list (35 entries, each marked verified or partly verified) is in the whitepaper.
