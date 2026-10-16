# Lean on Vampire *Models*

### Kernel-Checked Finite Counter-Models for Lean 4: a Verified Reflective Checker, a Measured Scaling Recipe, and a Million-Fact Certificate

**Michael Jagdeo**, Exponent Labs LLC · **Jeff Dumps**

*Whitepaper, October 2026. Code and data: https://github.com/exponentlabshq/lean-countermodel*

---

## Abstract

To show that axioms do **not** imply a claim, one exhibits a structure in which the axioms hold and the claim fails. Isabelle has had a finder for such counter-models for over fifteen years. Lean 4 can import *proofs* from automated provers and search for concrete counterexamples in fixed types, but it has no general, automated way to obtain counter-models of abstract first-order theories; projects build them by hand.

We present `lean-countermodel`, which turns finite models found by the Vampire prover into certificates checked by Lean's kernel. Certificates take two forms:

- **Shallow:** the model as a Lean inductive type, with one theorem per formula.
- **Reflected:** a Lean library defines first-order formulas as data, a Boolean evaluator, and ordinary first-order structures. It proves, once, that for a model whose domain is non-empty and whose functions are closed, and for closed, well-formed formulas, the evaluator agrees with **ordinary first-order satisfaction** in a structure on `Fin n`. A certificate checks validity, well-formedness and truth in one kernel evaluation, and concludes that this structure satisfies every formula. It uses only Lean's standard axioms (`propext`, `Quot.sound`).

Vampire is untrusted: a model that is ill-formed or that falsifies the encoded problem yields no certificate. The translation from TPTP into Lean remains trusted code, tested against an independent evaluator of the *original* formulas.

Most of the work is in making the check finish. One benchmark clause has about $10^{11}$ cases, and a 10,000-formula file overflowed Lean 4.13's kernel. We give a recipe of classic patterns: backtracking via miniscoping, bitsets, balanced trees, hierarchical aggregation, content-addressed caching, blocking and reflection. Each is kept or rejected on measurement, and we report the negative results. For our large ground-fact certificates, the cost was dominated by elaborating statements rather than evaluating them. Quantifier-heavy checking has a separate evaluation bottleneck.

**Evaluation:**

- **Three samples of 100 TPTP problems** with status Satisfiable or CounterSatisfiable [34] (fof/cnf), inputs rebuilt byte for byte from the official TPTP release. After the round-4 repair (below), all three were rerun at one commit. On the **third sample, selected before its first execution**, Vampire found 67 finite models within 30 s, and **59 were certified under our strict kernel-only policy (88.1% of models, 59% of all problems)**; 3 more with native evaluation, which enlarges the trusted base. The development set gives 71 of 78 (91.0%) and the second sample 55 of 62 (88.7%), with 2 native-assisted each. Conditional certification rates are similar across the three; full-pipeline success varies more (71%, 55%, 59%), mainly with how many models the finder returns. Uncertified candidates either hit Lean's time or instance-search limits or, in one case (`SYO595-1`), crashed in certificate generation; one further input crashed the translator. All are reported as failures. All three samples have now been exposed to development, so these are descriptive results, not an untouched test.
- **A source-fidelity correction.** Peer review found that the record reader could skip a legal TPTP record without error. **Eight earlier certificates omitted source premises and were withdrawn. The repaired pipeline subsequently certified their complete source problems. Unchanged strict totals do not validate the superseded certificates.** One previously native-assisted result timed out in the rerun and is reported as a failure. Records are now read totally and fail-closed, the test oracle reads them independently, and every certified result is checked against its original source file (§6.2.2).
- **A million-fact theory.** NLP263+1 (1,026,857 facts) is certified in a median 5.2 minutes reflected, against 14.1 minutes shallow, in a controlled, repeated comparison on the same Lean version, worker budget and laptop: about 2.7× in wall time and 2.6× in CPU time. These timings were measured at an earlier commit (`62d43d6`). The final code generates a byte-identical reflected certificate; its shallow certificate differs only by renamed helper declarations and one conjunct (`Nonempty T`), and was not re-timed (§6.3.1). Its model has one element, so this measures certificate throughput, not combinatorial checking.
- **A published Lean formalization.** The tool reproduces, from axioms alone, both hand-built counter-models of Nakamura's Lean reconstruction of Spinoza's *Ethics*, with smaller models. It also produces a certified negative-dependency map of that reconstruction's register.

**Keywords:** Lean 4 · finite model finding · counter-models · Vampire · TPTP · proof by reflection · certificates · interactive theorem proving

---

## Contents

1. [Introduction](#1-introduction)
2. [Background and Problem](#2-background-and-problem)
3. [Method: Find, Rewrite, Compile, Certify](#3-method-find-rewrite-compile-certify)
4. [The Verified Checker: Data Structures and Trust](#4-the-verified-checker-data-structures-and-trust)
5. [Scaling: Design Patterns, Data Structures and Measured Effects](#5-scaling-design-patterns-data-structures-and-measured-effects)
6. [Evaluation and Case Studies](#6-evaluation-and-case-studies)
7. [Related Work](#7-related-work)
8. [Limitations and Future Work](#8-limitations-and-future-work)
9. [Conclusion](#9-conclusion)
- [Appendix A: Reproducing Every Number](#appendix-a-reproducing-every-number)
- [References](#references)

### List of tables and figures
{{generated at assembly}}
