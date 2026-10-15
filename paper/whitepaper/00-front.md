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
- **A development set** of 100 TPTP problems with status Satisfiable or CounterSatisfiable [34] (fof/cnf): Vampire returned 77 finite models. **70 were certified under our strict kernel-only policy (90.9% of models, 70% of problems).** Two more were certified with native evaluation, which enlarges the trusted base. None of the 5 failures is an invalid certificate.
- **A held-out set** of 100 further problems, drawn uniformly with a fixed seed and checked with the frozen implementation: {{HELDOUT}}.
- **A million-fact theory.** NLP263+1 (1,026,857 facts) is certified in 4.8 minutes reflected, against 23.7 minutes shallow on the same Lean version and laptop. Its model has one element, so this measures certificate throughput, not combinatorial checking.
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
