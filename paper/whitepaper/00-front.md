# Lean on Vampire *Models*

### Kernel-Checked Finite Counter-Models for Lean 4: a Verified Reflective Checker, a Measured Scaling Recipe, and a Million-Fact Certificate

**Michael Jagdeo**, Exponent Labs LLC · **Jeff Dumps**

*Whitepaper, October 2026. Code and data: https://github.com/exponentlabshq/lean-countermodel*

---

## Abstract

To show that axioms do **not** imply a claim, one exhibits a structure in which the axioms hold and the claim fails. Isabelle has had a finder for such counter-models for over fifteen years. Lean 4 can import *proofs* from automated provers and search for concrete counterexamples in fixed types. It has no general way to obtain *counter-models* of abstract first-order theories, so projects build them by hand.

We present `lean-countermodel`, which turns finite models found by the Vampire prover into certificates checked by Lean's kernel. Vampire is never trusted: a wrong model fails the check. Certificates take two forms:

- **Shallow:** the model as a Lean inductive type, with one theorem per formula.
- **Reflected:** a 215-line Lean library defines first-order formulas as data, gives them Tarski semantics, and proves a Boolean evaluator sound and complete once. A certificate is then a single statement, `Holds M problem`, proved by kernel evaluation of packed data. It uses only Lean's standard axioms, and `#eval` prints exactly what it certifies.

The work is mostly about making the check finish. Naive certificates are hopeless at scale: one benchmark clause has about 10¹¹ cases, and a 10,000-formula file overflows Lean's kernel. We give a measured recipe of classic patterns, among them backtracking via miniscoping, greedy join ordering, bitsets, balanced trees, hierarchical aggregation, content-addressed caching, blocking and reflection. Each pattern is kept or rejected on measurement, and the negative results are reported. The central lesson for anyone generating large Lean certificates is that **the cost is elaborating statements, not evaluating them.**

**Evaluation:**

- **A uniform sample of TPTP.** On 100 problems drawn from the 2,561 TPTP problems with a finite-model status, Lean certifies **72 of the 77 models Vampire finds (94%), 70 of them with the kernel alone**, and none of the failures is a wrong model.
- **A million-fact problem.** NLP263+1 has 1,026,857 facts and 383,180 constants. Its certificate takes 20.7 minutes as a shallow certificate and **4.8 minutes reflected**, on an 8 GB laptop.
- **A published Lean formalization.** The tool reproduces, from axioms alone, both hand-built counter-models in Nakamura's Lean formalization of Spinoza's *Ethics*, with smaller models.

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
