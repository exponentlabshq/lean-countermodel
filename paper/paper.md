---
title: "Lean on Vampire *Models*: Kernel-Checked Finite Counter-Models for Lean 4"
author:
  - Michael Jagdeo, Exponent Labs LLC
  - "[co-author to confirm]"
date: "DRAFT, 2026-10-15"
---

# Abstract

Showing that axioms do *not* imply a statement requires a counter-model. Isabelle has Nitpick for this. Lean 4 has proof reconstruction from automated provers and certified search for concrete counterexamples, but no finder for abstract axiom systems: users build such counter-models by hand.

We connect Vampire's finite-model builder to Lean's kernel. The model becomes a finite inductive type with tables, and `axioms ∧ ¬conjecture` is proved by `decide`, so Vampire need not be trusted. The compiler is one Python file of about 8 KB.

Naive `decide` is hopeless on realistic problems: one benchmark clause has about 10¹¹ cases. We make it practical with five standard algorithmic patterns, each measured: backtracking via miniscoping, greedy join order, recursive flattening, bitmask tables, and per-formula theorems. A sixth, a cost-based planner, was measured and rejected.

On 100 TPTP problems sampled from the 2,561 with a finite-model status, Lean certifies 67 of the 73 models Vampire finds, 64 of them with the kernel alone. The tool also reproduces, from axioms alone, both hand-built counter-models in a published Lean formalization of Spinoza's *Ethics*, with smaller models.

# 1. The gap

Lean 4 can import proofs from automated provers: Lean-auto, LeanHammer, Duper, and Vampire proof reconstruction ("Lean on Vampire Proofs", ITP 2026). It can also search for concrete counterexamples: `plausible`, and Lean Disprove (ICML 2026 AI-for-Math workshop). Both kinds of search work *within* fixed types (`Nat`, `Fin n`).

What is missing is a finder that *invents* a structure, meaning a universe plus interpretations of the undefined symbols, that satisfies a theory and falsifies a target. This is the Nitpick and Mace4 capability. It is how independence, non-implication and vacuity are shown.

Without it, Lean projects build counter-models by hand. Nakamura's formalization of Spinoza's *Ethics* (arXiv:2605.02331, §4.4) is an example. The finite-magma-independence project does the same with Z3 scripts written for that one project.

# 2. Method

`cm.py problem.p`:
1. Runs `vampire -sa fmb` on a TPTP problem in fof or cnf.
2. Parses the FiniteModel output.
3. Emits:
   - `inductive T | e1 | … | en`, deriving `DecidableEq`, with `Decidable` instances for `∀` and `∃` over `T`;
   - a match table for each function and a bitmask for each predicate (§3.4);
   - one theorem per formula, each proved by `decide`, and `countermodel : axioms ∧ ¬conjecture` assembled from them.

**What must be trusted:**
- **Lean's kernel.** The proofs use only the `propext` axiom.
- **`cm.py`'s translation of formulas into Lean** (about 40 lines).
- **The rewriting of §3**, which is checked against the original formulas by an independent evaluator (§5).

Vampire is not trusted: a wrong model fails `decide`. Generated files set `autoImplicit false`, so an unbound name is an error rather than a silently added quantifier.

# 3. Making `decide` scale

`decide` evaluates at roughly 1,000 cases per second in Lean 4.13's elaborator. A clause with v variables over n elements costs nᵛ cases if it is checked naively. We measured each change by counting the atoms a lazy evaluator touches, and kept it only if it paid off.

| Pattern | Here | Effect |
|---|---|---|
| **Backtracking with pruning** | *Miniscoping*: each variable is quantified just before its first literal, using ∀X (A ∨ B) ↔ A ∨ ∀X B for X not in A. `decide` evaluates `∨` and bounded `∀` lazily, so a false guard skips its subtree. | NLP219-1 has one 13-variable clause over 7 elements, about 10¹¹ cases. After the rewrite, the whole problem needs 46,746 atom checks. |
| **Greedy join order** | The literal introducing the fewest new variables comes next | SWB017+3 starts from its most selective guard, `rest(S3, nil)` |
| **Recursive flattening** | `∀V (A → ∀W (B → C))` becomes one clause, ¬A ∨ ¬B ∨ C. A quantifier is pulled out only if its variables are fresh. | SWB017+3: 368,112 → 5,932 atom checks, from needing `native_decide` to 2–12 s with the kernel alone |
| **Bitmask instead of a linear scan** | A predicate is one natural number, read as `(MASK >>> index) % 2 = 1`. The kernel computes `Nat` operations natively. | NLP165-1: 10.9 s → about 1 s |
| **Divide and conquer** | One theorem per formula, so each `decide` starts with fresh caches | PLA025+1: 47 s → 14 s, with peak memory 805 MB → 420 MB |
| ~~Cost-based planner~~ | Order literals by the model's table densities | Mixed (−24% and +14% atom checks); rejected |

# 4. Evaluation

**TPTP.** TPTP's ProblemAndSolutionStatistics lists 2,561 fof and cnf problems with status Satisfiable or CounterSatisfiable. We sampled 100 uniformly. Each problem gets 30 s of Vampire, then 60 s of `decide`; `native_decide` is tried only after a timeout.

| Result | Problems |
|---|---|
| Certified, kernel only | 64 |
| Certified with `native_decide` | 3 |
| Lean rejected | 6 |
| Vampire found no model | 27 |

47 of the certified models have more than one element; the largest has 10. Five of the six rejections are deeply nested modal-logic problems (LCL6xx), whose instance search or evaluation exceeds Lean's limits. The sixth is a 16-element hardware model that overflows the stack. None is a wrong model. The median end-to-end time is 3 s per problem (mean 16 s, dominated by Vampire's 30 s limit on problems without a model).

**A published Lean project.** We transcribed Nakamura's definitions and `StatedAxioms` from spinoza-ethica-lean @ 6d4c046. Vampire then found counter-models for both of his published non-derivability claims (S-A12, S-A15) with **2 elements each**; his hand-built ones have 4 and 3. We also compiled these models into instances of his `EthicaWorld` and `StatedAxioms` classes and kernel-checked them against his unmodified library.

**A case study: tonal harmony.** `Music/Harmony.lean` derives conventional harmony from a generative core in core Lean, with no Mathlib, by `decide`. The core is pitch classes as `Fin 12`, the major scale as an interval pattern, and triads stacked on alternate degrees. It proves:
- the circle of fifths: twelve fifths visit all twelve pitch classes, then return;
- a fourth inverts a fifth but is a different operation;
- the Roman-numeral qualities I ii iii IV V vi vii°, **derived, in all twelve keys**, rather than stated.

Lean alone cannot show what each result *depends on*. The counter-models can:

| Question | Counter-model found | Reading |
|---|---|---|
| Do the circle-of-fifths axioms (a 12-cycle compatible with transposition) make f the fifth? | 12 elements, with f = s⁵ | No: the circle of **fourths** satisfies them too. "Fifth" is the definition f = s⁷. |
| Do a tonic, a fifth and some third make chord I major? | 12 elements: the scale has a minor third, not a major third | No: the quality comes from the specific offset 4 in the pattern |
| Does a collection read as C major and as a minor on t force t = C? | 12 elements, with t = s⁹(C) | No: t is A, the relative minor; the pitch classes alone don't fix the tonic |

**A known answer.** For "a fifth up equals a fourth up", given twelve fifths returning home and no early closure, the model found has exactly 12 elements, with f(x) = x + 7 (mod 12) and g(x) = x + 5.

# 5. How we checked the checker

`pytest`: 52 tests, about 4 s.
- **An independent evaluator.** A separate Python evaluator checks every model by brute force, without using the Lean translation.
- **Mutants.** One table entry at a time is corrupted. Lean must accept exactly the mutants the evaluator accepts.
- **The rewrites.** Every rewritten formula is compared with its original, on each example's model and all of that model's one-entry mutations.
- **Planted bugs**, each caught: a translation bug (→ compiled as ↔), a scoping bug, a dropped negation, a lost parenthesis, and a single-formula edge case.
- **A real bug, caught by the kernel.** One early version of the flattening read TPTP's `! [X] : A => B` as ∀X (A → B) instead of (∀X A) → B. On SWW883+1 this made a formula false in the model, and Lean rejected it. On three other problems, though, the altered formula happened to hold, so Lean certified *a different statement*. The bug was fixed, a regression example now fails the old code, and all 73 model-bearing problems were rerun. The lesson for any tool of this kind: the rewriting is part of what must be trusted, so it needs its own independent check, and we now have one.

# 6. Limits

- **Formats.** Purely propositional or trivially decided problems are answered by Vampire without its model builder, in a format we do not parse yet.
- **Trust in the rewriting.** The rewriting of §3 is trusted, and checked by testing rather than proved in Lean.
- **Scope.** Untyped first-order logic only.
- **The front end.** The missing front end is a Lean command that exports the current goal to TPTP, so users never write TPTP themselves.

# 7. Related work

- **Nitpick** (Blanchette & Nipkow 2010) and **Nunchaku**: model finding for Isabelle, and for higher-order logic.
- **Mace4:** finite model search for first-order logic.
- **Lean on Vampire Proofs** (Bodingbauer, Hajdu, Kovács, Polaczek, Rawson; ITP 2026): the converse of this work.
- **Lean Disprove** (Ondras & Freer 2026) and **plausible:** concrete counterexamples.
- **Benzmüller (2026):** imports Isabelle's Nitpick verdicts into Lean 4.

# Availability

[repo link]. Every number above is reproducible:
- `pytest test_cm.py`
- `python3 bench.py N`
