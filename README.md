# lean-countermodel

**Kernel-checked finite counter-models for Lean 4, found by Vampire.**

> To show that some axioms do **not** imply a claim, you exhibit a world where the axioms hold and the claim fails.
> Vampire finds such a world automatically. `cm.py` (8 KB of Python) writes it as Lean 4, and Lean's kernel checks it.
> Vampire never has to be trusted: a wrong model fails the check.

```
python3 cm.py examples/circle_of_fifths.p > Cm/circle_of_fifths.lean && lake build
```

---

## 1. Results at a glance

| Claim | Evidence |
|---|---|
| **Works on independent problems** | 100 problems sampled from TPTP, the standard prover benchmark. Lean certifies **67 of the 73 models Vampire finds**, 64 of them with the kernel alone. **None of the 6 failures is a wrong model.** |
| **Beats hand construction on a published Lean project** | It reproduces both of Nakamura's hand-built Spinoza counter-models [1] from his axioms alone, with **2-element** models against his 4 and 3, checked against his own library (§4.1) |
| **Makes brute-force checking feasible** | It takes a clause needing ~10¹¹ cases down to 46,746 atom checks for the whole problem; the median is 3 s per problem (§3) |
| **Readable by non-specialists** | Certified: the circle-of-fifths axioms cannot tell a fifth from a fourth, and a pitch collection does not fix its tonic (§4.2) |
| **Small** | `cm.py` 8.3 KB · `bench.py` 5.0 KB · `test_cm.py` 5.5 KB, with 52 tests running in about 4 s |

## 2. The gap

| Capability | Isabelle and others | Lean 4 |
|---|---|---|
| Import proofs from automated provers | Sledgehammer | Lean-auto, LeanHammer, Duper; Vampire proof reconstruction [2] |
| Find concrete counterexamples (values of fixed types) | Quickcheck | `plausible` [8], Lean Disprove [7] |
| **Find a new finite structure that refutes a claim from abstract axioms** | **Nitpick** [4]; Mace4 [11] for first-order logic | **None found.** Projects build these by hand ([1] §4.4) or with one-off scripts [10]. |

We found no Lean 4 tool in the last row. This project is a prototype of one. It is the converse of [2]: Bodingbauer et al. bring Vampire's *proofs* into Lean; we bring its *models*.

## 3. Method

### 3.1 Find, compile, certify

| Step | What happens | Trusted? |
|---|---|---|
| **Find** | `vampire -sa fmb` [3] searches for a finite model of `axioms ∧ ¬conjecture` (TPTP fof or cnf [6]) | No |
| **Rewrite** | Each formula is reshaped so checking can prune (§3.2) | **Yes**, but tested against the original (§5) |
| **Compile** | The model becomes `inductive T \| e1 \| … \| en`, a table per function, a bitmask per predicate, and one theorem per formula | **Yes**: the translation into Lean |
| **Certify** | Each theorem is proved by `decide`, and `countermodel : axioms ∧ ¬conjecture` combines them. Lean's kernel [5] checks it. | **Yes**: the kernel. Only the `propext` axiom is used. |

**The principle:** let an untrusted search do the finding, and make the trusted checker's job small enough to finish.

### 3.2 Making `decide` scale: five patterns, measured

`decide` checks about 1,000 cases per second, and a clause with *v* variables over *n* elements has *nᵛ* cases. We measured each change by counting the atoms a lazy evaluator touches, and kept it only if it paid off.

| Pattern | Applied as | Measured effect |
|---|---|---|
| **Backtracking with pruning** | Miniscoping [9]: each variable is quantified just before its first literal, using ∀X (A ∨ B) ↔ A ∨ ∀X B when X is not in A. Lazy `∨` and `∀` then skip whole subtrees. | NLP219: ~10¹¹ cases → **46,746** atom checks; from impossible to certified |
| **Greedy join order** | The literal introducing the fewest new variables comes next | SWB017 starts from its most selective guard |
| **Recursive flattening** | `∀V (A → ∀W (B → C))` becomes one clause, `¬A ∨ ¬B ∨ C`, with fresh variables only | SWB017: 368,112 → **5,932** checks, and from `native_decide` to the kernel alone |
| **Bitmask instead of a linear scan** | A predicate is one natural number, read as `(MASK >>> i) % 2 = 1`; the kernel does natural-number arithmetic natively | NLP165: 10.9 s → **~1 s** |
| **Divide and conquer** | One theorem per formula, so caches are fresh for each | PLA025: 47 s → **14 s**; peak memory 805 → 420 MB |
| ~~Cost-based planner~~ | Order literals by the model's table densities | Mixed (−24%, +14%); **rejected** |

### 3.3 Working method

- **Fibonacci batches** (1, 1, 2, 3, 5, 8): fix what breaks before scaling up.
- **Measure before optimizing:** the benchmark pipeline went from about 174 s to about 8 s per problem once we measured and found the bottleneck was *choosing* problems, not checking them.
- **Independent judges, and planted bugs** (§5).

## 4. Case studies

### 4.1 Spinoza's *Ethics*: Nakamura's Lean formalization [1]

**The question.** Nakamura formalizes *Ethics* I in Lean 4. His *demote experiments* ask whether a contested axiom of Spinoza's follows from a weaker principle. Two of his published answers are negative:

- **S-A12:** A12 (an attribute belongs to one substance) does not follow from his `StatedAxioms` plus `PSRSubstance`, a principle of sufficient reason requiring distinct substances to differ in some attribute.
- **S-A15:** A15 (every attribute of a substance is an attribute of God) does not follow from `StatedAxioms` plus plenitude.

He proves both with counter-models he built **by hand** ([1] §4.4), with 4 and 3 elements. We asked whether the tool could find them on its own.

**How we got the result.**

| Step | What we did | Check |
|---|---|---|
| 1. Read | His `Definitions.lean`: 13 primitive predicates (`inItself`, `perSeConceived`, `intellectPerceivesAsEssence`, …) and the defined `Substance`, `Attribute` and `IsGod`. His `Axioms.lean`: the 12 `StatedAxioms` fields, 4 of which are `True` placeholders. His sufficient-reason classes. All at commit 6d4c046. | — |
| 2. Transcribe | Into first-order logic: primitives → predicates; `def`s → biconditionals; the 8 substantive `StatedAxioms` fields → axioms; the weaker principle Σ → axiom; the target → conjecture. See `examples/nakamura_a12.p`. | Each line cites its Lean source |
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

### 4.2 Tonal harmony: the circle of fifths

`Music/Harmony.lean` (2.4 KB, core Lean, no Mathlib) **derives**, rather than states:
- the circle of fifths: twelve fifths visit every pitch class, then return;
- a fourth inverts a fifth yet differs from it;
- the Roman-numeral qualities **I ii iii IV V vi vii°, in all 12 major keys**.

Each theorem uses at most `propext`.

Lean alone cannot show what each result *depends on*. The counter-models can:

| Question | Counter-model | Reading |
|---|---|---|
| Is "fifth up = fourth up"? (a known-answer test) | exactly the 12-note cycle: f(x) = x+7, g(x) = x+5 | No; the model is the expected one |
| Do the circle-of-fifths axioms (a 12-cycle compatible with transposition) make f the fifth? | 12 elements, **f = s⁵** | No: the circle of **fourths** satisfies them. "Fifth" is a definition. |
| Do a tonic, a fifth and some third make chord I major? | a scale with a minor third | No: the quality comes from the offset 4 in the pattern |
| Does one collection, read as C major and as a minor on *t*, force *t* = C? | **t = A** | No: the relative minor. Pitch classes do not fix the tonic. |

### 4.3 Other examples

`group_comm` (group axioms don't imply commutativity: S₃, 6 elements), plus regression examples for each bug the benchmark found (§5).

## 5. Why trust it

| Check | What it guarantees |
|---|---|
| Lean's kernel | The model satisfies the *stated* formulas |
| A separate Python evaluator | The same verdict by brute force, independently of the translation into Lean |
| Mutants (corrupt one table entry at a time) | Lean accepts exactly the mutants the evaluator accepts |
| Rewrite equivalence | Each rewritten formula agrees with its original on every model and mutant |
| Planted bugs | Each is caught: → compiled as ↔ (7 tests fail), scoping (4), a dropped negation (18), a lost parenthesis (4), the single-formula case (1) |

**A lesson from a real bug.** An early version of the flattening read TPTP's `! [X] : A => B` as ∀X (A → B), but TPTP means (∀X A) → B. On one problem this made a formula false, and Lean rejected it. On **three others the altered formula happened to hold, so Lean certified a different statement.** We fixed it, added a regression test, and reran all 73 problems that had a model. **The rewrite is part of what must be trusted**: a kernel certifies only what it is given.

## 6. Limits

- Purely propositional or trivially decided problems: Vampire answers them without its model builder, in a format `cm.py` does not parse yet.
- Deeply nested formulas (modal-logic encodings) still exceed Lean's limits.
- Untyped first-order logic only.
- **The front end inside Lean is missing:** a command that exports the current goal, so users never write TPTP.

## 7. Reproduce

| | |
|---|---|
| Requirements | Lean 4.13 (elan) and Vampire 5.1 (on `PATH`, or set `VAMPIRE`) |
| Examples | `lake build`; check axioms with `lake env lean Axioms.lean` |
| Nakamura, against his library | `cd nakamura && lake build && lake env lean Axioms.lean` (clones spinoza-ethica-lean @ 6d4c046, about 11 MB) |
| Tests | `pytest test_cm.py`: 52 tests, about 4 s |
| Benchmark | `python3 bench.py N [WORKERS]` samples from `bench/eligible.tsv` (the 2,561 eligible TPTP problems); results go to `bench/results.jsonl` |
| Paper | `paper/paper.md` |

## References

1. Y. Nakamura. *Bennett's Conjecture in Lean 4.* arXiv:2605.02331, 2026. Code: [github.com/Nakammura/spinoza-ethica-lean](https://github.com/Nakammura/spinoza-ethica-lean).
2. J. Bodingbauer, M. Hajdu, L. Kovács, A. Polaczek, M. Rawson. *Lean on Vampire Proofs.* ITP 2026, arXiv:2603.26342. Code: [github.com/vprover/vamplean](https://github.com/vprover/vamplean).
3. L. Kovács, A. Voronkov. *First-Order Theorem Proving and Vampire.* CAV 2013. [vprover.github.io](https://vprover.github.io).
4. J. C. Blanchette, T. Nipkow. *Nitpick: A Counterexample Generator for Higher-Order Logic Based on a Relational Model Finder.* ITP 2010.
5. L. de Moura, S. Ullrich. *The Lean 4 Theorem Prover and Programming Language.* CADE 2021.
6. G. Sutcliffe. *The TPTP Problem Library and Associated Infrastructure.* Journal of Automated Reasoning 59(4), 2017. [tptp.org](https://tptp.org).
7. Ondras, C. Freer. *Lean Disprove.* ICML 2026 AI-for-Math workshop. [github.com/cameronfreer/lean4-skills](https://github.com/cameronfreer/lean4-skills).
8. *plausible*: property testing for Lean 4. [github.com/leanprover-community/plausible](https://github.com/leanprover-community/plausible).
9. A. Nonnengart, C. Weidenbach. *Computing Small Clause Normal Forms.* Handbook of Automated Reasoning, 2001 (miniscoping).
10. *finite-magma-independence*: Z3 models checked by `decide` in Lean, built by hand. [github.com/stefanopalmieri/finite-magma-independence](https://github.com/stefanopalmieri/finite-magma-independence).
11. W. McCune. *Mace4 Reference Manual and Guide.* Argonne National Laboratory, ANL/MCS-TM-264, 2003.
