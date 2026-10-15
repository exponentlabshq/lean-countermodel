# lean-countermodel

Vampire finds finite counter-models; Lean checks them. One file: `cm.py`, about 4 KB.

```
python3 cm.py examples/group_comm.p > Cm/group_comm.lean && lake build
```

Input is a TPTP `fof` problem: axioms and one conjecture. Vampire's finite-model builder (`-sa fmb`) looks for a structure where the axioms hold and the conjecture fails. `cm.py` writes that structure as Lean 4:
- a finite `inductive T`;
- a table for each function and predicate;
- one theorem, `countermodel : axioms ∧ ¬conjecture`, proved by `decide`.

The kernel checks it. If Vampire finds no model, `cm.py` exits non-zero.

## Why

Showing that axioms *don't* imply something takes a counter-model. Isabelle has Nitpick for this, and Mace4 exists for first-order logic, but Lean 4 had no equivalent for abstract axiom systems: tools that find a *new structure* rather than a value in a fixed type. Without one, Lean projects build each counter-model by hand. Nakamura's *Ethics* formalization (arXiv:2605.02331, §4.4) is an example.

## Examples

| Problem | Model | Before |
|---|---|---|
| `circle_of_fifths`: going up a fifth is not the same as going up a fourth | 12 elements: exactly x ↦ x+7 mod 12 | known answer |
| `group_comm`: group axioms don't imply commutativity | 6 elements (S₃) | sanity check |
| `nakamura_a12`: Spinoza's A12 doesn't follow from Nakamura's stated axioms + PSR | 2 elements | hand-built, 4 elements |
| `nakamura_a15`: A15 doesn't follow from stated axioms + plenitude | 2 elements | hand-built, 3 elements |
| `p14_bridge_weaker`: the P14 bridge H, with A14 and a unique god, doesn't give A15 | 2 elements | hand-built |
| `p7_needs_a4c`, `p7_needs_b1c`, `p7_needs_b1`: Ethics II P7 needs each of these bridges | 2 elements each | hand-built |
| `transitive_cnf`: clause form, miniscoped: a transitive relation need not be symmetric | small | — |
| `guarded_definition`: the shape of SWB017, a guard implying an equivalence | small | — |
| `single_formula`: the conjecture alone (regression for LCL643) | small | — |
| `music_fifth_is_a_definition`: the circle-of-fifths axioms don't make f the fifth | 12 elements: f is the **fourth** | — |
| `music_triad_needs_the_pattern`: a tonic, a fifth and some third don't make chord I major | 12 elements: a minor third | — |
| `music_tonic_underdetermined`: one collection, read as C major and as a minor on t, doesn't force t = C | 12 elements: t = A, the relative minor | — |
| `quantifier_scope`: TPTP's `! [X] : A => B` is (∀X A) → B (regression for SWW883+1) | small | — |
| `propositional`: zero-arity predicates mixed with first-order ones (regression for TPTP NLP165-1) | 2 elements | — |

Each takes about 0.1 s to find. `lake build` checks all sixteen, plus `Music/Harmony.lean`: Roman-numeral harmony derived in core Lean by `decide`, in about 2 s, and every theorem uses only the `propext` axiom. Generated files set `autoImplicit false`, so an unbound name is an error, and `maxHeartbeats 0`, so the build's wall clock is the only budget.

## What you must trust

- **Lean's kernel,** for "this structure satisfies this statement".
- **`cm.py`'s translation of the formulas** (the `lean()` function, about 40 lines). Read the generated `countermodel` statement: it should match the `.p` file.
- **Vampire is not trusted.** A bad model fails `decide`.

The Spinoza examples restate Nakamura's definitions and axioms in TPTP, transcribed from spinoza-ethica-lean @ 6d4c046. The theorems are about that transcription, not instances of his Lean classes.

## Testing

`pytest test_cm.py`: 52 tests, about 4 s. Three judges have to agree:

- **Lean's kernel** accepts every compiled counter-model, using only `propext`.
- **A separate Python evaluator** checks each model by brute force, without going through `cm.py`'s translation to Lean: the axioms hold and the conjecture fails.
- **Known answers.** The circle-of-fifths model must be exactly the 12-note cycle: up a fifth is x ↦ x+7 (mod 12), and up a fourth is its inverse.

**Mutants.** Two table entries per example are corrupted, one at a time. Lean must accept exactly the mutants that Python says are still counter-models: of the 18, 17 break and 1 survives, and Lean agrees on all of them. A problem that is a theorem must be refused. A deliberately planted translation bug (→ compiled as ↔) fails 7 tests. **Every rewrite is checked:** every miniscoped or flattened formula is compared with its original on each example's model and all of that model's one-entry mutations. Planted bugs are caught: a scoping bug fails 4 tests, a dropped negation fails 18, a lost parenthesis fails 4, and a missing single-formula case fails 1.

**The judges are not fully independent.** The evaluator reuses `cm.py`'s tokenizer and its left-to-right grouping of chained operators. TPTP requires parentheses wherever the grouping would be ambiguous, which makes this safe, but the two share that assumption.

## Benchmark: 100 TPTP problems

`python3 bench.py N [WORKERS]` samples N problems from `bench/eligible.tsv`, which lists the 2,561 fof and cnf problems that TPTP's ProblemAndSolutionStatistics marks Satisfiable or CounterSatisfiable. It downloads each problem, with its axiom files cached on disk, while the workers check earlier problems, and appends a row to `bench/results.jsonl`. Each problem gets 30 s of Vampire, then 60 s of `decide`; `native_decide` is tried only after a timeout. About 8 s per problem end to end, with 2 workers.

| Result | Problems |
|---|---|
| **Certified, kernel only (`decide`)** | **64** |
| Certified with `native_decide` | 3 |
| Lean rejected | 6. Five are deeply nested modal-logic problems (LCL6xx); one is a 16-element model that overflows the stack. |
| Vampire found no model | 27 |

**67 of the 73 models Vampire found are certified.** 47 have more than one element; the largest has 10. The median time is 3 s per problem.

### Making `decide` fast: algorithm patterns, measured

The bottleneck is checking, not finding: `decide` evaluates at roughly 1,000 cases per second. Each pattern was measured by counting the atoms a lazy evaluator touches, and kept only if it paid off.

| Pattern | What it does here | Effect |
|---|---|---|
| **Backtracking with pruning** (miniscoping) | Each variable is quantified just before its first literal. `decide` evaluates `∨` and bounded `∀` lazily, so a false guard skips its subtree. Sound since ∀X (A ∨ B) ↔ A ∨ ∀X B when X is not in A. | NLP219's 13-variable clause went from about 10¹¹ cases to 46,746 atom checks for the whole problem; the problem itself went from impossible to certified |
| **Greedy join order** | The literal introducing the fewest new variables comes next | Part of the above; SWB017 starts from its most selective guard, `rest(S3, nil)` |
| **Recursive flattening** | `∀V (A → ∀W (B → C))` becomes one clause, `¬A ∨ ¬B ∨ C`, so guards hidden inside nested quantifiers become visible to the ordering. A quantifier is pulled out only if its variables are fresh. | SWB017: 368,112 → 5,932 atom checks, and from `native_decide` to kernel-only in 2–12 s. PLA025: 91,921 → 31,675. |
| **Bitmask lookup instead of a linear scan** | Each predicate is one natural number, read as `(MASK >>> index) % 2 = 1`, which the kernel computes natively | NLP165: 10.9 s → about 1 s |
| **Divide and conquer** | One theorem per formula, combined with `⟨c0, c1, …⟩`, so each `decide` starts with fresh caches | PLA025: 47 s → 14 s, with peak memory 805 MB → 420 MB |
| ~~Cost-based query planner~~ (rejected) | Order literals by expected pruning, using the model's table densities | Mixed: PLA025 got 24% fewer checks, but NLP219 got 14% more. Not worth the extra code or tying the rewrite to the data. |

All timings are wall-clock on an 8 GB laptop and vary by about 2× with load. The atom counts are exact.

**Bugs the batches found** (now fixed, each covered by an example or the harness):
- deep formulas exhausting instance search;
- `.e1` shorthand making long tables elaborate very slowly;
- zero-arity predicates being dropped;
- clauses too wide for brute force;
- a lost parenthesis after flattening;
- a single-formula problem producing `⟨c0⟩`.

**Not supported yet:** purely propositional or trivially decided problems. For these, Vampire answers without its finite-model builder and prints a different model format.

## Requirements

Lean 4.13 (via elan) and Vampire 5.1, either on `PATH` or with `VAMPIRE` set.
