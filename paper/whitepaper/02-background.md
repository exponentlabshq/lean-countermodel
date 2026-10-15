## 2. Background and Problem

### 2.1 Counter-models

A first-order *problem* is a set of axioms $\Gamma$ and, optionally, a conjecture $\varphi$. A **counter-model** is a structure $\mathcal{M}$ with $\mathcal{M} \models \Gamma$ and $\mathcal{M} \not\models \varphi$. By soundness of first-order logic, a counter-model proves $\Gamma \nvdash \varphi$. If there is no conjecture, a model of $\Gamma$ shows that $\Gamma$ is consistent. A **finite** counter-model has a finite universe $\{0, \dots, n-1\}$ and finite tables for every constant, function and predicate. Checking it is decidable by enumeration, but naive enumeration costs $n^v$ cases for a formula with $v$ variables.

### 2.2 TPTP and Vampire

TPTP [23] is the standard problem library for automated theorem proving. Its 26,990 problems each carry a status. **2,561 of them are untyped first-order (`fof` or `cnf`) with status *Satisfiable* or *CounterSatisfiable*.** These statuses mean a model exists, not that a *finite* one does: the SZS ontology has separate *FinitelySatisfiable* and *FinitelyCounterSatisfiable* statuses [34]. A theory may have only infinite models, so a finite-model finder can fail on these problems for reasons other than time. Vampire [24] includes a finite-model builder (`-sa fmb`), which prints models as TPTP `tff` tables. We use it as an untrusted oracle.

### 2.3 Lean 4's kernel and `decide`

Lean 4 [25] is an interactive theorem prover whose small kernel checks proof terms. For a decidable proposition $P$:

- **`decide`** evaluates the `Decidable P` instance in the elaborator, then has the kernel re-check it;
- **`decide +kernel`** (Lean ≥ 4.15) asks the kernel alone to evaluate;
- **`native_decide`** compiles the check to machine code. It is fast, but it adds the compiler to what must be trusted. Since Lean 4.29, each such computation is recorded as its own axiom, with `_native` in its name [35].

**Our strict policy** accepts only kernel checks: `#print axioms` must list at most the standard axioms `propext` and `Quot.sound`. `cm.py` never emits `native_decide`. The benchmark harness tries it only after a kernel timeout, and reports such certificates in a separate, weaker category.

### 2.4 The problem

Given a TPTP problem and Vampire's finite model, produce a Lean file whose main theorem states, faithfully, that the model satisfies every axiom and falsifies the conjecture, and which **Lean's kernel accepts in reasonable time and memory**. Three difficulties make this hard:

1. **Search size.** Brute-force checking is $n^v$ per formula: about $10^{11}$ for one clause in our benchmark.
2. **Elaboration size.** A problem can have over a million formulas. Lean's per-declaration costs (parsing, elaboration, typeclass search, kernel type checking) dominate, and Lean 4.13 hits hard limits: kernel recursion depth, and declarations per file.
3. **Fidelity.** Every rewrite that makes checking fast is trusted code. A wrong rewrite can make Lean certify a statement *other than* the intended one, and we observed exactly that (§5).
