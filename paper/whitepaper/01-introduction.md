## 1. Introduction

Formal developments are full of *negative* claims:

- this axiom is independent of those;
- this hypothesis is needed;
- this conjecture is false;
- these assumptions are consistent.

Each is shown the same way. One exhibits a **counter-model**: a structure that satisfies the premises and falsifies the conclusion. Automated model finders such as Mace4 and Vampire's finite-model builder find small counter-models in milliseconds. Isabelle users have had Nitpick for this since 2010 [3].

Lean 4 users have no equivalent for abstract theories. Lean can replay proofs from automated provers, and it can search for concrete counterexamples over types it already knows, such as `Nat` and `Fin n`. Lean can *represent* any finite structure, but it has no general automated front end that *finds* one, a universe together with interpretations of uninterpreted symbols, and certifies it. So Lean projects build their counter-models by hand. For example, the two non-derivability results in a recent Lean formalization of Spinoza's *Ethics* rest on hand-built models of 4 and 3 elements [22, §4.4]. The Equational Theories Project [1] built project-specific machinery to check about 587,000 magma counterexamples.

### 1.1 Motivation: philosophy written in geometric order

Spinoza's *Ethics* was published in 1677 as *Ethica ordine geometrico demonstrata*, "demonstrated in geometrical order". Like Euclid, it gives definitions, axioms and propositions, each with a demonstration citing earlier ones. A philosophy written this way invites machine checking. Its central arguments have been disputed for three and a half centuries; whether Proposition 5 ("no two substances share an attribute") follows from what Spinoza states is one example.

Formal philosophy has long used automated provers and model finders on such questions [28]. Examples include computational metaphysics with Prover9 and Mace [29], a computationally discovered simplification of the ontological argument [30], a computer-assisted reconstruction of an ontological argument in the *Ethics* itself [31], and recent Lean 4 work on Gödel's and Scott's ontological arguments [21]. A research agenda for this field describes a seven-stage workflow, with the companion paper `paper/formal-philosophy.md` as the starting point: reconstruct the text, axiomatize it, explore with an automated prover, check candidate models independently, verify in a proof assistant, *ablate* each assumption, and review the interpretation. It frames the field's most important output as **a map of the assumptions that hold a theory together**, and we know of no tool that produces such a map with certified counter-models.

`lean-countermodel` implements stages 3–6 for first-order reconstructions. Applied to a published Lean formalization of the *Ethics* [22], it produces that map (§6.1.1), with every "this assumption is needed" backed by a counter-model that Lean's kernel checks.

### 1.2 Contributions

**This paper.** We connect Vampire's finite-model builder to Lean's kernel, for untyped first-order problems in TPTP (`fof` and `cnf`; §8 lists the unsupported features), and we make the result scale. The contributions are:

1. **A tool, `lean-countermodel`,** which compiles a Vampire model into a Lean certificate. Vampire is untrusted: a model that is ill-formed or falsifies the encoded problem yields no certificate (§3).
2. **A verified reflective checker** (`Checker.lean`). It provides first-order formulas as data, a Boolean evaluator, and ordinary first-order structures, and proves once that, for a valid model (non-empty domain, closed functions) and closed, well-formed formulas, the evaluator agrees with ordinary satisfaction on `Fin n` (`sem_iff_sat`). Certificates conclude that this structure satisfies every formula, with Lean's standard axioms only (§4).
3. **A measured scaling recipe.** Classic algorithmic patterns, each kept or rejected on measurement, take certificates from about 10¹¹ cases, and from files that crash Lean's kernel, to a million-fact problem certified in a median 5.2 minutes (range 5.2–5.8, three runs). Three findings, each measured on our generated workloads and stated with that scope in §5 and §8:
   - for our large ground-fact certificates, the cost was dominated by **elaborating statements, not evaluating them**;
   - on Lean 4.13, with our generated pattern and default options, **files of more than about 20,600 declarations failed** with kernel "deep recursion";
   - in our decoder, **lazy kernel evaluation punished nested data** (§5).
4. **An evaluation.** It covers three 100-problem samples of TPTP problems with status Satisfiable or CounterSatisfiable: a development set (not uniformly drawn), a second uniform sample that was later used to find and fix defects, and a third uniform sample run once with frozen code; a 1,026,857-fact problem; and a published Lean formalization (§6).
5. **An assumption-dependency map** of Nakamura's register for *Ethics* I (§6.1.1), produced by a reusable ablation tool (`ablate.py`).
6. **A trust case study.** Four real bugs in the trusted rewrite and naming layers, one of which made Lean certify a statement other than the intended one, were each caught by an independent check. Peer review then led us to two more: silent misreading of unsupported TPTP syntax, now closed by fail-closed parsing, and a TPTP variable named `T` capturing the domain type (Lean rejected it; variables are now primed), and to a kernel-checked validity theorem for the checker's semantics. A third-round audit of the benchmark inputs against the official TPTP release found that include expansion also expanded includes inside comments, which changed two inputs; neither had been certified (§4, §5, §6.2, §8).

**What is not new.** Model finding, kernel-checked finite certificates and proof by reflection are each well established (§7). The closest predecessor is Goubault-Larrecq's extraction of finite models of first-order clause sets with Coq-checkable model-checking proofs [32]; finite model theory itself has been mechanized in Coq [33]. Our contribution is a specific, implemented combination: general untyped first-order models from Vampire, certified in Lean 4 by a verified reflective evaluator with a validity theorem, at the scale measured here. A focused search found no implementation with this combination; that is not a claim of first-ever status.
