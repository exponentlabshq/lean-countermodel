# Response to peer review: *Lean on Vampire Models*

**To:** the reviewer (Manus AI) · **From:** Michael Jagdeo and Jeff Dumps · **Date:** 15 October 2026

Thank you for a careful, rigorous review. You checked the primary sources, including Nakamura's code at the exact revision, and constructed concrete counterexamples. That made it unusually actionable. We agree with every major point. Below we say, point by point, what changed and where; what is still running; and one finding your review led us to that neither of us had anticipated.

Two items are **pending** at the time of writing; their results will be inserted unchanged, whatever they show:
- the held-out evaluation with frozen code (§6.2.1);
- the controlled performance reruns (§6.3.1).

**On artifact access.** The 404 was expected: the repository is private until the revision is complete. It will be released, with a tagged version, before public circulation.

---

## Major comment 1: the reflected checker needs a model-validity theorem

**Agreed; this was the most important point, and it is now proved, not just asserted.** You were right that `check_iff` establishes only that the evaluator decides the *bounded* semantics. That semantics accepts your examples: `∀x, x ≠ c` with `c` out of range, and `∀x, ⊥` over an empty domain.

**Changes** (`Checker.lean`; whitepaper §4.4):
- **`Structure α` and `Fm.Sat`:** ordinary first-order structures and satisfaction, with every symbol interpreted inside the carrier and quantifiers ranging over all of it.
- **`Model.valid` (kernel-checked):** a non-empty domain, and every function used is closed at its checked arity, checked over all argument tuples.
- **`Tm.wf` / `Fm.wf` (kernel-checked):** variables are bound (no silent `getD` default), constants are in range, and functions are applied only at checked arities.
- **`sem_iff_sat`:** for a valid model and a well-formed formula, the bounded semantics holds **if and only if** ordinary satisfaction holds in the structure on `Fin n` that the model describes. Supporting lemmas: `val_interp` shows that clipping values into the domain never changes them in the valid case, and `allTuples_iff` covers the tuple enumeration. Axioms: `propext` and `Quot.sound`; no `sorry`.
- **Certificates now check `wf` and truth in one pass** (`Good`, `good_of_check`, `good_facts`, `good_append`) and conclude:
  `theorem countermodel : ∀ φ ∈ problem, φ.Sat (M.toStructure (Model.valid_pos valid)) ⟨0, _⟩ [] φ`
- **Your examples are now kernel-checked regression cases** (`tests/Boundary.lean`). `allNeC.check Out [] = true` (the old gap), but `allNeC.wf Out [] 0 = false`; `EmptyDomain.valid [] = false`. Also covered: a leaking function, an unbound variable, a wrong arity, and truncated data.
- **The trust-table claim "a misparsed model is still a model" is withdrawn** and replaced with what is actually checked (§3.8).

We took your suggestion to use `Fin n` as the semantic carrier. We kept the packed `Nat` representation for evaluation and proved the bridge between the two, rather than evaluating over `Fin n` directly.

## Major comment 2: source fidelity, decoder guarantees, the test oracle

**Agreed.**
- **The paper states three guarantees separately:** evaluator correctness (proved); model and formula well-formedness (kernel-checked); and fidelity to the source (trusted, tested). It now calls the system "a verified checker with a tested, trusted translation pipeline, not a verified TPTP-to-Lean compiler" (§4.4).
- **"Malformed data decodes to ⊥" is replaced** with the precise behavior (§4.3):
  - running out of fuel decodes to ⊥;
  - truncation, extra tokens and wrong counts are *not* detected by the decoder, and would be errors in the trusted translation;
  - out-of-scope variables, out-of-range constants and wrong arities are now rejected by `wf`.
- **`#eval problem` is described as a diagnostic, not a fidelity proof**, for the reasons you gave: numeric symbol ids, and compiled execution.
- **The test oracle:** you were right that the mutant comparison used the production rewriter. It now evaluates the **original source formulas** (`raw` in `test_cm.py`). All mutants still agree, so rewrite and translation are checked against the source.
- **The `'cat'` / `cat` regression test you asked for is added and passes:** both map to one symbol, and `'X'` stays distinct from the variable `X`.

**A finding your review led to.** Your minor comment on input scope prompted us to test unsupported TPTP syntax directly, and it exposed **a real class of silent misreadings**:

| Input | Earlier output | Effect |
|---|---|---|
| `p <~> q`, `p <= q` | `p` | the rest of the formula silently dropped |
| `p ~| q`, `p ~& q` | `p ∨ q`, `p ∧ q` | the opposite meaning |
| `tff`/`thf` statements, `include(...)` | ignored | a silently shortened problem certified |

None of our benchmark or example problems used these features; the raw-source oracle would have caught a mismatch. But the hazard was exactly the one you described. **The parser is now fail-closed:**
- every TPTP connective is a single token;
- unsupported constructs raise an error;
- every token must be consumed;
- files containing typed statements or includes are refused.

Each case has a test in both translators (`72bb3e2`), and §8.1 adds the feature matrix you asked for.

## Major comment 3: strict kernel certificates vs native fallback

**Agreed.** The abstract and §6.2 now lead with **70 of 77 models certified under the strict kernel-only policy (90.9%)**. The 2 `native_decide` certificates are reported separately as a larger trusted base: 72 of 77 (93.5%). Full-pipeline success is 70 of 100. The harness's acceptance policy is now described separately from `cm.py`, which never emits native tactics. The native-axiom wording follows the Lean 4.35 reference (`_native` axioms, one per computation, since 4.29), and the reference is cited.

## Major comment 4: sampling, development exposure, finite vs. satisfiable

**Agreed on all three.**
- **Terminology:** *Satisfiable* and *CounterSatisfiable* do not imply a finite model. The SZS ontology is now cited, and the frame is described as satisfiable/counter-satisfiable fof/cnf throughout (§2.2).
- **The set is called a development set,** described as non-uniform, with the first 20 (domain-first picker) and last 80 (uniform) reported separately. Your concern was borne out: the first 20 certified 17 of 17, while the uniform 80 certified 53 of 60 (88.3%).
- **Held-out evaluation:** code frozen at `1a55aef`, run from a separate git worktree. The sample is 100 new problems drawn uniformly without replacement from the 2,461 eligible problems outside the development set, with seed 20261015; the seed, method and list are in `bench/heldout-sample.json`. Finder yield, strict certification, native-assisted certification and full-pipeline success will be reported separately. **[Pending]**
- **The 90% dispatch threshold is now listed as unvalidated** (§8).

## Major comment 5: performance claims

**Agreed.**
- **The central lesson is scoped** to the workloads measured, and §5 states the reflected quantifier regression as a separate bottleneck.
- **An explicit cost model** distinguishes field-operation counts from bit-cost on growing `Nat`s.
- **The declaration limit** is restated as an observed failure point for one generated pattern on Lean 4.13, not re-tested on 4.35.
- **The cached 0.65 s median** is labeled as cache reuse, not a Lean speedup.
- **Greedy ordering** is described as a heuristic.
- **The million-fact comparison** is described as an observed ratio under stated conditions.
- **Metrics are defined explicitly.** Peak memory is now reported both per process and as an aggregate across concurrent Lean processes; the earlier figure was the largest single process.
- **Controlled reruns:** a new harness (`bench/perf.py`) runs clean builds on the same Lean version with the same worker budget. Runs are interleaved and repeated, and every record includes the machine, OS, Lean, Vampire and commit. It covers the 10,000-fact slice and the million-fact problem. **[Pending]**

Two experiments are **not yet done**:
- nontrivial-domain scaling sweeps, varying domain size, quantifier depth and fact share;
- the decode-once ablation of the quantifier regression.

The paper labels the re-decoding explanation as a hypothesis and lists both experiments as future work. We would rather not present them as done.

## Major comment 6: missing precedents and the novelty claim

**Agreed, and thank you for Goubault-Larrecq.** It is a genuine predecessor of the finite-model-to-certificate idea, and our search missed it. Added:
- Goubault-Larrecq, *Finite Models for Formal Security Proofs*, JCS 18(6), 2010;
- Kirst & Larchey-Wendling, *Trakhtenbrot's Theorem in Coq*, IJCAR 2020.

Both now appear in the introduction, §7.1 and the comparison table. The novelty claim is narrowed to the implemented combination, and §7.7 says explicitly that peer review found a predecessor our search missed. The *Lean on Vampire Proofs* citation now gives ITP 2026, LIPIcs 382, article 36, verified on the publisher page you cited, which also lists `vamplean`.

## Major comment 7: the assumption map and the philosophical claims

**Agreed. Your reading of Nakamura's source improved the case study.**
- **"Spinoza's eight stated axioms" is replaced** with "the eight nontrivial fields of Nakamura's reconstructed stated-axiom register". The text notes the four `True` placeholders, and that the eight mix stated-axiom content with an exclusivity rider and the bridges A8–A11.
- **The minimal sufficient sets** come from greedy deletion, so they are more than leave-one-out results. They now cite Nakamura's own direct proofs in `ModalForm.lean`, as you verified.
- **The substance/attribute overlap is explained as forced by A8 and A10,** so a sorted encoding would *conflict* with those bridges rather than refine them. The text also notes that God's definition requires only at least one attribute, and that smaller models are an automation result, not a more faithful Spinoza.
- **Non-derivability is distinguished from independence,** and both claims rest on the soundness of first-order logic.

## Minor comments

All addressed:
- **Input scope:** the §8.1 feature matrix, with fail-closed rejection.
- **The "cannot obtain a new structure" wording** is replaced: Lean can *represent* any finite structure, but lacks an automated front end that finds and certifies one.
- **"A wrong model fails the check"** now reads conditionally: no certificate exists for an ill-formed model, or one falsifying the encoded problem.
- **The dependency-map claim** is narrowed to certified negative-dependency maps for the chosen reconstruction.
- **Test counts are reconciled:** now 80.
- **Line counts** are no longer used as an assurance argument.

## Not yet addressed

- **A public, immutable release,** and `lean4checker --fresh` in CI. Both come before circulation.
- **Nontrivial-domain scaling experiments** and the **decode-once ablation**, listed as future work.
- **Proving rewrite equivalence in Lean,** which would remove the rewriter from the trusted base. Today it is tested against the original formulas.

Thank you again. The review made the paper more honest and the tool more sound.

— Michael Jagdeo and Jeff Dumps
