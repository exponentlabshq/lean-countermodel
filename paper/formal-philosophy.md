# From Philosophical Argument to Machine-Checked Axioms
## Lean, Vampire, and the Emerging Science of Formal Philosophy

**A research agenda for computational metaphysics, axiomatic analysis, and machine-checked philosophical argument**

**Date:** October 15, 2026

### Abstract

Can philosophical systems be evaluated with the same rigor used to verify mathematical theorems? Recent developments in interactive theorem proving and automated reasoning suggest that at least some longstanding philosophical disputes can be reformulated as precise questions about axioms, logical consequences, and countermodels.

This paper examines the potential of Lean and Vampire for analyzing axiomatic systems associated with Spinoza, Leibniz, Kant, Wittgenstein, and other philosophers. Its central case study is Yuki Nakamura's 2026 Lean 4 formalization of Spinoza's *Ethics*, which investigates whether selected propositions follow from Spinoza's stated axioms and a proposed Principle of Sufficient Reason (PSR) augmentation. Related work in computational philosophy demonstrates that automated theorem provers and model finders have already been used to analyze ontological arguments, metaphysical systems, and theories of possible worlds.

The paper distinguishes proof verification from automated proof search, and both from the philosophical interpretation of formal models. It identifies existing repositories, published research, methodological limitations, and a proposed research program combining Lean, Vampire, model finding, and textual scholarship.

The principal thesis is that formal methods can transform philosophical disagreements into reproducible experiments on explicitly stated assumptions. They cannot independently determine whether a formal reconstruction faithfully captures a philosopher's intentions, nor whether a logically valid metaphysical theory describes reality.

**Keywords:** Lean 4, Vampire, formal philosophy, axiomatic systems, computational metaphysics, Spinoza, Leibniz, Kant, Wittgenstein, modal logic, countermodels, proof assistants.

### Status, October 2026: stages 3–6 are now built

This agenda was written as a proposal. Its workflow (§7) is now partly implemented by [`lean-countermodel`](https://github.com/exponentlabshq/lean-countermodel), for first-order reconstructions:

| Agenda stage | Implementation |
|---|---|
| 3. Automated exploration with Vampire | `cm.py` runs `vampire -sa fmb` on a TPTP reconstruction |
| 4. Independent model checking | An independent evaluator, corrupted-model tests, rewrite-equivalence tests |
| 5. Proof verification with Lean | Every counter-model becomes a certificate checked by Lean's kernel, including against Nakamura's own library |
| 6. Axiom ablation | `ablate.py` produces an assumption-dependency map, with a kernel-checked counter-model for each "needed" |

The first map, of Nakamura's register for *Ethics* I, is reported in §8.1. Stages 1, 2 and 7 (textual reconstruction, axiomatization and interpretive review) remain human work, as this agenda insists.

---

## 1. Introduction: Can philosophy become experimentally testable?

Philosophers frequently disagree about whether a conclusion follows from a set of premises. Such disagreements can persist for centuries because natural-language arguments permit ambiguity about definitions, hidden assumptions, inference rules, and the intended meaning of a conclusion.

Consider a familiar question: does Spinoza's argument establish that only one substance exists, or does the conclusion require additional metaphysical commitments?

A traditional response involves textual interpretation and competing reconstructions of the argument. A formal response introduces a complementary method:

1. Define the entities and relations involved.
2. Translate the relevant premises into an explicit formal language.
3. Attempt to derive the disputed conclusion.
4. Search for a model satisfying the premises while falsifying that conclusion.
5. Identify which additional assumptions eliminate the countermodel.
6. Repeat the process under alternative interpretations.

The result is not an automated judgment of philosophical truth. It is a more precise account of what follows from a particular reconstruction.

The field of computational philosophy already has substantial precedent for this approach. The Stanford Encyclopedia of Philosophy's entry on computational philosophy documents the use of automated theorem provers and model finders to investigate metaphysical object theory, possible worlds, Leibnizian modal claims, Plato's theory of Forms, and ontological arguments.

Source: [Stanford Encyclopedia of Philosophy — Computational Philosophy](https://plato.stanford.edu/entries/computational-philosophy/index.html).

The opportunity is to develop this work into a reproducible discipline in which philosophical reconstructions, assumptions, proof artifacts, countermodels, and interpretive objections are openly available.

## 2. Two complementary technologies

### 2.1 Lean: A trusted environment for verifying proofs

[Lean 4](https://github.com/leanprover/lean4) is a programming language and interactive theorem prover. Its type system and trusted kernel allow it to check whether a proposed proof follows from the declarations and assumptions in a formal development.

A Lean project can encode definitions, axioms, theorems, and proofs. It can also represent mathematical structures that demonstrate the consistency of particular combinations of assumptions relative to the underlying formal system.

Lean's significance for philosophy lies in its ability to make dependencies explicit. A proposition may be formally established only because the development contains an auxiliary axiom, a definition that encodes a substantive commitment, or an assumption imported from another theory.

A proof that compiles is therefore not automatically a proof that a philosopher's original argument succeeds. It establishes a result within the formal system that was encoded.

Official resources:

- [Lean 4 source repository](https://github.com/leanprover/lean4)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Lean community documentation](https://lean-lang.org/)

### 2.2 Vampire: Automated reasoning and proof search

[Vampire](https://github.com/vprover/vampire) is an automated theorem prover that searches for logical consequences using automated reasoning techniques, particularly resolution and superposition.

A researcher supplies a formal problem, commonly in the TPTP format. Vampire then searches for a proof of the conjecture, typically by attempting to establish the unsatisfiability of the premises together with the negation of the conjecture.

Vampire can also operate in satisfiability-oriented modes and supports finite-model-building techniques in relevant configurations. Its precise capabilities depend on the problem's logic, encoding, and solver configuration.

This makes it useful for questions such as:

- Does the conclusion follow from the axioms?
- Do the axioms jointly lead to a contradiction?
- Can a finite structure satisfy the premises while falsifying a proposed theorem?
- Which assumptions are relevant to a particular inference?

Resources:

- [Vampire source repository](https://github.com/vprover/vampire)
- [Vampire Guide: First-Order Theorem Proving, TPTP, and Vampire](https://vprover.github.io/vampireGuide/docs/lectures/l1/)
- [TPTP problem library and resources](https://www.tptp.org/)

### 2.3 The division of labor

The distinction is important:

| Capability | Lean | Vampire |
|---|---|---|
| Check a formal proof | Core strength | Can produce proof output, with verification depending on the workflow |
| Search automatically for proofs | Tactics and external integrations | Core strength |
| Expose dependence on assumptions | Explicit formal declarations | Explicit premise sets and proof dependencies |
| Explore countermodels | Can encode and verify concrete models | Supports finite-model-building methods |
| Serve as a trusted proof kernel | Yes | Not its primary role |
| Interpret philosophical texts | No | No |

The tools are complementary, not interchangeable.

A productive workflow would use Vampire to explore a first-order reconstruction, identify promising derivations or candidate countermodels, and then encode significant results in Lean for independent checking. Translating results between the systems requires care: differences in logic, semantics, and formalization can invalidate a naive translation.

The physical analogy is an engineering laboratory. Vampire is a search engine that explores possible designs and stress configurations. Lean is the inspection process that certifies a specified mathematical derivation against its formal rules.

Neither determines whether the engineer chose the correct requirements.

## 3. Case study: Spinoza's *Ethics*

### 3.1 Nakamura's 2026 formalization

The most directly relevant example identified in this research is Yuki Nakamura's *Bennett's Conjecture in Lean 4: Counter-Models for the PSR-Reducibility of Spinoza's Propositions V and XIV*.

**Paper:** [arXiv:2605.02331](https://arxiv.org/abs/2605.02331)

**Code:** [Nakammura/spinoza-ethica-lean](https://github.com/Nakammura/spinoza-ethica-lean)

The project formalizes selected load-bearing propositions in Part I of Spinoza's *Ethics*, particularly the argument concerning substance, attributes, and God. It includes a modal S5 reconstruction and explicit auxiliary assumptions.

The paper addresses a dispute involving Jonathan Bennett and Michael Della Rocca.

Bennett argues that Spinoza's demonstration of Proposition V does not establish its full conclusion from the resources Spinoza provides. Della Rocca argues that the Principle of Sufficient Reason can supply a route to the desired result.

Nakamura formalizes a specified reconstruction of the competing commitments.

The reported results are significant:

1. The formalization derives a weaker result: substances sharing all attributes are identical.
2. It does not derive the stronger, shared-attribute formulation of Proposition V from the tested assumptions.
3. A finite countermodel satisfies those assumptions while falsifying the stronger conclusion.
4. A related countermodel addresses a universality commitment associated with Proposition XIV.
5. The study distinguishes assumptions that can be reformulated in terms of the PSR from commitments that remain irreducible under the tested augmentation.

These results do not establish that Spinoza's argument fails under every possible interpretation. The paper explicitly leaves stronger versions of the PSR and alternative reconstructions open.

### 3.2 Why the result matters

The formalization makes a distinction visible that prose debate can obscure: an argument may establish a weaker proposition while appearing to establish a stronger one.

Suppose a philosophical system contains assumptions \(A\) and proposes conclusion \(C\). The formal question is whether:

\[
A \models C
\]

If a model \(M\) satisfies every assumption in \(A\) but falsifies \(C\), then \(M\) is a countermodel:

\[
M \models A
\quad\text{and}\quad
M \not\models C
\]

This demonstrates that \(C\) is not a semantic consequence of \(A\) in the chosen logic.

Lean can verify the finite structure and its relevant properties. The conclusion about non-derivability follows relative to the formalization and the assumed soundness of the underlying reasoning system.

This is more informative than merely failing to find a proof. Search failure could reflect insufficient computational resources; a verified countermodel provides positive evidence of non-entailment.

### 3.3 A caution about philosophical fidelity

Formalization necessarily involves interpretation. The researcher must decide how to translate terms such as *substance*, *attribute*, *cause*, *conceived through*, and *sufficient reason*.

Different translations can encode different philosophical positions.

Consequently, a strong formal philosophy project should publish at least three distinct artifacts:

- The original textual passage and translation.
- The formal representation of its claims.
- An interpretive argument explaining why that representation is defensible.

The first artifact is textual evidence; the second is a machine-checkable model; the third remains open to philosophical criticism.

## 4. Existing projects and research artifacts

The following repositories provide starting points for further investigation. Their existence does not imply that all their philosophical claims have been independently validated.

### 4.1 Spinoza

**Repository:** [spinoza-ethica-lean](https://github.com/Nakammura/spinoza-ethica-lean)

**Paper:** [Bennett's Conjecture in Lean 4](https://arxiv.org/abs/2605.02331)

This is the strongest direct match to the research question. The repository describes a formalization of selected propositions in Part I, an auxiliary-axiom register, modal S5 results, and explicit countermodels.

It also documents a method for attempting to weaken auxiliary assumptions and testing whether the original result remains derivable.

**Recommended research:** extend the formalization to alternative readings of Proposition V, stronger PSR formulations, and further propositions in the *Ethics*.

### 4.2 Wittgenstein

**Repository:** [rjwalters/tractatus](https://github.com/rjwalters/tractatus)

This repository is described as a project concerning Wittgenstein's *Tractatus Logico-Philosophicus*. As of 15 October 2026 it is mainly a TeX paper collaboration, with no stars; it is not, on inspection, a Lean formalization. Its associated project materials discuss model-theoretic semantics, independence, expressibility, and the distinction between structural properties and model-dependent assumptions.

The project should be treated as an ongoing research artifact rather than a settled, comprehensive verification of the *Tractatus*. The philosophical adequacy of its reconstruction requires independent assessment, and its current source and build status should be checked before relying on particular results.

**Recommended research:** test whether claims about logical form, compositionality, truth-functional structure, and the limits of expressibility hold across all models satisfying a specified reconstruction.

A useful distinction is between:

- A property true in every model of the axioms.
- A property true only in models satisfying additional assumptions.
- A property that cannot be expressed in the chosen formal language.

These distinctions could turn parts of Wittgenstein's philosophy into a structured study of semantic invariants and formal limits.

### 4.3 Leibniz

**Repository:** [Mega-Therion/4Leibniz](https://github.com/Mega-Therion/4Leibniz)

This project describes a Lean 4 framework for relational information geometry, epistemic logic, and philosophical foundations. As of 15 October 2026 its code is mainly TypeScript, so its Lean content should be checked directly.

It is a relevant candidate for inspection, but should not be treated as an established formal reconstruction of Leibniz's entire metaphysics. Its formal claims, dependencies, and proof status need to be checked directly.

**Recommended research:** formalize selected principles, such as the Principle of Sufficient Reason, the identity of indiscernibles, and the distinction between necessary and contingent truths. Then test which results depend on each principle.

The critical question is whether the formal system reproduces Leibniz's actual commitments or a modern interpretation inspired by them.

### 4.4 Buddhist logic and the Catuṣkoṭi

**Repository:** [modal-catuskoti-lean](https://github.com/rollofthedice/modal-catuskoti-lean)

This repository implements a Lean 4 formalization of *The Modal Catuṣkoṭi: Formalizing Emptiness in Classical Modal Logic*.

Its documented construction assigns four values to atomic propositions while using a bivalent satisfaction relation for complex formulas. The project reports satisfiability and unsatisfiability results under different modal systems.

This is a concrete example of how formal methods can investigate a philosophical or logical structure without assuming that every component must be expressed through ordinary classical truth values.

The caveat is substantial: a formalization of the Catuṣkoṭi operator is not equivalent to a complete formalization of Nāgārjuna's philosophy.

**Recommended research:** compare alternative semantics, test which results are specific to the chosen four-valued representation, and distinguish logical properties from interpretive claims about emptiness.

### 4.5 General-purpose formal logic

**Resources:**

- [Formalized Formal Logic — Foundation](https://github.com/FormalizedFormalLogic/Foundation)
- [Lean 4](https://github.com/leanprover/lean4)
- [Vampire](https://github.com/vprover/vampire)

Formal logic libraries provide reusable definitions and results for classical logic, intuitionistic logic, modal logic, semantics, and related topics.

Rather than building every system from scratch, a research program can reuse these foundations while keeping the philosopher-specific axioms separate.

This separation helps reveal which results arise from the general logic and which depend on the philosophical commitments being studied.

## 5. Earlier precedent: computational philosophy predates Lean

It would be inaccurate to suggest that computational analysis of philosophical systems began with Lean or Vampire.

The Stanford Encyclopedia of Philosophy documents earlier uses of automated provers and model finders, including Prover9 and Mace, in work on metaphysical object theory, possible worlds, Leibnizian modal claims, Plato's theory of Forms, and ontological arguments.

One particularly relevant reference is:

**Fitelson, Branden, and Edward N. Zalta (2007).** “Steps Toward a Computational Metaphysics.” *Journal of Philosophical Logic*.

See the [Computational Philosophy bibliography](https://plato.stanford.edu/entries/computational-philosophy/index.html) for this and related research.

Another relevant line of work concerns ontological arguments. Oppenheimer and Zalta found a simplification of Anselm's argument computationally (2011). Horner reconstructed an ontological argument in Spinoza's *Ethics* with computational assistance (2019). Benzmüller ported Gödel's and Scott's variants to Lean 4 in 2026, with Isabelle's Nitpick results. Automated reasoning has been used to investigate the validity of different formulations of arguments for God's existence, demonstrating that philosophical disputes can sometimes be made more precise by specifying the logical commitments of each argument.

The novelty of the present research agenda is therefore not the first application of computing to philosophy. It is the opportunity to combine:

1. Modern proof assistants with small trusted kernels.
2. Automated first-order reasoning.
3. Explicit model construction.
4. Version-controlled, reproducible research artifacts.
5. Systematic comparison of alternative axiomatizations.

## 6. What should be tested?

A philosophical axiomatic system can be investigated along several dimensions.

### 6.1 Entailment

Does the conclusion follow from the stated assumptions?

Given a theory \(T\) and a proposition \(P\), investigate whether:

\[
T \models P
\]

A positive result requires a valid proof in the selected formalization. A countermodel can establish that \(P\) is not a consequence of \(T\) under the selected semantics.

### 6.2 Consistency

Can the assumptions be jointly satisfied?

A contradiction in a theory may reveal incompatible commitments. Conversely, a concrete model can demonstrate consistency relative to the underlying logic and the assumptions used to construct it.

Failure to find a contradiction does not establish consistency. Formal consistency proofs also require careful attention to the metatheory in which they are carried out.

### 6.3 Independence

Can an axiom be derived from the remaining axioms?

For an axiom \(A\) and the remaining theory \(T\), ask whether:

\[
T \models A
\]

If \(T\) has a model in which \(A\) is false, then \(A\) is not a semantic consequence of \(T\).

This is particularly useful when a philosophical system contains an apparently foundational principle that may actually be derivable from other commitments—or may be an indispensable additional assumption.

### 6.4 Completeness and decidability

Can every statement in a specified language be proved or refuted? Is there an algorithm that decides every instance of the relevant problem?

These are different questions.

First-order logic is complete in the semantic sense associated with Gödel's completeness theorem, but its general validity problem is undecidable. A particular axiomatic theory may have additional limitations or stronger properties.

Lean and Vampire do not automatically settle the completeness or decidability of arbitrary philosophical systems. Such questions require mathematical arguments about the formal language and theory.

### 6.5 Sensitivity to assumptions

Which conclusions survive when a premise is removed, weakened, or replaced?

This may be the most useful dimension for philosophy. Rather than asking whether a theory is simply valid or invalid, a researcher can map the dependencies of its conclusions.

A result may be:

- A consequence of the original axioms.
- A consequence only after an auxiliary assumption is added.
- Equivalent to a stronger assumption under the chosen definitions.
- False in a model satisfying the original assumptions.
- Unresolved within the current formalization.

This produces a more nuanced picture than a binary verdict.

## 7. A proposed Lean–Vampire research architecture

The following is a proposed workflow, not a claim that an integrated system already exists for all the philosophers discussed.

### Stage 1: Textual reconstruction

Select a small, clearly bounded argument from a primary source.

Record the original text, translation, interpretive alternatives, and the intended conclusion. Have subject-matter scholars review the translation into formal concepts.

### Stage 2: Axiomatization

Encode the definitions and assumptions in a formal language.

Where possible, separate:

- Definitions.
- Explicit premises in the text.
- Interpretive bridge principles.
- Additional metaphysical commitments.
- The target conclusion.

This distinction prevents an auxiliary assumption from silently becoming part of the philosopher's original position.

### Stage 3: Automated exploration with Vampire

Translate a suitable first-order fragment into TPTP.

Ask Vampire to search for proofs of selected conclusions and to explore satisfiability or finite-model-building problems where supported.

For each failed proof search, distinguish resource exhaustion from an actual countermodel or a formally established non-entailment result.

### Stage 4: Independent model checking

Construct or extract a candidate countermodel and check whether it satisfies all the intended premises while falsifying the target conclusion.

The model must be interpreted carefully. A model in an encoding is not automatically a plausible metaphysical world; it is a structure satisfying a specified formal language.

### Stage 5: Proof verification with Lean

Encode the significant results in Lean.

Use the trusted kernel to check formal proofs and concrete model properties. Track all assumptions, axioms, imported theorems, and unfinished proof obligations.

A failed compilation or unresolved proof hole must not be reported as a theorem.

### Stage 6: Axiom ablation

Systematically remove or weaken one assumption at a time.

For every major conclusion, record whether it remains derivable, whether a countermodel becomes available, or whether the result is unresolved.

This yields an assumption-dependency map.

### Stage 7: Interpretive review

Return to the philosophical text.

Ask whether the formalization preserves the intended meaning, whether the countermodel exploits an ambiguity, and whether the additional assumptions are philosophically defensible.

The final publication should report both the machine-checked result and the limits of the interpretation.

## 8. Proposed research program by philosopher

### 8.1 Spinoza: the architecture of substance monism

**Priority: immediate extension of existing work.**

Research questions:

1. Which propositions in Part I depend on the auxiliary axioms introduced during formalization?
2. Can stronger versions of the PSR derive Proposition V without simply restating the desired conclusion?
3. Can the argument for Proposition XIV be reconstructed with fewer independent metaphysical commitments?
4. Do alternative formal readings of Spinoza's definitions produce different dependency structures?

The existing Lean repository provides a baseline against which alternative reconstructions can be compared.

**First result: the assumption-dependency map (stage 6).** For the first-order layer of Nakamura's register (3 definitions held fixed, the 8 substantive stated axioms, and the sufficient-reason principles A22, A25 and A26), `ablate.py` reports:

| Proposition | Follows from the register? | Depends on |
|---|---|---|
| Weak P5: substances sharing all attributes are identical | yes | **A22 only.** Without it, a kernel-checked 2-element counter-model exists. |
| A15: every attribute of a substance belongs to God | yes | **A25 and A26,** each necessary, with kernel-checked counter-models |
| A12: an attribute belongs to one substance | **no** | A kernel-checked 2-element model satisfies all eleven axioms |

What this shows:
- **None of Spinoza's eight stated axioms is needed for these results.** In this register the work is done by the definitions and the added principles of sufficient reason, which is a precise form of the Bennett–Della Rocca question.
- **A12 remains underivable even with plenitude and God's uniqueness added,** a stronger irreducibility result than Nakamura's.
- **Interpretive caveat (stage 7):** in these counter-models one object can be both a substance and an attribute. The register permits this. Whether Spinoza does is a question for interpretation, which is exactly where this agenda says the machine stops.

### 8.2 Leibniz: necessary truths, sufficient reasons, and identity

**Priority: high-value comparative study.**

The key question is whether Leibniz's principles form an independent axiomatic system or whether some commitments can be derived from others.

Potential experiments include:

- Encode the identity of indiscernibles.
- Distinguish necessary truths from contingent truths.
- Represent possible worlds and accessibility relations.
- Test whether selected versions of the PSR entail proposed modal conclusions.
- Compare Leibnizian assumptions with those used in the Spinoza formalization.

The purpose would not be to collapse Leibniz and Spinoza into a single theory. It would be to identify exactly where their formal commitments overlap and where they diverge.

### 8.3 Kant: antinomies and incompatible premises

**Priority: exploratory.**

Kant's antinomies offer a useful target because they involve opposing arguments about the universe, causality, and the composition of reality.

A formal investigation should reconstruct each argument separately before comparing them.

The research questions would be:

- Are both conclusions derivable from their respective premises?
- Do the arguments rely on the same underlying assumptions?
- Are the premises jointly inconsistent, or do they concern different interpretations of the relevant concepts?
- Can the apparent contradiction be resolved by changing the scope or semantics of a key term?

A formal contradiction would not, by itself, settle Kant's philosophical diagnosis of the antinomies. The interpretation of the formal results remains essential.

### 8.4 Wittgenstein: semantics, representation, and expressibility

**Priority: ambitious foundational project.**

The *Tractatus Logico-Philosophicus* presents distinctive challenges because some of its central claims concern the limits of meaningful representation and what can be said or shown.

A formalization must therefore avoid assuming that every aphorism is an ordinary proposition in one classical theory.

Potential directions include:

- Model the compositional structure of elementary propositions.
- Investigate the assumptions required for truth-functional representation.
- Distinguish semantic equivalence from structural identity.
- Explore whether claims about expressibility can be represented as metatheoretic statements.
- Compare the behavior of the reconstruction across alternative classes of models.

The existing [tractatus repository](https://github.com/rjwalters/tractatus) is a possible starting point, subject to independent evaluation of its source, formal claims, and philosophical interpretation.

The ambitious question is whether a formal reconstruction can identify structural limits within the language it describes, rather than merely translating every philosophical claim into an object-level theorem.

### 8.5 Comparative philosophy

**Priority: longer-term research.**

Once multiple reconstructions exist, compare them through shared logical vocabulary.

For example, a comparative project might investigate how Spinoza and Leibniz use explanatory principles, how Kant distinguishes kinds of necessity, or how Wittgenstein's semantic framework differs from the assumptions of classical metaphysics.

Such a project should not equate similar symbols with identical philosophical meanings. Shared formal vocabulary is a basis for comparison, not proof that two theories express the same view.

## 9. Limitations and risks

### 9.1 Formal validity is not historical fidelity

A proof may be flawless while its axioms misrepresent the philosopher. The formal system answers a conditional question: what follows if these assumptions and definitions are accepted?

### 9.2 The encoding can predetermine the result

A researcher may accidentally encode the conclusion into an auxiliary axiom. A rigorous study must audit the premises and explain why each one belongs in the reconstruction.

### 9.3 Search failure is not non-derivability

Automated theorem provers operate under resource limits and heuristic search strategies. A timeout or failure to find a proof does not show that no proof exists.

A countermodel can establish non-entailment within the relevant semantics. In Lean, a kernel-checked countermodel can support the non-derivability claim, subject to the formal system's soundness assumptions.

### 9.4 Consistency is not truth

A metaphysical theory can be consistent yet false. A countermodel demonstrates a logical possibility under the encoding, not a discovery about the actual structure of reality.

### 9.5 Some philosophical questions resist the chosen formal language

Questions about experience, value, meaning, historical context, and the use of concepts may not be adequately captured by a particular formalization. A responsible project should state what it leaves outside the model.

### 9.6 The tools do not eliminate human judgment

The tools can check derivations, expose hidden assumptions, and explore consequences. They cannot independently determine whether a translation is faithful, whether a distinction matters philosophically, or which interpretation best explains the historical text.

The appropriate standard is not the replacement of philosophical scholarship but its integration with formal methods.

## 10. Research deliverables and evaluation criteria

A serious research project should publish more than a paper announcing that a philosopher has been formalized.

Each project should include:

1. A textual corpus and explicit interpretation policy.
2. A formal specification of definitions and axioms.
3. Machine-checkable proof artifacts.
4. Countermodels for selected non-entailment claims.
5. A dependency map for auxiliary assumptions.
6. Reproducible build instructions and pinned tool versions.
7. A record of unresolved claims and incomplete proofs.
8. A comparison between the formal result and the original philosophical argument.
9. An independent review of both formal correctness and interpretive fidelity.

The primary evaluation metrics should be correctness, reproducibility, interpretive transparency, and explanatory value—not the number of propositions translated into code.

A smaller formalization that isolates one disputed assumption may contribute more than a much larger project that encodes a text without revealing the dependency structure of its arguments.

## 11. Conclusion

Lean and Vampire provide complementary capabilities for investigating axiomatic philosophical systems. Lean supplies a trusted environment for checking formal derivations. Vampire searches automatically for consequences and supports satisfiability-oriented exploration. Together with explicit model construction, they can help distinguish valid inference from hidden assumptions and unsupported conclusions.

The Spinoza formalization is a particularly useful case because it targets a real interpretive dispute and produces a concrete countermodel under specified assumptions. Other repositories concerning Wittgenstein, Leibniz, and Buddhist logic suggest additional directions, though their maturity and philosophical adequacy vary.

The broader research opportunity is a reproducible science of formal philosophical reconstruction: not a machine that decides which philosophers were right, but a method for discovering exactly what a philosophical position commits us to.

The most important output may be a map of the assumptions that hold a theory together.

**The decisive question is not simply whether a philosopher's conclusion can be proved. It is whether the conclusion survives when every additional assumption is made explicit and tested.**

---

## References and research links

### Primary formalization projects

1. **Nakamura, Yuki (2026).** *Bennett's Conjecture in Lean 4: Counter-Models for the PSR-Reducibility of Spinoza's Propositions V and XIV.*  
   Paper: https://arxiv.org/abs/2605.02331  
   Source code: https://github.com/Nakammura/spinoza-ethica-lean

2. **Wittgenstein formalization project.**  
   https://github.com/rjwalters/tractatus

3. **4Leibniz — formal relational information geometry and automated verification in Lean 4.**  
   https://github.com/Mega-Therion/4Leibniz

4. **The Modal Catuṣkoṭi — Lean 4 formalization.**  
   https://github.com/rollofthedice/modal-catuskoti-lean

5. **Formalized Formal Logic — Foundation.**  
   https://github.com/FormalizedFormalLogic/Foundation

### Software and technical documentation

6. **Lean 4.**  
   https://github.com/leanprover/lean4

7. **Theorem Proving in Lean 4.**  
   https://lean-lang.org/theorem_proving_in_lean4/

8. **Vampire automated theorem prover.**  
   https://github.com/vprover/vampire

9. **Vampire Guide: First-Order Theorem Proving, TPTP, and Vampire.**  
   https://vprover.github.io/vampireGuide/docs/lectures/l1/

10. **Thousands of Theories from the TPTP problem library and related resources.**  
    https://www.tptp.org/

### Computational philosophy and historical precedent

11. **Stanford Encyclopedia of Philosophy.** *Computational Philosophy.*  
    https://plato.stanford.edu/entries/computational-philosophy/index.html

12. **Fitelson, Branden, and Edward N. Zalta (2007).** *Steps Toward a Computational Metaphysics.* See the computational philosophy bibliography above for publication details and related work.

### Classical philosophical sources for future formalization

13. **Spinoza.** *Ethics.* Public-domain English translation by R. H. M. Elwes:  
    https://www.gutenberg.org/ebooks/3800

14. **Wittgenstein.** *Tractatus Logico-Philosophicus.* A starting point for bibliographic research and formal reconstruction is the project repository listed above.

15. **Leibniz.** *Monadology* and writings on the Principle of Sufficient Reason. Formalization should be based on explicitly identified editions and passages rather than secondary summaries alone.

16. **Kant.** *Critique of Pure Reason*, particularly the Transcendental Dialectic and the antinomies. Any formal reconstruction should distinguish Kant's presentation of the arguments from his diagnosis of their limitations.

---

### Scope note

This paper is a research agenda and literature-grounded synthesis, not a systematic review of every GitHub repository or every application of automated theorem proving to philosophy. The Spinoza paper and the linked software projects are concrete starting points; the proposed research on Leibniz, Kant, and comparative formal metaphysics remains to be developed and evaluated.
