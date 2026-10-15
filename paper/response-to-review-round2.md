# Response to the second-round assessment: *Lean on Vampire Models*

**To:** the reviewer (Manus AI) · **From:** Michael Jagdeo and Jeff Dumps · **Date:** 15 October 2026

Thank you. The second round was precise about what still needed evidence rather than assertion, and it caught two statements in our first response that were wrong. We correct those first. Then we answer the four outstanding items in order.

## Corrections to our first response

1. **"None of our benchmark or example problems used these features": wrong.**
   - **Method:** we ran every archived input through the fail-closed parser. Each file passes through `cm.problem()` and every formula through `cm.lean()`. The method and per-file results are in `bench/input-audit.json`.
   - **Development set:** **3 of the 100 inputs use unsupported syntax.**
     - `BIO001+1`: a string literal;
     - `HWV042+1` and `KRS244+1`: the connective `<~>`.
   - **Example problems:** 0 of the 15 use unsupported syntax.
   - **No certificate was affected.** In both earlier runs, Vampire, reading the original file, found no finite model for these 3 within 30 s. Nothing was translated, so no certificate was produced from a misread formula. In the final run they are reported as **unsupported input**, not as *no model*.

2. **"The raw-source oracle would have caught a mismatch": overstated.** The oracle and `cm.py` share a lexer. The oracle detects translation errors only for constructs its own parser reads correctly. A lexing error common to both would go undetected. The paper now says so (§8.2).

3. **"Truncated data is covered": overstated.** `tests/Boundary.lean` contains one decoder test. It shows that a token stream with too little fuel decodes to ⊥, which is never `Good`. That documents a behaviour; it is not a rejection guarantee. The decoder does not detect truncated or miscounted streams in general (§4.3), and the test's comment now says so.

4. **The theorem in our letter was transcribed with dot notation inconsistently.** Item 1 below gives the exact compiling declaration and its `#check`.

## 1. The proof chain, and its use in both output paths

**The reflected path.** This is the exact generated text for `examples/transitive_cnf.p` (`Refl/transitive_cnf.lean`):

```lean
def fns : List (Nat × Nat) := …                   -- every (function id, arity) the problem uses
theorem valid : M.valid fns = true := by decide +kernel
theorem h0 : Good M fns (decode …) := good_of_check M fns _ (by decide +kernel)
theorem good : Good M fns problem := …           -- assembled with good_append / good_facts
theorem countermodel : ∀ φ ∈ problem, φ.Sat (M.toStructure (Model.valid_pos valid)) ⟨0, Model.valid_pos valid⟩ [] :=
  countermodel_of_good M fns problem valid good
```

Lean reports:

```
#check @transitive_cnf.countermodel
  : ∀ (φ : Fm), φ ∈ transitive_cnf.problem → Fm.Sat (transitive_cnf.M.toStructure ⋯) ⟨0, ⋯⟩ [] φ
#check @CM.Fm.Sat : {α : Type} → Structure α → α → List α → Fm → Prop
#print axioms transitive_cnf.countermodel  →  [propext, Quot.sound]
```

`Sat` takes the formula last, so `φ.Sat S d []` is `Fm.Sat S d [] φ`. The ⟨0, ⋯⟩ argument is the default element that the structure needs. Every certificate uses both justifying facts, because `countermodel_of_good` cannot be applied without them:

- `valid`: a non-empty domain, and closure of every function in `fns`;
- `good`: well-formedness and truth for every formula.

**On your completeness question:**

- **Functions:** `fns` is generated from the problem. Even if `fns` were wrong, `Fm.wf` rejects any function application whose (id, arity) pair is not in `fns`, so a missing entry makes the certificate fail rather than pass.
- **Constants:** checked by `wf` at each use, against the domain size. Unused table entries are deliberately not checked, as you suggested.
- **Predicates:** the evaluator reads a predicate's truth table at the arity of each use. Before this round, one name used at two arities would have shared a table. **`cm.py` now refuses any problem that uses a symbol at two arities** (TPTP treats `p/1` and `p/2` as distinct), with a test. The audit found no archived input that does this, so no result changes.
- **The guarantee is stated for the problem's signature** as used in its formulas. It is not a validation of every entry in Vampire's model file.

**The shallow path** (`Cm/transitive_cnf.lean`) proves each formula as an ordinary Lean proposition over an inductive type with one constructor per element:

```lean
inductive T | e1 | e2
abbrev «a» : T := T.e1
abbrev «r» (x0 x1 : T) : Prop := (4 >>> (1 * x0.idx + 2 * x1.idx)) % 2 = 1
theorem c0 : ∀ X Y : T, ¬ r X Y ∨ ∀ Z : T, ¬ r Y Z ∨ r X Z := by decide
theorem countermodel : … := ⟨c0, ⟨c1, c2⟩⟩
```

Here, validity holds by construction:
- the domain is non-empty;
- constants are constructors;
- functions are total Lean functions `T → … → T`;
- each symbol has one Lean type, so arities are fixed by elaboration;
- quantifiers range over all of `T`.

No validity theorem is needed, because there is no encoded semantics: the statement *is* first-order satisfaction in Lean's own logic. The remaining trusted step is the same as for reflection: whether the Lean statement transcribes the TPTP source.

**Rewording, as you asked:** "no certificate exists for an ill-formed model" now reads, in effect: under the strict axiom policy, no certificate exists for a model that fails the checked validity conditions (non-empty domain, closed functions at the arities used) or the checked well-formedness of each formula.

## 2. An immutable artifact

Ready for you now:

- **Snapshot:** commit **`[FINAL]`**, tagged `review-2026-10-15`, provided to you as a `git archive` tarball with SHA-256 `[SHA]`. It contains:
  - the revised manuscript (Markdown and PDF);
  - all sources and tests;
  - `lean-toolchain` (Lean 4.35.0) and the Vampire version string;
  - both certificate libraries for all 15 examples (`Cm/` shallow, `Refl/` reflected);
  - the raw benchmark logs, and `bench/recheck.log`.
- **`recheck.sh`:**
  - rebuilds everything;
  - prints `#print axioms` for all 30 shipped certificates;
  - replays three modules through the kernel from scratch with `leanchecker --fresh`, which ships with Lean 4.35: `Checker`, `AllShallow` (all 15 shallow certificates) and `AllReflected` (all 15 reflected certificates);
  - fails on any `sorryAx`, native-evaluation axiom or error.
- **On this machine, all three replays pass**:
  - `Checker`: 133 s;
  - `AllShallow`: 70 s;
  - `AllReflected`: 85 s.
- **Axioms:** every certificate depends only on `propext` and `Quot.sound`, or on no axioms at all.
- **Scope:** these are the shipped example certificates. The benchmark certificates are generated during runs and deleted afterwards, so the snapshot holds their logs and axiom output, not the `.olean` files. Rebuilding them is `bench.py`.

## 3. The frozen held-out evaluation, and version consistency

**Version relationship, shown rather than asserted:**

- `a2c16ab` (semantic validity), `72bb3e2` (fail-closed parser) and `a23fe9c` (arity guard; unsupported inputs recorded) are linear ancestors of the evaluation commit: `git merge-base --is-ancestor` succeeds for each.
- We **did not use `1a55aef` results.** That run crashed on an `include` in the held-out sample (`SYN000+2`), because the harness let `cm.py`'s rejection propagate. We fixed the harness to record such inputs, and froze again at **`a23fe9c`**.
- An earlier, partial held-out run overlapped with a mid-run parser change. **It was discarded**, and none of its outcomes are reported.
- `cm.py`, `bench.py` and `Checker.lean` are byte-identical between `a23fe9c` and the snapshot commit.

**Both sets were rerun on `a23fe9c`.** The run used a separate git worktree, the same 30 s Vampire limit, and the same model cache, so the finder's answers are unchanged. That includes the development set, so the 70/77 figure is no longer inherited from the old checker. Earlier figures stay in the paper only as labeled history.

[RESULTS TABLE]

**Categories** (each problem is in exactly one):
- **unsupported input:** rejected by the fail-closed parser; kept in the denominator.
- **no model:** Vampire found no finite model within 30 s. This is a resource-limited outcome, not a semantic result.
- **strict:** certified with kernel checks and the standard axioms only.
- **native-assisted:** certified only with `native_decide`, a larger trusted base.
- **not certified:** Vampire found a model, but Lean did not accept the certificate within the time limit.

**On 17/17 vs 53/60:** agreed. The paper now presents it as a descriptive breakdown only. The established problem is the non-uniform design itself.

## 4. Controlled performance runs on the revised implementation

The harness (`bench/perf.py`) has these properties:
- clean builds;
- the same Lean (4.35.0) and the same worker budget for both methods;
- shallow and reflected runs interleaved, and repeated.

Its definitions are written into every record:
- **Start:** before `cm.py` is invoked.
- **Stop:** after the final `#print axioms` check, which is included in the time.
- **Model search:** excluded, by reading Vampire's answer from the content-addressed cache.
- **Checker library:** prebuilt and not timed, for both methods.
- **Memory:** peak per process, and the peak aggregate across concurrent Lean processes, sampled every 0.2 s.
- **Final fresh replay** (`leanchecker`): timed separately, not included.

All reflected timings measure the **strengthened** certificate, with its validity and well-formedness checks. The earlier truth-only timings are not reused.

[PERFORMANCE TABLE]

The million-fact case remains described as a one-element throughput stress test.

## Terminology

`ablate.py` and §6.1 now say **subset-minimal** sufficient set, found by greedy deletion. It is not necessarily a smallest set, or the only one, and a Vampire timeout would leave minimality unresolved. Sufficiency of the two reported sets is supported by Nakamura's direct proofs. Each retained axiom's necessity is supported by a certified counter-model when it is removed.

We agree with the scoping in your "future work" section. The paper keeps the decode-once ablation, multidimensional scaling and a verified translator as future work, and limits its performance conclusions to the workloads measured.

— Michael Jagdeo and Jeff Dumps
