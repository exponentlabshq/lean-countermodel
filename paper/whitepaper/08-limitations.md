## 8. Limitations and Future Work

### 8.1 Supported input

`cm.py` reads self-contained, untyped TPTP problems. Since peer review, unsupported features are **rejected with an error**, never translated: an earlier version silently misread several of them (§5).

| Feature | Status |
|---|---|
| `fof`, `cnf` statements | supported |
| Every record read in full: whitespace and `%` comments between any two tokens; record names that are lower-case words, single-quoted words with any punctuation (`'thm.bool.TRUTH'`) or integers; optional annotations after the formula | supported, tested; text that is not a complete record makes the whole file **rejected** (§3.3) |
| Roles: `axiom`, `hypothesis`, `definition`, `assumption`, `lemma`, `theorem`, `corollary`, `plain`, `negated_conjecture`; `conjecture` (negated in the certificate) | supported (non-conjecture roles are treated as assumptions) |
| Other roles (`type`, `unknown`, `question`, `fi_*`, …) | **rejected** (no assertion meaning to certify) |
| Connectives `~ & \| => <=>`; quantifiers `! ?`; `=`, `!=`; `$true`, `$false` | supported |
| Plain and quoted names (`cat` and `'cat'` are one symbol; `'X'` is never a variable) | supported, tested |
| `%` comments, including `%` inside quoted names | supported, tested |
| `/* … */` block comments | **rejected** (`cm.py` strips only `%` comments; none of the 300 benchmark inputs uses them) |
| Connectives `<~>`, `<=`, `~\|`, `~&` | **rejected** |
| `$distinct`, other `$`-defined symbols, numbers, strings | **rejected** |
| `tff`, `thf`, `tcf`, `tpi` statements | **rejected** (the whole file) |
| `include(...)` | **rejected** by `cm.py`. The benchmark harness expands includes beforehand with `bench.expand` (trusted, now tested by `test_include_expansion`): each plain `include('Axioms/F.ax').` outside comments and quoted names is replaced by that axiom file. A *selective* include, `include('Axioms/F.ax', [names])`, is left in place, so the input is rejected and recorded as *unsupported input* (`SYN000+2`). An unresolved include, an include of a file that itself includes, or one outside `Axioms/` is refused. Originals, expansions and axiom files are recorded with SHA-256s against the official TPTP v9.3.1 release (`bench/inputs.json`) |
| One symbol used at two arities (TPTP's `p/1` and `p/2` are distinct symbols) | **rejected** (the model tables are keyed by name) |
| Purely propositional problems Vampire settles without printing a finite model | not handled (no model to certify) |

### 8.2 Limitations

| Limitation | Effect | Path forward |
|---|---|---|
| **No front end inside Lean** | Users write TPTP by hand | A Lean command that exports the current goal (first-order part) to TPTP and applies the certificate. This is the step that makes the tool adoptable. |
| **Reflected checking of nested quantifiers is slow** | PLA025+1 did not finish in 400 s reflected, against 4.4 s shallow, so we dispatch by fact share | Decode once, then check (`decode D = L`, then `check L`), so that lazy kernel evaluation stops re-decoding subformulas inside quantifier loops |
| **Trusted translation and rewriting** | A bug here can certify the wrong statement. It happened once (§5) and was caught by an independent check; peer review prompted a second class (silent misreading of unsupported syntax), now closed by fail-closed parsing. An audit of the archived inputs at `1a55aef` (`bench/input-audit.json`, on the earlier scraped inputs) found 3 development inputs with unsupported syntax; all 3 were *no model*, so no certificate was affected. The final runs apply the same checks to the rebuilt inputs before Vampire runs, and their *unsupported input* verdicts supersede that audit. The frozen run of the second sample then exposed variable capture: `GEG001+1` binds a variable named `T`, the domain type's name; Lean rejected the certificate, and variables are now emitted primed (`X'`). The input rebuild from the TPTP release (§6.2) exposed include expansion inside comments, which had changed two inputs: two benchmark no-model-found outcomes concerned altered inputs and are superseded by the corrected runs. **Round-4 review: record omission.** The regular expression that found records skipped any record it could not match, and the test oracle had copied it, so both agreed on a weakened problem. It dropped records from 9 benchmark inputs, 8 of which had been reported certified; Lean had checked only the formulas it was given (§6.2.2). Records are now read by a total, fail-closed reader, and the oracle has its own. The oracle still shares the in-formula lexer and the variable collector with `cm.py`, so correlated errors in those two helpers remain possible. | Prove the rewrites in Lean, or emit both the original and the rewritten formula and prove them equivalent |
| **Translator robustness** | The third sample exposed two crashes, reported as failures: `cm.py`'s recursive-descent translator exceeds Python's recursion limit on very deep nesting (`KRS290-1`), and the benchmark's shallow path does not pass the output directory that `cm.py` needs for problems over 2,000 formulas (`SYO595-1`) | An iterative parser; pass the output directory and build the modules, as the reflected path already does |
| **Untyped first-order logic only** | No sorts, arithmetic or higher-order input | TPTP `tff` sorts, using Vampire's multi-sorted models |
| **Vampire's limits are our limits** | Within 30 s, no model for 19, 34 and 29 of the three 100-problem samples. By the TPTP headers, 18 of those 82 have no finite model at all and one needs 64 elements; 9 hit the finite-model builder's encoding limit; the other 54 timed out without a documented cause (§6.2.1) | Longer limits; other finders such as Mace4 or SAT-based search |
| **Some formats are unread** | Purely propositional problems that Vampire settles without printing a finite model | Parse Vampire's other model formats |
| **Lean-version effects** | Lean 4.13's limit of about 20,600 declarations per file may not hold on Lean ≥ 4.33, which changed how kernel recursion is bounded | Re-test on current Lean before reporting upstream |
| **Spinoza encoding** | Our 2-element models let objects be both substances and attributes, as Nakamura's axioms allow | A sorted encoding; as §6.1 explains, separating substances from attributes would revise the relevant bridges or the signature, so it would be a different reconstruction, not a refinement of this one |
| **Sample, not census** | Three 100-problem samples: a development set (the first 20 picked by domain), a second sample used for debugging, and a third drawn and frozen before any result (§6.2.1) | The full 2,561, now cheap with caching and indexing |
| **Hybrid dispatch threshold** | The 90% fact-share threshold was chosen during development, and only a few problems use reflection | Validate it on problems with intermediate fact shares |
| **Non-derivability, not independence** | A counter-model shows a target does not follow; independence also needs its negation not to follow | Run both directions in `ablate.py` |
