## 8. Limitations and Future Work

### 8.1 Supported input

`cm.py` reads self-contained, untyped TPTP problems. Since peer review, unsupported features are **rejected with an error**, never translated: an earlier version silently misread several of them (§5).

| Feature | Status |
|---|---|
| `fof`, `cnf` statements | supported |
| Roles: `axiom`, `hypothesis`, `definition`, `lemma`, `theorem`, `negated_conjecture`; `conjecture` (negated in the certificate) | supported (non-conjecture roles are treated as assumptions) |
| Connectives `~ & \| => <=>`; quantifiers `! ?`; `=`, `!=`; `$true`, `$false` | supported |
| Plain and quoted names (`cat` and `'cat'` are one symbol; `'X'` is never a variable) | supported, tested |
| `%` comments, including `%` inside quoted names | supported, tested |
| Connectives `<~>`, `<=`, `~\|`, `~&` | **rejected** |
| `$distinct`, other `$`-defined symbols, numbers, strings | **rejected** |
| `tff`, `thf`, `tcf`, `tpi` statements | **rejected** (the whole file) |
| `include(...)` | **rejected**; the benchmark records such inputs as *unsupported input* and keeps them in the denominator |
| One symbol used at two arities (TPTP's `p/1` and `p/2` are distinct symbols) | **rejected** (the model tables are keyed by name) |
| Purely propositional problems Vampire settles without printing a finite model | not handled (no model to certify) |

### 8.2 Limitations

| Limitation | Effect | Path forward |
|---|---|---|
| **No front end inside Lean** | Users write TPTP by hand | A Lean command that exports the current goal (first-order part) to TPTP and applies the certificate. This is the step that makes the tool adoptable. |
| **Reflected checking of nested quantifiers is slow** | PLA025+1 did not finish in 400 s reflected, against 4.4 s shallow, so we dispatch by fact share | Decode once, then check (`decode D = L`, then `check L`), so that lazy kernel evaluation stops re-decoding subformulas inside quantifier loops |
| **Trusted translation and rewriting** | A bug here can certify the wrong statement. It happened once (§5) and was caught by an independent check; peer review prompted a second class (silent misreading of unsupported syntax), now closed by fail-closed parsing. An audit of every archived input (`bench/input-audit.json`) found 3 development inputs with unsupported syntax; all 3 were *no model*, so no certificate was affected. Fail-closed parsing also shares its lexer with the test oracle, so correlated lexing errors remain possible. | Prove the rewrites in Lean, or emit both the original and the rewritten formula and prove them equivalent |
| **Untyped first-order logic only** | No sorts, arithmetic or higher-order input | TPTP `tff` sorts, using Vampire's multi-sorted models |
| **Vampire's limits are our limits** | 23 of 100 sampled problems had no model within 30 s; 11 of them are rated 1.00 by TPTP | Longer limits; other finders such as Mace4 or SAT-based search |
| **Some formats are unread** | Purely propositional problems that Vampire settles without printing a finite model | Parse Vampire's other model formats |
| **Lean-version effects** | Lean 4.13's limit of about 20,600 declarations per file may not hold on Lean ≥ 4.33, which changed how kernel recursion is bounded | Re-test on current Lean before reporting upstream |
| **Spinoza encoding** | Our 2-element models let objects be both substances and attributes, as Nakamura's axioms allow | A sorted encoding |
| **Sample, not census** | A 100-problem development set (the first 20 picked by domain) and a 100-problem held-out set (§6.2.1) | The full 2,561, now cheap with caching and indexing |
| **Hybrid dispatch threshold** | The 90% fact-share threshold was chosen during development, and only a few problems use reflection | Validate it on problems with intermediate fact shares |
| **Non-derivability, not independence** | A counter-model shows a target does not follow; independence also needs its negation not to follow | Run both directions in `ablate.py` |
