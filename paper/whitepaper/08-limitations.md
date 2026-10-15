## 8. Limitations and Future Work

| Limitation | Effect | Path forward |
|---|---|---|
| **No front end inside Lean** | Users write TPTP by hand | A Lean command that exports the current goal (first-order part) to TPTP and applies the certificate. This is the step that makes the tool adoptable. |
| **Reflected checking of nested quantifiers is slow** | PLA025+1 did not finish in 400 s reflected, against 4.4 s shallow, so we dispatch by fact share | Decode once, then check (`decode D = L`, then `check L`), so that lazy kernel evaluation stops re-decoding subformulas inside quantifier loops |
| **Trusted translation and rewriting** | A bug here can certify the wrong statement. It happened once (§5) and was caught by an independent check. | Prove the rewrites in Lean, or emit both the original and the rewritten formula and prove them equivalent |
| **Untyped first-order logic only** | No sorts, arithmetic or higher-order input | TPTP `tff` sorts, using Vampire's multi-sorted models |
| **Vampire's limits are our limits** | 23 of 100 sampled problems had no model within 30 s; 11 of them are rated 1.00 by TPTP | Longer limits; other finders such as Mace4 or SAT-based search |
| **Some formats are unread** | Purely propositional problems that Vampire settles without printing a finite model | Parse Vampire's other model formats |
| **Lean-version effects** | Lean 4.13's limit of about 20,600 declarations per file may not hold on Lean ≥ 4.33, which changed how kernel recursion is bounded | Re-test on current Lean before reporting upstream |
| **Spinoza encoding** | Our 2-element models let objects be both substances and attributes, as Nakamura's axioms allow | A sorted encoding |
| **Sample, not census** | 100 of 2,561 problems; the first 20 picked by an earlier method | The full 2,561, now cheap with caching and indexing |
