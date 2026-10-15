## 9. Conclusion

Counter-models are how one shows that something does *not* follow. With `lean-countermodel`, Lean 4 users can get them for any first-order theory: Vampire finds them, Lean's kernel certifies them, and Vampire is never trusted.

The tool is small. The work was in making certificates finish. One lesson recurred throughout: **Lean's cost lies in elaborating statements, not in evaluating them.** Each pattern that reduced elaboration paid off, among them balanced trees, hierarchical aggregation, compact encodings and reflection through a once-verified evaluator. The patterns that added elaboration or unification work backfired, and we report those too.

The verified checker turns a certificate into a single statement, `Holds M problem`, which anyone can read with `#eval` and which depends only on Lean's standard axioms. With it, a million-fact problem is certified in under five minutes on a laptop. The tool also reproduces, automatically and with smaller models, the hand-built counter-models of a published Lean formalization.

The remaining gap is the user's side: a command inside Lean that takes a goal and returns a certified counter-model. The checker and the scaling recipe are the foundation for it.

---

## Appendix A: Reproducing Every Number

| Result | Command | Data |
|---|---|---|
| Unit and integration tests | `pytest test_cm.py` | 69 tests |
| Examples (shallow) | `lake build`; `lake env lean Axioms.lean` | `examples/`, `Cm/` |
| One reflected certificate | `python3 cm.py --reflect examples/group_comm.p > G.lean && lake env lean G.lean` | — |
| Nakamura, against his library | `cd nakamura && lake build && lake env lean Axioms.lean` | spinoza-ethica-lean @ 6d4c046 |
| TPTP benchmark | `python3 bench.py N [WORKERS]` | `bench/eligible.tsv`, `bench/results*.jsonl` |
| NLP263 | `python3 cm.py --reflect bench/problems/NLP263+1.p DIR`, then build the modules | `bench/nlp263-*.json` |

Requirements: Lean 4.35 via elan (`nakamura/` uses 4.13), Vampire 5.1, and Python 3.12.
