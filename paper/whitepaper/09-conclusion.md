## 9. Conclusion

Counter-models are how one shows that something does *not* follow. With `lean-countermodel`, Lean 4 users can get them for any first-order theory: Vampire finds them, Lean's kernel certifies them, and Vampire is never trusted.

The tool is small. The work was in making certificates finish. One lesson recurred on the ground-fact workloads we measured: **Lean's cost lay in elaborating statements, not in evaluating them.** Each pattern that reduced elaboration paid off, among them balanced trees, hierarchical aggregation, compact encodings and reflection through a once-verified evaluator. The patterns that added elaboration or unification work backfired, and we report those too.

The verified checker turns a certificate into a single statement: the ordinary first-order structure the model describes satisfies every formula of the problem. It depends only on Lean's standard axioms, and every shipped certificate replays through `leanchecker --fresh`. With it, a million-fact problem is certified in a median of 5.2 minutes on a laptop, about 2.7× faster than one theorem per formula under matched conditions. The tool also reproduces, automatically and with smaller models, the hand-built counter-models of a published Lean formalization.

The remaining gap is the user's side: a command inside Lean that takes a goal and returns a certified counter-model. The checker and the scaling recipe are the foundation for it.

---

## Appendix A: Reproducing Every Number

| Result | Command | Data |
|---|---|---|
| Unit and integration tests | `pytest test_cm.py` | 102 tests |
| Axioms and fresh kernel replay of all shipped certificates | `./recheck.sh` | writes `bench/recheck.log` |
| Examples (shallow) | `lake build`; `lake env lean Axioms.lean` | `examples/`, `Cm/` |
| One reflected certificate | `python3 cm.py --reflect examples/group_comm.p > G.lean && lake env lean G.lean` | — |
| Nakamura, against his library | `cd nakamura && lake build && lake env lean Axioms.lean` | spinoza-ethica-lean @ 6d4c046 |
| TPTP development sample (original sampling) | `python3 bench.py N [WORKERS]` | `bench/eligible.tsv`, `bench/results*.jsonl` |
| Frozen development and held-out runs (§6.2, §6.2.1) | `python3 bench/frozen.py <repo>/bench`, from a worktree of `51481a4` (usage in the file) | `bench/heldout-sample.json`, `bench/results-final-*.jsonl`, `bench/superseded-*.jsonl` |
| Input audit (§8) | see `method` in the file | `bench/input-audit.json` |
| Controlled timings (§6.3.1) | `python3 bench/perf.py bench/problems/NLP263+1.p 3 4`; `python3 bench/perf.py bench/slice10000.p 3 4` (the first 10,000 statements of NLP263+1) | `bench/perf.jsonl` |
| NLP263 | `python3 cm.py --reflect bench/problems/NLP263+1.p DIR`, then build the modules | `bench/nlp263-*.json` |

Requirements: Lean 4.35 via elan (`nakamura/` uses 4.13), Vampire 5.1, and Python 3.12.
