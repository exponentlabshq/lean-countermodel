## 9. Conclusion

Counter-models are how one shows that something does *not* follow. With `lean-countermodel`, Lean 4 users can get them for supported untyped first-order inputs for which the finder produces a checkable finite model: Vampire finds them, Lean's kernel certifies them, and Vampire is never trusted. The interface takes arbitrary signatures; what limits coverage is the supported TPTP fragment (§8.1) and the finder, which is incomplete and cannot help with theories that have only infinite models.

The tool is small. The work was in making certificates finish. One lesson recurred on the ground-fact workloads we measured: **Lean's cost lay in elaborating statements, not in evaluating them.** Each pattern that reduced elaboration paid off, among them balanced trees, hierarchical aggregation, compact encodings and reflection through a once-verified evaluator. The patterns that added elaboration or unification work backfired, and we report those too.

The verified checker turns a certificate into a single statement: the ordinary first-order structure the model describes satisfies every formula of the problem. It depends only on Lean's standard axioms, and every shipped certificate replays through `leanchecker --fresh`; so do all 185 strict certificates of the three benchmark samples. Separately, 189 of the 192 certified results (strict and native-assisted) were checked against their original source files; for the other three, that check did not finish and they are listed by name (§6.2.2). With it, a million-fact problem is certified in a median of 5.2 minutes on a laptop, about 2.7× faster than one theorem per formula under matched conditions, measured at an earlier commit (§6.3.1). The tool also reproduces, automatically and with smaller models, the hand-built counter-models of a published Lean formalization.

The remaining gap is the user's side: a command inside Lean that takes a goal and returns a certified counter-model. The checker and the scaling recipe are the foundation for it.

---

## Appendix A: Reproducing Every Number

| Result | Command | Data |
|---|---|---|
| Unit and integration tests | `pytest test_cm.py` (Vampire on `PATH` or in `$VAMPIRE`) | 106 tests; 18 run without Vampire |
| Axioms and fresh kernel replay of all shipped certificates | `./recheck.sh` | writes `bench/recheck.log` |
| Examples (shallow) | `lake build`; `lake env lean Axioms.lean` | `examples/`, `Cm/` |
| One reflected certificate | `python3 cm.py --reflect examples/group_comm.p > G.lean && lake env lean G.lean` | — |
| Nakamura, against their library | `cd nakamura && lake build && lake env lean Axioms.lean` | spinoza-ethica-lean @ 6d4c046 |
| Benchmark inputs, from the official TPTP v9.3.1 release (§6.2) | `python3 bench/inputs.py TPTP-v9.3.1 [TPTP-v9.3.1.tgz]` | `bench/inputs.json` (SHA-256 of the tarball, every original, expansion and axiom file) |
| TPTP development sample (original sampling) | `python3 bench.py N [WORKERS]` | `bench/eligible.tsv`, `bench/results*.jsonl` |
| Frozen runs (§6.2): development and second sample at `acb343b`, third sample at `30ad4f3` | `python3 bench/frozen.py <repo>/bench [dev second third]`, from a worktree of that commit (usage in the file) | `bench/heldout-sample.json`, `bench/third-sample.json`, `bench/results-final-{dev,second,third}.jsonl`, `bench/superseded-*.jsonl` |
| Fresh kernel replay of every strict benchmark certificate (§6.2) | `python3 bench/replay.py <repo>/bench`, in the same worktree, after `frozen.py` | `bench/replay-{dev,second,third}.jsonl`, `bench/replay.log` |
| Input audit on the earlier scraped inputs (§8), superseded by the final runs' classifications | see `method` in the file | `bench/input-audit.json` |
| Controlled timings (§6.3.1) | `python3 bench/perf.py bench/problems/NLP263+1.p 3 4`; `python3 bench/perf.py bench/slice10000.p 3 4` (the first 10,000 statements of NLP263+1) | `bench/perf.jsonl` |
| NLP263 | `python3 cm.py --reflect bench/problems/NLP263+1.p DIR`, then build the modules | `bench/nlp263-*.json` |

Requirements: Lean 4.35 via elan (`nakamura/` uses 4.13), Vampire 5.1.0, and Python 3.12 with pytest. Vampire 5.1.0 is a single binary from its GitHub release, for example `gh release download v5.1.0 -R vprover/vampire -p vampire-macOS-ARM64.zip` (other platforms have their own assets); put it on `PATH` or set `VAMPIRE`. The Lean project has no dependencies beyond Lean's core library, so `lake build` needs no network access after the toolchain is installed.
