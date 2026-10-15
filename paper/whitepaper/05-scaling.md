## 5. Scaling: Design Patterns, Data Structures and Measured Effects

**Central lesson, for the workloads we measured.** For our large ground-fact certificates, the cost was dominated by Lean *elaborating statements* (parsing, elaboration, typeclass search, kernel type checking of large terms) rather than by evaluating them, and reducing proposition elaboration gave the largest gains. This is not a claim about all Lean certificates: quantifier-heavy checking has a separate evaluation bottleneck, which our own reflected regression on PLA025+1 shows (§4.5).

**Cost model.** Unless stated otherwise, $O(\cdot)$ counts field operations (shifts, masks, comparisons) on fixed-width fields. On `Nat` data, a shift costs time proportional to the bit length of the number shifted. That is why blocking (pattern 13a) matters, and why an "$O(1)$ packed lookup" means a constant number of operations on a bounded block, not constant time on an unbounded table.

Profile of one 2,000-fact shallow chunk (Lean 4.13):

| Phase | Time | Share |
|---|---|---|
| Parsing | 3.83 s | 41% |
| Tactic execution | 1.37 s | 15% |
| Elaboration | 1.34 s | 14% |
| Kernel type checking | 1.08 s | 12% |
| Typeclass inference | 1.04 s | 11% |
| Other (definitions, linting, sharing, metavariables) | 0.59 s | 6% |
| **Total** | **9.25 s** | 100% |

Parsing alone outweighs tactic execution (where `decide` actually runs) by 2.8×. Together, parsing, elaboration and typeclass inference take 66% of the chunk's time, against 15% for running the tactics.

Machine for all measurements: 8 GB laptop, 8 cores.

### 5.1 Master table

| # | Pattern (classic name) | Where applied | Big-O before → after | Measured effect | Status |
|---|---|---|---|---|---|
| 1 | Backtracking with pruning (miniscoping; lazy ∨, bounded ∀ in `decide`) | clause evaluation | $\lvert M\rvert^k$ full enumeration → pruned search tree | NLP219-1: 13-var clause over 7 elements $\approx 10^{11}$ cases → 46,746 atom checks for the whole problem; impossible → certified | kept |
| 2 | Greedy join ordering (fewest new variables first) | literal order inside a clause | — (heuristic) | a heuristic, not a guarantee of picking the most selective literal (the density planner, R1, shows selectivity is data-dependent); on SWB017+3 it happens to start from a highly selective guard, `rest(S3, nil)` | kept |
| 3 | Loop fusion / deforestation (recursive flattening ∀V(A→∀W(B→C)) → one clause, fresh vars only) | FOF → clause translation | nested loops re-enter outer guards → one fused loop | SWB017+3 368,112 → 5,932 atom checks; `native_decide` → kernel-only `decide` in 2–12 s. PLA025+1 91,921 → 31,675 | kept |
| 4 | Bitset (bitmask predicate tables) | model predicate lookup | $O(n)$ list-membership scan → $O(1)$ bit test | NLP165-1 10.9 s → ~1 s | kept |
| 5 | Divide and conquer (one theorem per formula) | certificate layout | one monolithic term → n small independent terms | PLA025+1 47 s → 14 s; peak memory 805 MB → 420 MB | kept |
| 6 | Memoization (VARS cache of literal variables) | Python rewriter | recompute per visit → once per literal | SYN832-1 rewrite 21.8 s → 8.4 s, identical output | kept |
| 7 | Balanced binary tree | conjunction terms | depth $O(n)$ → $O(\log_2 n)$ | linear 10,000-way ∧ overflows kernel ("deep recursion"); tree passes | kept |
| 8 | Partitioning / sharding (≤10,000 declarations per module) | Lean modules | — (hard limit) | an observed, reproducible failure point on Lean 4.13 for our generated pattern: files with more than ~20,600 declarations fail ("deep recursion"); not re-tested on 4.35; Names split for 383,180 constants | kept |
| 9 | Segment tree / map-reduce (hierarchical aggregation) | final theorem | restate n formulas in Main → $O(n/\text{chunk})$ chunk conjunctions | 10,000-formula slice 109 s → 12.3 s wall; Main 77 s → 0.09 s | kept |
| 10 | Content-addressed cache (SHA-256 of problem+flags+version) | Vampire calls | re-run per invocation → $O(1)$ hit | on a Lean-only rerun, every problem with a deterministic Vampire answer (77 models and 3 definite give-ups) is served from the cache; the 2026-10-15 rerun's median end-to-end time fell from 3 s to 0.65 s per problem; timeouts never cached | kept |
| 11 | Index lookup instead of rejection sampling | benchmark selection | ~113 requests/problem → 1–2 | picking ~165 s → negligible; end-to-end ~174 s → ~8 s per problem (~22×) | kept |
| 12 | Producer–consumer pipeline, memory-sized worker pool, fail-fast, LPT scheduling | build orchestration | — (makespan) | ~600 MB per chunk → 3–4 workers on 8 GB; `native_decide` only after timeout; LPT ordering was not measured in isolation | kept |
| 13 | Reflection (verified evaluator `Checker.lean`) with compact encoding | ground-fact certificates | elaborate n propositions → elaborate one data literal + one evaluator | *Historical, truth-only certificate* (before the validity and well-formedness checks; single runs, Lean 4.35, §5.3): 10,000-fact slice 36.1 s → 5.1 s CPU. *Current, controlled* (§6.3.1, same Lean, validated certificate, median of 3): 31.1 s → 9.8 s CPU (3.2×) | kept (hybrid) |
| 13a | Square-root decomposition / blocking (packed Nat per block) | reflected data encoding | lookup in one 557,591-bit number $O(N)$ per shift ($O(N^2)$ total) → $O(\text{block})$ | unblocked packing quadratic; array literal of 11,312 numbers timed out in elaboration | kept |
| 13b | Fuel = nesting depth instead of token count | reflected evaluator | kernel cost grows with fuel → bounded by depth | >9 min → 12 s | kept |
| 13c | Direct addressing / binary search instead of `match` chains | reflected predicate and constant lookup | $O(n)$ literal comparison chain → $O(1)$ packed lookup, $O(\log n)$ blocks | 10.4 → 8.5 s CPU | kept |
| 13d | Fixed-width records (fact tables) | reflected facts | — | 8.5 → 5.66 s CPU | kept |
| 13e | Block-size tuning | reflected facts | — | 128: 5.11 s, 512: 5.66 s, 2048: 7.68 s CPU | kept (128) |
| 13f | `decide +kernel` instead of `decide` | reflected proof | skip elaborator-side evaluation | prototype 7.0 s → 3.1 s | kept |
| R1 | Cost-based query planner (order by model table density) | literal order | — | PLA025 −24% atom checks; NLP219 +14% | rejected |
| R2 | Hash-consing (memoized fact lemmas per equivalence class) | shallow facts | 9,957 facts → 27 lemmas | build 38.8 s vs 12.3 s (3× slower) | rejected |
| R3 | Opaque `def` vs `abbrev` for named propositions | shallow statements | — | no effect | rejected |
| R4 | `rfl` instead of `decide` for positive facts | shallow facts | — | 6.75 → 5.12 s (1.3×) | measured, not adopted: superseded by reflection |
| R5 | Short-name interning | constant names | — | not measured | untested |
| R6 | Reflection for quantifier-heavy problems | PLA025+1 (10-element model) | — | >400 s (did not finish) vs 4.4 s shallow; primitive recursor 228 s | rejected → hybrid dispatch |

### 5.2 Patterns grouped by the cost they attack

**Search size (patterns 1–3, R1).** Search size grows as $\lvert M\rvert^k$ in the number of variables k. Backtracking with miniscoping, lazy ∨ and bounded ∀ cuts NLP219-1 from a $\approx 10^{11}$-case clause to 46,746 atom checks for the whole problem. Greedy join order starts each search at the literal that introduces the fewest new variables. That is a heuristic: it often coincides with a selective guard, but selectivity depends on the model's data (R1). Recursive flattening fuses nested guarded quantifiers into one clause that introduces only fresh variables. Without it, the inner loop re-evaluates outer guards. This alone moved SWB017+3 from `native_decide` to kernel-only `decide`. Once search was this small, it stopped dominating the cost.

**Elaboration (patterns 5, 9, 13, R2).** These attack the cost that dominates in the profile. Splitting into one theorem per formula keeps each elaboration problem small: PLA025+1 47 s → 14 s, with peak memory halved. Hierarchical aggregation removes the second elaboration of every formula in Main. Restating 10,000 formulas in one final theorem took 77 s, of which the statement alone took 59 s and an explicit `And.intro` term 237 s. Reflection removes per-formula elaboration entirely. The certificate becomes data (packed Nat literals) plus one verified evaluator `Checker.lean`, run with `decide +kernel`. Hash-consing failed for the opposite reason: it *added* unification of each fact against a shared lemma (R2).

**Kernel limits (patterns 7, 8, 13a–13c).** These are hard limits rather than costs: Lean either works or fails.

- A right-nested ∧ of 10,000 conjuncts fails with "deep recursion". A balanced tree has depth ⌈$\log_2 n$⌉.
- **On Lean 4.13, with our generated pattern and default options**, files with more than about 20,600 declarations failed with kernel "deep recursion". Even 30,000 trivial `def c_i : Nat := 1` fail, in a band of ~340 failures around declaration 20,600. The fix caps modules at 10,000 declarations.
- In the reflected path, kernel evaluation is sensitive to representation.
  - A 557,591-bit number shifted on every lookup made decoding quadratic. Blocking fixed it.
  - Structural recursion on fuel = token count made evaluation take more than 9 min. Fuel = nesting depth: 12 s.
  - `match` on literals compiles to an $O(n)$ comparison chain. Packed $O(1)$ lookup and binary search over constant blocks replaced it.

**Memory and I/O (patterns 4, 5, 6, 13d–13e).** Bitmask tables replace list scans (NLP165-1 10.9 s → ~1 s). Each chunk needs ~600 MB, which caps parallelism on 8 GB. Divide and conquer halved peak memory on PLA025+1. Reflection shrank NLP263+1 from 178 MB of source to 25 MB and from 2.0 GB of build output to 65 MB (Table 5.3). Fixed-width fact records with 128 facts per block gave the lowest reflected CPU time.

**Pipeline throughput (patterns 10–12).** These patterns reduce the time spent outside Lean.

- **Vampire cache.** Keyed by SHA-256(problem, flags, version). Timeouts are never cached, because two problems flipped from model to timeout under CPU load. **Note:** the lower median time of reruns (0.65 s against 3 s per problem) reflects cache reuse, not a Lean improvement.
- **Benchmark selection.** It reads the TPTP ProblemAndSolutionStatistics index: 2,561 eligible problems of 26,990 (CNF SAT 1,305; FOF CSA 888; FOF SAT 368). Rejection sampling took ~113 requests per problem; the index needs 1–2.
- **Build pipeline.** A producer–consumer pipeline, with the worker pool sized by memory (3–4 workers). Jobs run longest first (LPT) to shorten the makespan. `native_decide` runs only after a `decide` timeout, so kernel-only proofs remain the default.

### 5.3 NLP263+1: shallow vs reflected

NLP263+1: 1,026,857 ground facts, 383,180 constants, 1-element model. Sources: `bench/nlp263-lean4.13.json`, `bench/nlp263-reflected-lean4.35.json`.

**Historical, uncontrolled measurements.** This subsection records the development-time runs: single runs, different Lean versions, different worker counts, varying load, and a reflected certificate *without* the validity and well-formedness checks added after peer review. They explain how the design was reached; they are **not** the paper's performance claim. The controlled comparison is §6.3.1 (median 14.1 min shallow against 5.2 min reflected, 2.7×).

| Metric | Shallow (Lean 4.13) | Reflected (Lean 4.35) | Ratio |
|---|---|---|---|
| Wall time | 20.7 min (1,241 s) | 4.8 min (290 s) | 4.3× |
| CPU time | 54 min (3,262 s) | 17.5 min (1,052 s) | 3.1× |
| Peak memory | 1.64 GB | 0.50 GB | 3.3× |
| Lean source | 178 MB | 25 MB | 7.1× |
| Build output | 2.0 GB | 65 MB | ~31× |
| Modules | 555 (Base 1, Names 39, Chunk 514, Main 1) | 253 (Base 1, Part 251, Main 1) | 2.2× |
| Granularity | 2,000 facts/chunk, 3 parallel | 128 facts/block, 32 blocks/part, 4 parallel | — |
| Axioms | none | `propext`, `Quot.sound` | — |
| Failed modules | 0 | 0 | — |

Lean versions differ between the two columns. On the 10,000-fact slice, however, the shallow method costs about the same on both versions (39.6 s CPU on 4.13, 36.1 s on 4.35). This suggested that most of the gap comes from the method, not the Lean version; §6.3.1 tests that directly on one Lean version and finds a smaller gap than this table shows. The version did matter for quantifier-heavy shallow proofs: PLA025+1 took 14–47 s on 4.13 and 4.4 s on 4.35.

10,000-fact slice, Lean 4.35:

| Variant | Wall | CPU |
|---|---|---|
| Shallow | 15.1 s | 36.1 s |
| Reflected, one file | 7.1 s | 5.1 s |
| Bare reflection prototype | 3.1 s | not recorded |

### 5.4 Illustrations

**Hierarchical aggregation (shallow path).** Each formula is elaborated exactly once, in its chunk. Main only combines $O(n/2000)$ chunk theorems.

```
                          Main            Main: ∧ of chunk theorems (0.09 s)
                       /   |    \
            Chunk_1  Chunk_2 ... Chunk_514          ≤2,000 facts each
            thm_1..thm_k  +  balanced ∧-tree         depth ⌈log₂ k⌉
                  \        |        /
              Names_1 ... Names_39                   ≤10,000 decls each
              (383,180 constants)                    (< ~20,600 limit)
                       \   |   /
                         Base                        model, predicate bitmasks
```

Reflected path: `Base` (model + `Checker.lean`) → `Part_1 … Part_251` (32 blocks each) → `Main`.

**Blocking (reflected encoding).**

```
unblocked:   facts ──► one Nat of 557,591 bits
             lookup(i) = (N >>> (i·w)) &&& mask      shift touches all N bits
             ⇒ O(N) per lookup, O(N²) per pass       (quadratic)

blocked:     facts ──► [B_0][B_1][B_2] ... [B_m]     128 facts per block
             one packed Nat literal per block, fixed-width records
             lookup(i) = decode(B_{i/128}, i mod 128)
             ⇒ O(block) per lookup; whole pass linear in N
             constants: binary search over sorted blocks, O(log m)
```

Block size is a trade-off between per-block overhead and per-lookup shift cost: 128 → 5.11 s, 512 → 5.66 s, 2048 → 7.68 s CPU.

### 5.5 Negative results

- **Cost-based query planner.** Ordering literals by model table density cut atom checks by 24% on PLA025 but raised them by 14% on NLP219. A planner that wins on one problem and loses on another adds complexity without a reliable gain. The greedy fewest-new-variables order was kept.
- **Hash-consed fact lemmas.** Grouping 9,957 facts into 27 shared lemmas by equivalence class made the build 3× slower (38.8 s vs 12.3 s). Unifying each fact with a shared lemma costs more than deciding the fact directly. This is the clearest confirmation of the central lesson: fewer terms do not help when each one needs more elaboration.
- **Opaque `def` vs `abbrev`** for named propositions had no measurable effect.
- **`rfl` instead of `decide`** for positive facts gave 1.3× (6.75 → 5.12 s). This is a small gain next to the order-of-magnitude effects above.
- **Short-name interning** was not measured.
- **Reflection on quantifier-heavy problems.** PLA025+1 (10-element model) did not finish in 400 s reflected, against 4.4 s shallow on Lean 4.35. The primitive recursor brought it to 228 s, still 50× slower. Hypothesis: lazy kernel evaluation re-decodes subformulas inside quantifier loops. Policy: hybrid dispatch, which reflects when ≥90% of formulas are ground facts and uses the shallow method otherwise.

### 5.6 Lessons for builders of large Lean certificates

- **Profile before optimizing, and expect elaboration to dominate.** Parsing alone was 41% of a chunk. `decide` itself was a minority of the cost.
- **Never state a formula twice.** Prove each one once, locally, and aggregate proofs hierarchically. Restating 10,000 formulas in Main cost 77 s; aggregating chunk conjunctions cost 0.09 s.
- **Keep every term shallow and every file small.** Use balanced trees for big conjunctions ($\log_2 n$ depth) and keep modules at ≤10,000 declarations. Lean 4.13 had an undocumented failure band near 20,600.
- **Reduce the search before you reduce the proof.** Miniscoping, lazy connectives, greedy join order and flattening turn $10^{11}$ cases into tens of thousands.
- **For ground data, use reflection, and design the encoding for the kernel.** Use packed blocks (~128 records), $O(1)$ lookups instead of `match` chains, fuel bounded by depth, and `decide +kernel`. For quantifier-heavy problems, stay shallow and dispatch per problem.
- **Distrust sharing that adds unification.** Hash-consed lemmas made the build 3× slower. Fewer terms help only if each one costs the same to elaborate.
- **Engineer the pipeline as carefully as the proof.**
  - Content-addressed caching. Never cache timeouts, because they depend on load.
  - Pick problems from an index instead of sampling.
  - Size worker pools by memory, not cores.
  - Schedule longest jobs first.
  - Fall back to `native_decide` only on a timeout.
