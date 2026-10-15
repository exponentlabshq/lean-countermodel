## 3. Method: Find, Rewrite, Compile, Certify

`cm.py` turns a TPTP problem (`fof` or `cnf`) into a Lean 4 proof that a finite structure satisfies `axioms ∧ ¬conjecture`. An untrusted search finds the structure; a Python translation states the claim; Lean's kernel checks it.

### 3.1 Pipeline

```mermaid
flowchart LR
    P["TPTP problem<br/>(fof / cnf)"] --> V["Vampire<br/>-sa fmb -updr off -t 30<br/>vampire(path)"]
    V -->|"FiniteModel text"| M["Model parse<br/>model(path)<br/>(n, consts, tables)"]
    P --> R["Rewrite<br/>problem · literals · clause · miniscope"]
    M --> S["Shallow emit<br/>emit()"]
    M --> F["Reflected emit<br/>emit_reflect()"]
    R --> S
    R --> F
    S -->|"inductive T, bitmasks,<br/>theorem cᵢ := by decide"| K["Lean kernel"]
    F -->|"Model M, packed tokens,<br/>Holds M problem"| K
    C["Checker.lean<br/>check_iff, holds_of_check"] --> K
```

```
 TPTP problem ──► vampire(path) ──► model(path) ──► (n, consts, tables) ─┐
      │            -sa fmb -updr off                                     │
      │            -t 30, $CM_CACHE                                      │
      │                                                                  ▼
      └──────► problem(path) ──► [(role, formula)] ──┬──► emit()         ── shallow:  T, masks, cᵢ := by decide ──┐
               literals / clause / miniscope         └──► emit_reflect() ── reflected: M, Dᵦ/Fᵦ, Holds M problem ──┤
                                                                                       ▲                         ▼
                                                                       Checker.lean ───┘                   Lean kernel
```

### 3.2 Find: `vampire(path)`

`vampire` runs `$VAMPIRE` (default `vampire`) with `-sa fmb -updr off -t 30`: the finite-model-building saturation algorithm, a 30 s limit, and unused-predicate-definition removal disabled. Without `-updr off`, Vampire may settle a problem by deleting unused predicates and print no model.

If `$CM_CACHE` is set, the output is stored under `sha256(problem bytes ‖ flags ‖ vampire --version)`. A cache hit skips Vampire entirely, so a Lean upgrade reruns only Lean. Output containing `Time limit` is never written to the cache: a timeout reflects machine load, not the problem.

### 3.3 Model parse: `model(path)`

`model` returns `(n, consts, tables)`:

| Field | Source in Vampire output | Python type |
|---|---|---|
| `n` | count of `declare_$i<k>` lines | `int` |
| `consts` | `tff(<c>_definition, axiom, c = 'fmb_$i_k')` → element `k`; `tff(<p>_definition, axiom, (~)p)` → `bool` | `{name: int \| bool}` |
| `tables` | each `(~)f('fmb_$i_…', …) (= 'fmb_$i_k')`; `= k` makes a function entry, a bare (negated) atom a predicate entry | `{symbol: {args tuple: int \| bool}}` |

Elements are numbered `1 … n` as Vampire prints them. If the output has no `FiniteModel`, `model` exits with `no finite counter-model found`; for a theorem this is the correct outcome (`test_a_theorem_has_no_counter_model`).

Lexing is shared by every stage: `TOKENS` treats a quoted name `'…'` (including escaped quotes and `%`) as one token, and `uncomment` strips `%` comments only outside quoted names.

### 3.4 Rewrite: `problem`, `literals`, `clause`, `miniscope`

`decide` and the reflected evaluator both evaluate bounded `∀` and `∨` lazily. A clause with *v* variables over *n* elements has *nᵛ* cases unless a false literal prunes its subtree. The rewrite moves each quantifier as close as possible to the first literal that uses its variable.

`problem(path)` returns `[(role, formula)]`. For each annotated formula it calls `literals(f, cnf)`, which calls `clause(tokens, scope)` to flatten the formula into `(scope, disjuncts)`. The result is rewritten by `miniscope(scope, lits)` when the formula is `cnf`, or when it is `fof`, has a non-empty scope, and flattens into more than one literal. Every other formula is kept verbatim.

**`clause` rules** (applied recursively, on tokens; `unwrap` drops enclosing parentheses, `split` splits at a top-level operator):

| Input shape | Output | Condition | Equivalence used |
|---|---|---|---|
| `! [X̄] : B` | `clause(B, scope ∪ X̄)` | `B` contains no top-level binary operator, and `X̄ ∩ scope = ∅` | ∀X̄ B is ∀X̄ B; the variables become part of the clause's universal prefix |
| `A₁ & … & Aₖ => B` | `[¬A₁, …, ¬Aₖ] ++ clause(B)` | top-level `=>` | A → (B → C) ↔ (A ∧ B) → C ↔ ¬A ∨ ¬B ∨ C |
| `D₁ \| … \| Dₖ` | `clause(D₁) ++ … ++ clause(Dₖ)` | top-level `\|` | associativity of ∨ |
| anything else | one literal | — | — |

Two side conditions carry the soundness of the flattening.

1. **TPTP binding.** In TPTP, `! [X] : A => B` parses as `(∀X A) → B`: the quantifier binds only the unit that follows it. `clause` pulls `∀` out only when its body `B` is a single unit (`whole`: no top-level `&`, `|`, `=>`, `<=>`). An earlier version read `! [X] : A => B` as ∀X (A → B); on three TPTP problems the altered formula still held, and Lean certified a different statement (README §5). The regression is covered by `examples/quantifier_scope.p`.
2. **Fresh variables only.** A quantifier is pulled into the clause's prefix only if none of its variables is already in `scope`. Pulling a re-bound `X` out would capture occurrences of an outer `X`. When the condition fails, the subformula stays one literal with its own quantifier.

Pulling `∀X̄` out of a disjunct is sound because, under the freshness condition, `X̄` does not occur in the other disjuncts: A ∨ ∀X B ↔ ∀X (A ∨ B) for X ∉ FV(A).

For `cnf`, `literals` starts with `scope = VARS(f)`: the clause's free variables are implicitly universal. `VARS` collects `[A-Z]\w*` identifiers after deleting quoted names, so `'X'` is never a variable.

**`miniscope(scope, lits, bound)`** rebuilds the clause as nested quantified disjunctions:

```
miniscope(scope, lits, bound):
    lit  := argmin over lits of |(VARS(l) ∩ scope) \ bound|      -- greedy: fewest new variables first
    body := lit                         if lits = [lit]
            (lit | miniscope(scope, lits \ lit, bound ∪ new(lit)))   otherwise
    return ![new(lit)]: body  if new(lit) ≠ ∅  else body
```

Each variable is bound immediately before the first literal that uses it, via ∀X (A ∨ B) ↔ A ∨ ∀X B when X ∉ FV(A). The greedy order chooses the literal that introduces the fewest new variables, so selective guards come first and lazy evaluation prunes early. Each literal is parenthesized by `literals`, because `![Z]: A <=> B` would otherwise bind only `A`.

### 3.5 Compile (shallow): `emit`

`emit(path, n, consts, tables)` produces a self-contained Lean file:

| Model part | Lean form |
|---|---|
| Universe | `inductive T \| e1 \| … \| en deriving DecidableEq`, `T.all`, `T.mem`, `T.idx`, and `Decidable (∀ x, p x)` / `Decidable (∃ x, p x)` instances via `decidable_of_iff` over `T.all` |
| Constant `c` | `abbrev «c» : T := T.ek` |
| Propositional symbol `p` | `abbrev «p» : Prop := True \| False` |
| Predicate `p` of arity *k* | `abbrev «p» (x0 … x(k-1) : T) : Prop := (MASK >>> (1 * x0.idx + n * x1.idx + …)) % 2 = 1` |
| Function `f` | `def «f» : T → … → T` by a pattern-matching table |
| Formula *i* (from `lean(f)`) | `theorem c<i> : <φᵢ> := by decide`; a conjecture is emitted as `¬φ` |
| Whole claim | `theorem countermodel : <tree of ∧> := <tree of ⟨_, _⟩>` |

`tree(xs, pair)` builds balanced conjunctions and anonymous-constructor proofs: depth log₂ *m* instead of *m*, since a chain of 10,000 `∧` overflows the kernel. One theorem per formula gives each `decide` fresh caches.

Every generated file starts with `set_option autoImplicit false`: an unbound name is an elaboration error, never a silently added implicit argument. `sym(k)` writes a TPTP symbol as `«k»` if it matches `[a-z]\w*`, and as `«'k'»` otherwise. Quoted names keep their quotes, so a constant `'X'` becomes `«'X'»` and cannot be captured by a bound variable `X`, and `'T'` cannot collide with the type `T` (`examples/quoted_capture.p`, `examples/quoted_names.p`).

**Modular output.** If the problem has more than `CM_CHUNK` formulas (default 2000), `emit` returns a dict of modules instead of one string:

| Module | Contents |
|---|---|
| `Base` | options, `T`, instances, predicate and function tables |
| `Names<k>` | constant `abbrev`s, `CM_CHUNK × 5` (10,000 by default) per module |
| `Chunk<j>` | `def P<i> : Prop := φᵢ`, `theorem c<i> : P<i> := by unfold P<i>; decide`, `def C<j>` (balanced ∧ of its `P<i>`), `theorem chunk<j> : C<j>` |
| `Main` | `theorem countermodel : <tree of C<j>>` |

Constants live in separate `Names` modules because Lean 4.13 fails with "deep recursion" on files with more than about 20,000 declarations (comment in `emit`). No module restates the whole problem, and `lake` checks chunks in parallel.

### 3.6 Compile (reflected): `emit_reflect`

`emit_reflect(path, n, consts, tables)` does not state formulas as Lean propositions. It writes the model as a `CM.Model` with packed tables, writes the problem as packed natural numbers, and proves each block with one `decide +kernel` call through the verified evaluator in `Checker.lean` (§4).

- `tokens(f, ids)` translates a formula into the prefix token stream read by `CM.decode`. Variables become de Bruijn indices (`env.index(k)`, last-bound variable at index 0). Symbols become numbers via `ids = {"pred", "fn", "const"}`, assigned in sorted name order; propositional symbols are numbered after the table predicates, as 0-ary predicates. A conjecture is prefixed with opcode `4` (¬).
- `as_fact(toks)` recognizes ground literals `(¬)p(c₁, …, cₖ)` over constants and returns `(polarity, predicate, [constant ids])`. Facts go into fixed-width fact tables (`F<j>`, 128 per block, proved by `holds_facts`); all other formulas go into token blocks (`D<b>`, about 4096 tokens per block, proved by `holds_of_check`).
- Lookups in the generated `M`: predicates are one packed mask per symbol, read by `get (get MASKS p mw) (index n args) 1 == 1`; constants are packed 4096 per block, the block chosen by `bsearch`, a balanced tree of `if c / 4096 < k` comparisons; functions are selected by `bsearch` over function ids, then read with `get … (index n args) w`.
- The statement is `theorem countermodel : Holds M problem`, where `problem : List Fm` is a balanced `++` tree of the decoded blocks, proved by a balanced tree of `holds_append`. Above 32 blocks (`per_part`) the output is split into `Base`, `Part<k>` and `Main` modules.

`bench.py`'s `run_hybrid` chooses reflection when the share of ground-literal formulas (`fact_share`) is at least 0.9, and the shallow path otherwise.

### 3.7 Certify

The kernel checks every `decide` (shallow) or `decide +kernel` (reflected) proof. `native_decide` is never emitted by `cm.py`; `bench.py` tries it only as a fallback after a shallow `decide` timeout and reports such problems separately as `certified (native)`.

### 3.8 Trust boundary

| Stage | Code | Trusted? | Why / how it is checked |
|---|---|---|---|
| Find | Vampire | **No** | A wrong model makes `decide` fail. Mutation tests confirm that Lean rejects broken models. |
| Cache | `vampire()`, `$CM_CACHE` | **No** | It returns Vampire's output for an identical problem, flag set and version; the output is untrusted anyway. |
| Model parse | `model()` | **No** | A misparsed model is still a model; if the formulas fail in it, Lean rejects. |
| Rewrite | `problem`, `clause`, `literals`, `miniscope` | **Yes** | A non-equivalent rewrite changes what is certified. Tested by `test_rewriting_preserves_meaning` and regression examples. |
| Translation (shallow) | `lean()`, `sym()`, `emit()` | **Yes** | The Lean statement must mean the TPTP formula. Tested by the independent evaluator and by mutant agreement; the statement is readable in the `.lean` file. |
| Translation (reflected) | `tokens()`, `as_fact()`, symbol numbering | **Yes** | The `Fm` data must mean the TPTP formula. Tested by `test_reflected_mutants_agree_with_python`; `#eval problem` prints the certified formulas. |
| Evaluator | `Checker.lean` (`Fm.check`, `decode`, `fact`) | **No** (proved) | `check_iff`, `holds_of_check` and `holds_facts` are kernel-checked theorems. |
| Certify | Lean kernel | **Yes** | Axioms: `propext` (shallow); `propext`, `Quot.sound` (reflected, per `bench/nlp263-reflected-lean4.35.json`). |

### 3.9 Worked example: `transitive_cnf`

Input (`examples/transitive_cnf.p`):

```
cnf(transitive, axiom, ~ r(X,Y) | ~ r(Y,Z) | r(X,Z)).
cnf(a_before_b, axiom, r(a,b)).
cnf(not_symmetric, negated_conjecture, ~ r(b,a)).
```

`problem` rewrites the first clause. `scope = {X, Y, Z}`; all three literals introduce two new variables, so `min` takes the first, `~r(X,Y)`, binding `X, Y`; then `~r(Y,Z)` introduces only `Z`:

```
![X,Y]: ((~ r ( X , Y )) | ![Z]: ((~ r ( Y , Z )) | (r ( X , Z ))))
```

Vampire returns a 2-element model: `a = 1`, `b = 2`, and `r` true only at `(1, 2)`. `emit` encodes `r` as mask `4 = 2^(0 + 2·1)`, bit index `x0.idx + 2·x1.idx`. Generated `Cm/transitive_cnf.lean` (excerpt):

```lean
inductive T | e1 | e2
  deriving DecidableEq
...
abbrev «a» : T := T.e1
abbrev «b» : T := T.e2
abbrev «r» (x0 x1 : T) : Prop := (4 >>> (1 * x0.idx + 2 * x1.idx)) % 2 = 1

theorem c0 : (∀ X Y : T, (¬(«r» X Y) ∨ (∀ Z : T, (¬(«r» Y Z) ∨ («r» X Z))))) := by decide
theorem c1 : («r» «a» «b») := by decide
theorem c2 : ¬(«r» «b» «a») := by decide

theorem countermodel : (((∀ X Y : T, (¬(«r» X Y) ∨ (∀ Z : T, (¬(«r» Y Z) ∨ («r» X Z)))))) ∧
    (((«r» «a» «b»)) ∧ (¬(«r» «b» «a»)))) :=
  ⟨c0, ⟨c1, c2⟩⟩
```

In the reflected path, with `ids = {pred: {r: 0}, const: {a: 0, b: 1}}`, `tokens` produces:

| Formula | Tokens | Route |
|---|---|---|
| transitive | `9 9 6 4 0 0 2 0 1 0 0 9 6 4 0 0 2 0 1 0 0 0 0 2 0 2 0 0` | token block `D0` |
| `r(a,b)` | `0 0 2 1 0 1 1` → `as_fact` = `(1, 0, [0, 1])` | fact table `F0` |
| `~r(b,a)` | `4 0 0 2 1 1 1 0` → `as_fact` = `(0, 0, [1, 0])` | fact table `F0` |

Reading the first stream: `9 9` is ∀∀, `6` is ∨, `4 0 0 2 (0 1) (0 0)` is ¬r(var 1, var 0), i.e. ¬r(X, Y), because `Y`, bound last, is index 0.

`group_comm.p` illustrates the other branch of `problem`: each `fof` formula there is a single equation under one `!`, so `clause` yields one literal, the `ok` test fails, and the formula is emitted unchanged, e.g. `theorem c3 : ¬(∀ X Y : T, ((«mul» X Y) = («mul» Y X))) := by decide` over the 6-element model S₃.

### 3.10 Independent checks (`test_cm.py`)

The trusted Python stages are tested against an evaluator that shares only the lexer (`TOKENS`) with `cm.py`. Tests that need Vampire and `lake` are skipped when either is missing.

| Test | What it checks |
|---|---|
| `holds(s, n, consts, tables, env)` | Not a test: a brute-force evaluator of the **original** TPTP text. It parses with its own recursive descent and evaluates `!`/`?` with `itertools.product` over `1 … n`. It never sees `lean()`, `tokens()` or `Checker.lean`. |
| `countermodel(path, …)` | Python's verdict: every formula of `problem(path)` holds, except the conjecture, which fails. |
| `test_compiles_to_committed_file` | `cm.py` output equals the committed `Cm/<name>.lean`, for each of the 15 `examples/*.p`. |
| `test_kernel_accepts_with_propext_only` | `lake build` succeeds and every line of `#print axioms` (via `Axioms.lean`) ends with `[propext]`. |
| `test_python_agrees_it_is_a_countermodel` | `holds` confirms Vampire's model for every example. |
| `test_circle_of_fifths_is_the_known_answer` | The model has exactly 12 elements, and `f` and `g` are x ↦ x+7 and x ↦ x+5 (mod 12). |
| `test_mutants_lean_and_python_agree` | Two random one-entry corruptions per example (seed 0): Lean (shallow) accepts **exactly** the mutants that `holds` accepts, and at least one mutant is rejected. |
| `test_reflected_mutants_agree_with_python` | Same, seed 1, through `emit_reflect` and `Checker.lean`. This tests the reflected translation, the trusted part of that path. |
| `test_reflected_certificate` | Each example's model certifies through `emit_reflect`. |
| `test_rewriting_preserves_meaning` | Each rewritten formula agrees with its raw original (a `cnf` closed with `![VARS]`) under `holds`, on the model and on every one-entry mutation of every table. |
| `test_a_theorem_has_no_counter_model` | `cm.py` exits non-zero on `∀X p(X) ⊢ p(k)`. |
| `test_large_problems_split_into_modules`, `test_constants_split_into_name_modules` | With `CM_CHUNK=2` or `1`, modular output builds with `lake`; `#print axioms` on the result contains no `sorryAx`. |
| `test_vampire_cache_is_transparent` | With `CM_CACHE`, the second run hits the cache (one entry) and emits identical Lean. |

The file defines 4 tests parametrized over the 15 examples plus 8 single tests: 68 test cases.

**Planted bugs.** The suite was validated by introducing known bugs into `cm.py` and confirming failures (README §5): `=>` compiled as `↔` (7 tests fail), a scoping bug (4), a dropped negation (18), a lost parenthesis (4), and the single-formula case (1). The planted variants are not in the repository; the counts are those recorded in the README, measured against the suite at that time.
