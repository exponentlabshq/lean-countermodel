## 4. The Verified Checker: Data Structures and Trust

`Checker.lean` (namespace `CM`, 430 lines) is the evaluator behind the reflected path (§3.6). It defines first-order syntax as data; a bounded semantics `Fm.Sem` and a Boolean evaluator `Fm.check`, proved equivalent by `Fm.check_iff`; decoders from packed natural numbers to formulas; ordinary first-order structures with satisfaction `Fm.Sat`; the validity and well-formedness checks `Model.valid` and `Fm.wf`; the bridge `sem_iff_sat`; and the certificate layer `Good` and `countermodel_of_good` (§4.4). A reflected certificate is one kernel evaluation of `check` per block, not one elaborated proposition per formula.

### 4.1 Data structures

Syntax is plain inductive data, with de Bruijn variables:

```lean
inductive Tm where
  | var (i : Nat)
  | const (c : Nat)
  | app (f : Nat) (args : List Tm)

inductive Fm where
  | atom (p : Nat) (args : List Tm)
  | eq (a b : Tm)
  | tru | fls
  | not (φ : Fm)
  | and (φ ψ : Fm) | or (φ ψ : Fm) | imp (φ ψ : Fm) | iff (φ ψ : Fm)
  | all (φ : Fm) | ex (φ : Fm)
  deriving Repr
```

A model is a domain size and three lookup functions. Elements are `0 … n-1`:

```lean
structure Model where
  n : Nat
  const : Nat → Nat
  fn : Nat → List Nat → Nat
  pred : Nat → List Nat → Bool
```

Terms evaluate under an environment `env : List Nat`. Index 0 is the most recently bound variable:

```lean
def Tm.val (M : Model) (env : List Nat) : Tm → Nat
  | .var i => env.getD i 0
  | .const c => M.const c
  | .app f args => M.fn f (Tm.vals M env args)
def Tm.vals (M : Model) (env : List Nat) : List Tm → List Nat
  | [] => []
  | t :: ts => t.val M env :: Tm.vals M env ts
```

The semantics is a `Prop`. Quantifiers range over `x < M.n`:

```lean
def Fm.Sem (M : Model) : List Nat → Fm → Prop
  | env, .atom p args => M.pred p (Tm.vals M env args) = true
  | env, .eq a b => a.val M env = b.val M env
  ...
  | env, .all φ => ∀ x, x < M.n → φ.Sem M (x :: env)
  | env, .ex φ => ∃ x, x < M.n ∧ φ.Sem M (x :: env)
```

The evaluator mirrors it clause by clause in `Bool`. Bounded quantifiers become counting loops that stop at the first decisive value:

```lean
def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => f k && allBelow f k
def anyBelow (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => f k || anyBelow f k

def Fm.check (M : Model) : List Nat → Fm → Bool
  | env, .atom p args => M.pred p (Tm.vals M env args)
  | env, .eq a b => a.val M env == b.val M env
  | env, .imp φ ψ => !φ.check M env || ψ.check M env
  ...
  | env, .all φ => allBelow (fun x => φ.check M (x :: env)) M.n
  | env, .ex φ => anyBelow (fun x => φ.check M (x :: env)) M.n
```

`allBelow` and `anyBelow` count down from `n` and build no list. Together with `&&`/`||`, they give `check` the pruning that §3.4's miniscoping relies on.

| Structure | Role | Encoding | Lookup / evaluation cost |
|---|---|---|---|
| `Tm` | term syntax | inductive; `var` is a de Bruijn index | `Tm.val`: $O(\lvert t\rvert )$ model lookups; `.var i` is `env.getD i 0`, $O(i)$ |
| `Fm` | formula syntax | inductive, 11 constructors | `Fm.check`: $O(\lvert \varphi\rvert  \cdot  n^{\varphi})$ worst case for quantifier nesting depth q; lazy `&&`, `\|\|`, `allBelow`, `anyBelow` prune |
| `Model` | finite structure | `n` plus `const`, `fn`, `pred` as functions | cost of the function bodies (§4.2) |
| `Fm.Sem` | meaning (specification) | `Prop`, never evaluated | — |
| `allBelow` / `anyBelow` | bounded ∀ / ∃ | structural recursion on `n` | ≤ n calls of `f`; stops at the first `false` / `true` |
| `Holds M φs` | certificate statement | `∀ φ ∈ φs, φ.Sem M []` | — |

### 4.2 Models in generated certificates

`emit_reflect` writes one `def M : Model`. Elements are shifted from Vampire's `1 … n` to `0 … n-1` (`x - 1`). Two helpers from `Checker.lean` do all lookups:

```lean
def get (packed i w : Nat) : Nat := (packed >>> (i * w)) % 2 ^ w   -- w-bit field i
def index (n : Nat) : List Nat → Nat                               -- tuple → position, base n
  | [] => 0
  | x :: xs => x + n * index n xs
```

The generated model, with `n`, `K = 4096`, the element width `w = max(n-1,1).bit_length()` and the mask width `mw` substituted:

```lean
def M : Model where
  n := n
  const c := get (if c / 4096 < k then … else …) (c % 4096) w
  fn f args := get (if f < k then … else …) (index n args) w
  pred p args := get (get MASKS p mw) (index n args) 1 == 1
```

| Symbol kind | Python (`emit_reflect`) | Lean lookup | Cost in symbols |
|---|---|---|---|
| Predicate *p* | `masks[i]`: bit `idx(a)` set iff `p(a)` is true; propositional symbols are 0-ary predicates with mask 1 or 0; all masks packed into one Nat at width `mw` | `get (get MASKS p mw) (index n args) 1` | $O(1)$: two `get`s, one `index` ($O(\text{arity})$) |
| Constant *c* | `cvals` packed `w` bits each, 4096 per block (`cblocks`) | `bsearch('c / 4096', cblocks)` selects the block; `get … (c % 4096) w` | $O(\log b)$ comparisons for b blocks, then one `get` |
| Function *f* | `fn_tables[i]`: value `v-1` at field `idx(a)`, width `w` | `bsearch('f', fn_tables)`; `get … (index n args) w` | $O(\log F)$ comparisons for F functions, then one `get` |

`bsearch(var, xs)` writes `xs[var]` as a balanced tree of `if var < mid` comparisons. A `match` on literals would be a chain of $O(n)$ comparisons. Each `get` is a shift of a packed Nat, and a shift costs time linear in the Nat's bit length. Blocking bounds that length (§5, pattern 13a).

### 4.3 Problem encodings

**(a) Token streams.** A block of non-fact formulas is one Nat, `D<b>`, of fixed-width tokens in prefix order. The token width is `tw = max(max token, 10).bit_length()`, at least 4 bits.

| Formulas | Opcode | Operands | Terms | Opcode | Operands |
|---|---|---|---|---|---|
| atom | `0` | `p k t₁…tₖ` | variable | `0` | `i` (de Bruijn) |
| `=` | `1` | `t t` | constant | `1` | `c` |
| ⊤ / ⊥ | `2` / `3` | — | application | `2` | `f k t₁…tₖ` |
| ¬ | `4` | `φ` | | | |
| ∧ ∨ → ↔ | `5` `6` `7` `8` | `φ ψ` | | | |
| ∀ / ∃ | `9` / `10` | `φ` | | | |

The decoder is mutually recursive and fueled:

| Function | Signature | Reads |
|---|---|---|
| `readTm s w` | `fuel → i → Option (Tm × Nat)` | one term at position `i`; returns the next position |
| `readTms s w` | `fuel → k → i → Option (List Tm × Nat)` | `k` terms |
| `readFm s w` | `fuel → i → Option (Fm × Nat)` | one formula |
| `readFms s w fuel` | `k → i → List Fm` | `k` formulas; on `none` it returns `[.fls]` and stops |
| `decode s w k depth` | `List Fm` | `readFms s w depth k 0` |

Fuel bounds the recursion depth, and each call consumes one unit. Kernel cost grows with the fuel, so `emit_reflect` passes `depth = max(map(nesting, fs)) + 2`, where `nesting` is the token count of a single formula. That is an upper bound on the nesting depth, not the block's token count (§5, pattern 13b: >9 min → 12 s). What the decoder does with bad data is precise, and narrower than "malformed data decodes to ⊥":

- **Detected failures:** if the fuel runs out, `readFm` returns `none`, and `readFms` emits `.fls`, which can never be certified.
- **Not detected by the decoder:** `get` reads zeros past the end of the data, and the formula count is supplied by the generator. So truncation, extra tokens and wrong counts can decode to *some* formula list. Such errors may be accepted as a different decoded formula list. The kernel proof remains about that list, not necessarily the intended source problem; detecting the mismatch is the responsibility of the trusted translation and its tests (§4.6).
- **Caught by `Fm.wf`:** out-of-scope variables, out-of-range constants and wrong function arities (§4.4).

`tests/Boundary.lean` records these cases as kernel-checked facts.

Illustration: `fof(irrefl, axiom, ![X]: ~ r(X,X)).` with `ids["pred"]["r"] = 0`. `tokens` returns `[9] + body`, and `X` is index 0:

```
formula :  ∀ X . ¬ r ( X , X )
tokens  :  9   4   0   0   2   0  0   0  0
           │   │   │   │   │   └──┘   └──┘
           ∀   ¬  atom p=0 k=2 var 0  var 0
position:  0   1   2   3   4   5  6   7  8

packed (tw = 4 bits, token i at bits 4i … 4i+3, least significant first):
  bits  35..32 31..28 27..24 23..20 19..16 15..12 11..8 7..4 3..0
  token   0      0      0      0      2      0      0     4    9
  D = 9 + 4·2⁴ + 2·2¹⁶ = 131145

decode 131145 4 1 11  =  [.all (.not (.atom 0 [.var 0, .var 0]))]
  (depth = 9 tokens + 2 = 11)
```

**(b) Fact tables.** `emit_reflect` diverts every formula that `as_fact` recognizes as a ground literal `(¬)p(c₁,…,cₖ)` over constants into fixed-width records. With K slots for the largest fact arity, each record has `K + 2` fields of `fw` bits: polarity (1 asserted, 0 denied), predicate, then K constant ids, zero-padded. A block `F<j>` holds 128 records (`facts_per_block`). The arity table `ar` is packed at width `aw = K.bit_length()`.

```lean
def fact (s w K : Nat) (ar : Nat → Nat) (i : Nat) : Fm :=
  let b := i * (K + 2)
  let p := get s (b + 1) w
  let a := (List.range (ar p)).map fun j => Tm.const (get s (b + 2 + j) w)
  if get s b w == 1 then .atom p a else .not (.atom p a)

def decodeFacts (s w K : Nat) (ar : Nat → Nat) (k : Nat) : List Fm := (List.range k).map (fact s w K ar)
```

`fact` reads record `i` directly with $O(K)$ `get`s. No general decoding and no fuel are needed.

Illustration: the facts of `transitive_cnf.p` (§3.9), with `r = 0`, `a = 0`, `b = 1`, `K = 2` and `fw = 1`:

```
record i = fields [i·4 … i·4+3]        (K + 2 = 4 fields, fw = 1 bit each)

            ┌──────────┬───────────┬────────┬────────┐
            │ polarity │ predicate │ slot 0 │ slot 1 │
            ├──────────┼───────────┼────────┼────────┤
 0: r(a,b)  │    1     │     0     │   0    │   1    │   as_fact → (1, 0, [0, 1])
 1: ~r(b,a) │    0     │     0     │   1    │   0    │   as_fact → (0, 0, [1, 0])
            └──────────┴───────────┴────────┴────────┘
 F0 = pack([1,0,0,1, 0,0,1,0], 1) = 2⁰ + 2³ + 2⁶ = 73
 ar = get 2 p 2                     (arity of r = 2, aw = 2)

theorem hf0 : Holds M (decodeFacts F0 1 2 ar 2) := holds_facts M _ _ _ _ _ (by decide +kernel)
```

### 4.4 Soundness

The certificate rests on two theorems, both proved once in `Checker.lean`.

**(1) From bounded evaluation to ordinary semantics.** `Fm.Sem` is a *bounded* semantics. Quantifiers range over `x < M.n`, but nothing in `Model` stops a constant or function value from leaving that range, and `M.n` may be 0. Peer review rightly pointed out the consequence. With `M.n = 1` and a constant interpreted as 1, the bounded semantics makes `∀x, x ≠ c` true, although it is unsatisfiable in any structure containing `c`; with `M.n = 0`, `∀x, ⊥` is vacuously true. The checker therefore defines ordinary structures and satisfaction, and two kernel-checked conditions:

```lean
structure Structure (α : Type) where
  const : Nat → α
  fn : Nat → List α → α
  pred : Nat → List α → Prop
def Fm.Sat (S : Structure α) (d : α) : List α → Fm → Prop  -- ∀/∃ range over all of α

def Model.valid (M : Model) (fns : List (Nat × Nat)) : Bool :=      -- 0 < n; each function closed
  0 < M.n && fns.all fun (f, k) => allTuples M.n (fun xs => M.fn f xs < M.n) k
def Fm.wf (M : Model) (fns : List (Nat × Nat)) : Nat → Fm → Bool   -- bound variables, constants in range,
                                                                    -- functions at checked arities
theorem sem_iff_sat (M) (fns) (hv : M.valid fns = true) (d : Fin M.n) (φ : Fm) :
    ∀ env : List (Fin M.n), φ.wf M fns env.length = true →
    (φ.Sem M (env.map Fin.val) ↔ φ.Sat (M.toStructure (Model.valid_pos hv)) d env)
```

`M.toStructure` is the structure on `Fin M.n` that `M` describes. Its values are clipped into the domain, and the proof shows the clipping never changes a value for valid models and well-formed terms (`val_interp`). For a closed formula (`env = []`), **the bounded semantics coincides with ordinary first-order satisfaction.** The reviewer's examples are rejected: `allNeC.wf Out [] 0 = false` and `EmptyDomain.valid [] = false` are kernel-checked in `tests/Boundary.lean`.

**(2) The evaluator decides the bounded semantics:**


One theorem connects the evaluator to the semantics. It is proved once, by induction on `Fm`, and holds for every formula and every model:

```lean
theorem Fm.check_iff (M : Model) (φ : Fm) : ∀ env, φ.check M env = true ↔ φ.Sem M env
```

**What a certificate states.** Each block is checked in one pass, `φ.wf M fns 0 && φ.check M []`, giving `Good M fns block` (`good_of_check`, `good_facts`). Blocks combine with `good_append`, `M.valid fns` is one more `decide +kernel`, and `countermodel_of_good` concludes:

```lean
theorem countermodel : ∀ φ ∈ problem, φ.Sat (M.toStructure (Model.valid_pos valid)) ⟨0, Model.valid_pos valid⟩ [] :=
  countermodel_of_good M fns problem valid good
-- #check @transitive_cnf.countermodel (generated from examples/transitive_cnf.p):
--   ∀ (φ : Fm), φ ∈ transitive_cnf.problem → Fm.Sat (transitive_cnf.M.toStructure ⋯) ⟨0, ⋯⟩ [] φ
-- @Fm.Sat : {α : Type} → Structure α → α → List α → Fm → Prop   (dot notation places φ last)
```

That is: **the ordinary first-order structure on `Fin n` satisfies every formula of the decoded problem.** What it does *not* state is that the decoded problem is the TPTP source; that is the trusted translation (§3.8).

The `atom` case is `rfl`. The propositional cases are `simp` with the induction hypotheses, and `imp` adds a case split on `φ.check M env`. The quantifier cases use

```lean
theorem allBelow_iff (f : Nat → Bool) : ∀ n, allBelow f n = true ↔ ∀ x, x < n → f x = true
theorem anyBelow_iff (f : Nat → Bool) : ∀ n, anyBelow f n = true ↔ ∃ x, x < n ∧ f x = true
```

each proved by recursion on `n`. Three lemmas lift `check_iff` to certificates:

| Lemma | Hypothesis (closed by `decide +kernel`) | Conclusion |
|---|---|---|
| `holds_of_check M φs` | `φs.all (·.check M []) = true` | `Holds M φs` |
| `holds_facts M s w K ar k` | `(List.range k).all (fun i => (fact s w K ar i).check M []) = true` | `Holds M (decodeFacts s w K ar k)` |
| `holds_append` | `Holds M a`, `Holds M b` | `Holds M (a ++ b)` |

These truth-only lemmas are the inner layer of `good_of_check`, `good_facts` and `good_append`, which add the well-formedness conjunct. In the generated certificate, `problem : List Fm` is a balanced `++` tree of the `decode D<b> …` and `decodeFacts F<j> …` blocks, a conjecture appears negated (opcode `4`), and `good : Good M fns problem` is a balanced tree of `good_append` over the per-block proofs `h<b>` and `hf<j>`; the public statement is `countermodel` above. NLP263+1's reflected certificate depends on the axioms `propext` and `Quot.sound` only. `#print axioms` on the library pins down where `Quot.sound` enters: through `allBelow_iff` and `anyBelow_iff`, the lemmas for the quantifier loops. `check_iff`, `holds_of_check` and `holds_facts` inherit it from them, and `holds_append` needs only `propext`. Both are standard Lean axioms, used throughout Mathlib.

**Fidelity, and its limit.** `decode`, `decodeFacts` and `M` are ordinary Lean definitions, so `#eval problem` prints the list of formulas the certificate is about. That is a useful diagnostic, not a proof of fidelity. It shows numeric symbol ids, so comparing it with the TPTP source needs the generator's symbol map and the rewrite. And `#eval` runs compiled code, so it adds nothing to the kernel proof. Fidelity to the source therefore rests on the trusted, tested translation (§3.8): a *verified checker* with a *tested translation pipeline*, not a verified TPTP-to-Lean compiler.

### 4.5 Shallow vs reflected certificates

| | Shallow (`emit`, §3.5) | Reflected (`emit_reflect`) |
|---|---|---|
| Statement form | one Lean `Prop` per formula over `inductive T`; `theorem c<i>' : φᵢ := by decide` | ordinary satisfaction `φ.Sat (M.toStructure …)` for every φ in `problem`, over `Fm` data |
| Trusted code | `lean()`, `sym()`, `emit()`, rewriter, kernel | `tokens()`, `as_fact()`, symbol numbering, rewriter, kernel. `Checker.lean` is proved, and `#eval problem` exposes the statement |
| Per-formula cost | parse + elaborate + typeclass search + `decide` for each formula | no per-formula elaboration: one Nat literal per block, evaluated by `decide +kernel` |
| Axioms | `propext` (examples) | `propext`, `Quot.sound` |
| Best use | quantifier-heavy problems | fact-heavy problems |

Measured (8 GB laptop, 8 cores):

| Workload | Shallow | Reflected |
|---|---|---|
| 10,000-fact slice, Lean 4.35, median of 3 (§6.3.1) | 31.1 s CPU | **9.8 s CPU** |
| NLP263+1, 1,026,857 facts, Lean 4.35, median of 3 (§6.3.1) | 14.1 min wall | **5.2 min** wall |
| PLA025+1, quantifier-heavy, 10-element model, Lean 4.35 | **4.4 s** | >400 s (did not finish); 228 s with the evaluator written using the primitive recursor |

Reflection wins on ground facts and loses badly on nested quantifiers. *Hypothesis:* lazy kernel evaluation re-decodes subformulas inside the `allBelow`/`anyBelow` loops, because the `decode …` term is unfolded under each quantifier instead of being shared. *Policy:* hybrid dispatch. `bench.py`'s `run_hybrid` reflects when `fact_share ≥ 0.9` and uses the shallow method otherwise. *Future work:* decode once and check the result. That means proving `decode D … = L` for an explicit list `L`, then running `check` on `L`, so that quantifier loops never touch the packed stream.

### 4.6 Independent checks of the reflected path (`test_cm.py`)

The reflected path trusts the encoder, not the evaluator. Two tests target it, both against `holds`, a brute-force evaluator of the original TPTP text. It reads records with its own reader and shares only the in-formula lexer and the variable collector with `cm.py`: no record reader, parser, rewriter or translator (§3.10).

| Test | Check |
|---|---|
| `test_reflected_certificate` | `lake build Checker` succeeds, and for every `examples/*.p` the `emit_reflect` output is accepted by `lake env lean`. |
| `test_reflected_mutants_agree_with_python` | Two random one-entry corruptions per example (seed 1): a predicate entry is flipped, or a function entry is changed to a different element. The list of reflected Lean verdicts must equal `[countermodel(p, *m) …]`, where `countermodel` evaluates `raw(p)`, the formulas as written in the source, and never `problem(p)`, the production rewriter. Call chain: `countermodel(p, n, consts, tables)` → `raw(p)` → `records(text)` (the oracle's own lexer and record matcher over the whole file) → `holds(f, n, consts, tables)` for each formula. Lean accepts **exactly** the mutants that Python accepts, and `not all(lean)` ensures that some mutant is rejected. |

A wrong translation in `tokens` or `as_fact` would certify a formula other than the TPTP one. The mutant test exposes this whenever a corrupted model separates the two formulas, which is why its docstring calls it a check on "the part of the reflected path that is trusted".
