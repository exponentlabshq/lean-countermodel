"""TPTP problem -> Vampire finite model -> Lean 4 counter-model, checked by `decide`.
Usage: python3 cm.py problem.p > Problem.lean   (Vampire on PATH, or set VAMPIRE)"""
import itertools, os, re, subprocess, sys

OPS = {"&": "∧", "|": "∨", "=>": "→", "<=>": "↔"}
TOKENS = r"<=>|=>|!=|'[^']*'|[\w$]+|\S"


def lean(s):
    """A TPTP fof formula as a Lean proposition over T."""
    t = re.findall(TOKENS, s)[::-1]
    nxt, peek = t.pop, lambda *k: t and t[-1] in k

    def form():
        a = unit()
        while peek(*OPS):
            a = f"({a} {OPS[nxt()]} {unit()})"
        return a

    def unit():
        k = nxt()
        if k == "~":
            return f"¬{unit()}"
        if k in "!?":  # ![X,Y]: body
            nxt()
            vs = [v for v in iter(nxt, "]") if v != ","]
            nxt()
            return f"({'∀' if k == '!' else '∃'} {' '.join(vs)} : T, {unit()})"
        if k == "(":
            a = form()
            nxt()
            return a
        a = term(k)
        return f"({a} {'=' if nxt() == '=' else '≠'} {term(nxt())})" if peek("=", "!=") else a

    def term(k):
        if k[0] == "$":
            return k[1:].capitalize()  # $true, $false
        k = k.strip("'")
        k = f"«{k}»" if k[0].islower() else k  # quoted: a TPTP name may be a Lean keyword
        if not peek("("):
            return k
        nxt()
        args = [term(nxt())]
        while nxt() == ",":
            args.append(term(nxt()))
        return f"({k} {' '.join(args)})"

    return form()


VARS = lambda f: set(re.findall(r"\b[A-Z]\w*", f))


def unwrap(ts):
    """Tokens without parentheses that enclose all of them."""
    while ts[:1] == ["("] and all(d > 0 for d in itertools.accumulate((t == "(") - (t == ")") for t in ts[:-1])):
        ts = ts[1:-1]
    return ts


def split(ts, op):
    """Token list split at `op` outside parentheses."""
    parts, d = [[]], 0
    for t in ts:
        d += (t == "(") - (t == ")")
        parts += [[]] if t == op and d == 0 else []
        parts[-1] += [] if t == op and d == 0 else [t]
    return [unwrap(p) for p in parts]


def clause(ts, scope):
    """(scope, disjuncts) of a formula flattened into one clause: ∀ is pulled out of disjuncts when its variables
    are fresh, `A → B` becomes `¬A1 ∨ … ∨ B`, and B is flattened in turn. Anything else stays one literal."""
    ts = unwrap(ts)
    body = ts[ts.index("]") + 2:] if ts[:1] == ["!"] else []
    whole = all(len(split(body, op)) == 1 for op in OPS)  # TPTP: `! [X] : A => B` is (∀X A) → B
    if body and whole and not (vs := set(ts[2:ts.index("]")]) - {","}) & scope:
        return clause(body, scope | vs)
    if len(imp := split(ts, "=>")) == 2:
        scope, rest = clause(imp[1], scope)
        return scope, [["~", "(", *g, ")"] for g in split(imp[0], "&")] + rest
    if len(ors := split(ts, "|")) > 1:
        lits = []
        for d in ors:
            scope, more = clause(d, scope)
            lits += more
        return scope, lits
    return scope, [ts]


def literals(f, cnf):
    """(scope, disjuncts) of a cnf clause (all variables in scope) or a fof formula."""
    scope, lits = clause(re.findall(TOKENS, f), VARS(f) if cnf else set())
    return scope, [f"({' '.join(l)})" for l in lits]  # parenthesized: `![Z]: A <=> B` would bind only A


def miniscope(scope, lits, bound=frozenset()):
    """∀scope over a disjunction, each variable bound just before its first literal, fewest new variables first.
    Sound since ∀X (A ∨ B) ↔ A ∨ ∀X B when X is not in A; `decide` then prunes like backtracking."""
    new = lambda l: (VARS(l) & scope) - bound
    lit = min(lits, key=lambda l: len(new(l)))  # greedy join order
    rest = [l for l in lits if l is not lit]
    body = f"({lit} | {miniscope(scope, rest, bound | new(lit))})" if rest else lit
    return f"![{','.join(sorted(new(lit)))}]: {body}" if new(lit) else body


def problem(path):
    """[(role, formula)] from a TPTP file: cnf clauses closed by ∀, and those plus ∀-implications in fof miniscoped."""
    src = re.sub(r"%.*", "", open(path).read())
    out = []
    for k, r, f in re.findall(r"(fof|cnf)\(\s*[\w']+\s*,\s*(\w+)\s*,(.*?)\)\s*\.(?=\s*(?:fof|cnf)\(|\s*$)", src, re.S):
        scope, lits = literals(f, k == "cnf")
        ok = k == "cnf" or scope and len(lits) > 1
        out.append((r, miniscope(scope, lits) if ok else f))
    return out


def model(path):
    """Vampire's finite model as (size, {constant: element}, {symbol: {args: element or bool}})."""
    out = subprocess.run([os.getenv("VAMPIRE", "vampire"), "-sa", "fmb", "-t", "30", path], capture_output=True, text=True).stdout
    if "FiniteModel" not in out:
        sys.exit(f"{path}: no finite counter-model found")
    m, el = out[out.index("FiniteModel"):], lambda s: int(re.search(r"\d+$", s)[0])
    tables = {}
    for neg, f, args, val in re.findall(r"(~?)'?(\w+)'?\(('fmb[^)]*)\)(?: = '(fmb[^']*)')?", m):
        tables.setdefault(f, {})[tuple(map(el, re.findall(r"fmb_\$i_\d+", args)))] = el(val) if val else not neg
    consts = {c: el(v) for c, v in re.findall(r"(\w+)_definition,axiom,'?\w+'? = '(fmb[^']*)'", m)}
    consts |= {c: not neg for c, neg in re.findall(r"(\w+)_definition,axiom,(~?)'?\w+'?\)\.", m)}  # propositions
    return len(re.findall(r"declare_\$i\d", m)), consts, tables


def emit(path, n, consts, tables):
    """The model and the claim `axioms ∧ ¬conjecture` as a Lean file."""
    name = os.path.basename(path).rsplit(".", 1)[0]
    ns, es, e = re.sub(r"\W", "_", name), [f"e{k}" for k in range(1, n + 1)], lambda k: f"T.e{k}"  # qualified: `.e1` in long tuple lists elaborates very slowly
    parts = [("¬" if r == "conjecture" else "") + lean(f) for r, f in problem(path)]
    claim = " ∧ ".join(parts)
    out = [f"-- Generated by cm.py from {name}.p: a {n}-element counter-model.",
           "set_option autoImplicit false  -- an unbound name is an error, never silently quantified",
           "set_option maxRecDepth 100000  -- long formulas recurse deeply",
           "set_option maxHeartbeats 0  -- no per-proof cap: the build's wall clock is the budget",
           "set_option synthInstance.maxSize 100000  -- deep formulas need deep instance search",
           f"namespace {ns}\n\ninductive T | {' | '.join(es)}\n  deriving DecidableEq\n",
           f"def T.all : List T := [{', '.join('T.' + x for x in es)}]",
           "theorem T.mem (x : T) : x ∈ T.all := by cases x <;> decide",
           "def T.idx : T → Nat\n  " + " ".join(f"| T.{x} => {i}" for i, x in enumerate(es))]
    for q, w in (("∀", "⟨fun h x => h x (T.mem x), fun h x _ => h x⟩"),
                 ("∃", "⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, T.mem x, h⟩⟩")):
        out.append(f"instance (p : T → Prop) [DecidablePred p] : Decidable ({q} x, p x) :=\n"
                   f"  decidable_of_iff ({q} x ∈ T.all, p x) {w}")
    out.append("")
    out += [f"abbrev «{c}» : Prop := {v}" if isinstance(v, bool) else f"abbrev «{c}» : T := {e(v)}" for c, v in consts.items()]
    for f, tbl in tables.items():
        k = len(next(iter(tbl)))
        xs, row = [f"x{j}" for j in range(k)], lambda a: ", ".join(map(e, a))
        if isinstance(next(iter(tbl.values())), bool):  # predicate: a bitmask over tuples; the kernel does Nat arithmetic natively
            mask = sum(1 << sum((x - 1) * n ** j for j, x in enumerate(a)) for a, v in tbl.items() if v)
            at = " + ".join(f"{n ** j} * {x}.idx" for j, x in enumerate(xs))
            out.append(f"abbrev «{f}» ({' '.join(xs)} : T) : Prop := ({mask} >>> ({at})) % 2 = 1")
        else:  # function: a pattern-matching table
            out.append(f"def «{f}» : {' → '.join(['T'] * (k + 1))}\n  " + " ".join(f"| {row(a)} => {e(v)}" for a, v in tbl.items()))
    # One theorem per formula: each `decide` starts with fresh caches, so memory doesn't pile up across formulas.
    out += [f"\ntheorem c{i} : {f} := by decide" for i, f in enumerate(parts)]
    proof = f"⟨{', '.join(f'c{i}' for i in range(len(parts)))}⟩" if len(parts) > 1 else "c0"  # ⟨c0⟩ is not a term
    return "\n".join(out) + f"\n\ntheorem countermodel : {claim} :=\n  {proof}\n\nend {ns}\n"


if __name__ == "__main__":
    print(emit(sys.argv[1], *model(sys.argv[1])), end="")
