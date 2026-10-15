"""TPTP problem -> Vampire finite model -> Lean 4 counter-model, checked by `decide`.
Usage: python3 cm.py problem.p > Problem.lean   (Vampire on PATH, or set VAMPIRE)"""
import hashlib, itertools, os, re, subprocess, sys
from functools import cache

OPS = {"&": "∧", "|": "∨", "=>": "→", "<=>": "↔"}
QUOTED = r"'(?:[^'\\]|\\.)*'"  # a quoted name; it may contain `%` and escaped quotes
TOKENS = rf"<=>|=>|!=|{QUOTED}|[\w$]+|\S"
NAME = rf"(?:{QUOTED}|\w+)"  # a symbol in Vampire's model output, possibly quoted


def sym(k):
    """A TPTP symbol as a Lean name: «abc» if TPTP needs no quotes, «'X'» if it does. Quoted names keep their
    quotes, so a constant 'X' or 'T' can never become the variable X or the type T."""
    return f"«{k}»" if re.fullmatch(r"[a-z]\w*", k) else f"«'{k}'»"


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
        k = sym(k.strip("'")) if k[0] == "'" or k[0].islower() else k  # a symbol; a variable otherwise
        if not peek("("):
            return k
        nxt()
        args = [term(nxt())]
        while nxt() == ",":
            args.append(term(nxt()))
        return f"({k} {' '.join(args)})"

    return form()


VARS = cache(lambda f: frozenset(re.findall(r"\b[A-Z]\w*", re.sub(QUOTED, "", f))))  # memoized; quoted names are never variables


def uncomment(src):
    """Source without `%` comments; a `%` inside a quoted name is not a comment."""
    return re.sub(rf"({QUOTED})|%.*", lambda m: m[1] or "", src)


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
    src = uncomment(open(path).read())
    out = []
    for k, r, f in re.findall(r"(fof|cnf)\(\s*[\w']+\s*,\s*(\w+)\s*,(.*?)\)\s*\.(?=\s*(?:fof|cnf)\(|\s*$)", src, re.S):
        scope, lits = literals(f, k == "cnf")
        ok = k == "cnf" or scope and len(lits) > 1
        out.append((r, miniscope(scope, lits) if ok else f))
    return out


def vampire(path):
    """Vampire's output, cached in $CM_CACHE (if set) under a hash of the problem, the flags and Vampire's version:
    a Lean upgrade then reruns only Lean."""
    # `-updr off`: otherwise Vampire may settle the problem by deleting unused predicates, without printing a model
    cmd = [os.getenv("VAMPIRE", "vampire"), "-sa", "fmb", "-updr", "off", "-t", "30"]
    if cache := os.getenv("CM_CACHE"):
        version = subprocess.run([cmd[0], "--version"], capture_output=True, text=True).stdout
        key = hashlib.sha256(open(path, "rb").read() + " ".join(cmd[1:]).encode() + version.encode()).hexdigest()
        if os.path.exists(hit := os.path.join(cache, key)):
            return open(hit).read()
    out = subprocess.run(cmd + [path], capture_output=True, text=True).stdout
    if cache and "Time limit" not in out:  # a timeout depends on the machine's load, not the problem
        os.makedirs(cache, exist_ok=True)
        open(hit, "w").write(out)
    return out


def model(path):
    """Vampire's finite model as (size, {constant: element}, {symbol: {args: element or bool}})."""
    out = vampire(path)
    if "FiniteModel" not in out:
        sys.exit(f"{path}: no finite counter-model found")
    m, el = out[out.index("FiniteModel"):], lambda s: int(re.search(r"\d+$", s)[0])
    tables = {}
    for neg, f, args, val in re.findall(rf"(~?)({NAME})\(('fmb[^)]*)\)(?: = '(fmb[^']*)')?", m):
        tables.setdefault(f.strip("'"), {})[tuple(map(el, re.findall(r"fmb_\$i_\d+", args)))] = el(val) if val else not neg
    consts = {c: el(v) for c, v in re.findall(rf"tff\('?(.*?)_definition'?,axiom,{NAME} = '(fmb[^']*)'", m)}
    consts |= {c: not neg for c, neg in re.findall(rf"tff\('?(.*?)_definition'?,axiom,(~?){NAME}\)\.", m)}  # propositions
    return len(re.findall(r"declare_\$i\d", m)), consts, tables


CHUNK = int(os.getenv("CM_CHUNK", 2000))  # formulas per Lean module, when a problem has more


def tree(xs, pair):
    """xs combined as a balanced binary tree: depth log₂ n instead of n."""
    return xs[0] if len(xs) == 1 else pair.format(tree(xs[:len(xs) // 2], pair), tree(xs[len(xs) // 2:], pair))


def emit(path, n, consts, tables):
    """The model and the claim `axioms ∧ ¬conjecture` as a Lean file."""
    name = os.path.basename(path).rsplit(".", 1)[0]
    ns, es, e = re.sub(r"\W", "_", name), [f"e{k}" for k in range(1, n + 1)], lambda k: f"T.e{k}"  # qualified: `.e1` in long tuple lists elaborates very slowly
    parts = [("¬" if r == "conjecture" else "") + lean(f) for r, f in problem(path)]
    claim = tree([f"({p})" for p in parts], "({} ∧ {})")  # balanced: a chain of 10,000 ∧ overflows the kernel
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
    names = [f"abbrev {sym(c)} : Prop := {v}" if isinstance(v, bool) else f"abbrev {sym(c)} : T := {e(v)}" for c, v in consts.items()]
    out += names if len(parts) <= CHUNK else []  # modular output puts the constants in their own modules
    for f, tbl in tables.items():
        k = len(next(iter(tbl)))
        xs, row = [f"x{j}" for j in range(k)], lambda a: ", ".join(map(e, a))
        if isinstance(next(iter(tbl.values())), bool):  # predicate: a bitmask over tuples; the kernel does Nat arithmetic natively
            mask = sum(1 << sum((x - 1) * n ** j for j, x in enumerate(a)) for a, v in tbl.items() if v)
            at = " + ".join(f"{n ** j} * {x}.idx" for j, x in enumerate(xs))
            out.append(f"abbrev {sym(f)} ({' '.join(xs)} : T) : Prop := ({mask} >>> ({at})) % 2 = 1")
        else:  # function: a pattern-matching table
            out.append(f"def {sym(f)} : {' → '.join(['T'] * (k + 1))}\n  " + " ".join(f"| {row(a)} => {e(v)}" for a, v in tbl.items()))
    if len(parts) <= CHUNK:  # one file: one theorem per formula, so each `decide` starts with fresh caches
        out += [f"\ntheorem c{i} : {f} := by decide" for i, f in enumerate(parts)]
        proof = tree([f"c{i}" for i in range(len(parts))], "⟨{}, {}⟩")
        return "\n".join(out) + f"\n\ntheorem countermodel : {claim} :=\n  {proof}\n\nend {ns}\n"
    # Many formulas: modules, aggregated as a tree. Base holds the model; each chunk names its formulas (P_i),
    # proves them (c_i) and their conjunction (C_j); Main combines the C_j. No file restates the whole problem,
    # and lake checks the chunks in parallel.
    opts = "\n".join(l for l in out[:5] if l.startswith("set_option"))
    files = {"Base": "\n".join(out) + f"\n\nend {ns}\n"}
    # Lean 4.13 fails ("deep recursion") on files with more than about 20,000 declarations, so constants go in
    # modules of CHUNK * 5 (10,000 by default).
    for k in range(0, len(names), CHUNK * 5):
        files[f"Names{k // (CHUNK * 5)}"] = f"import {ns}.Base\nnamespace {ns}\n\n" + "\n".join(names[k:k + CHUNK * 5]) + f"\n\nend {ns}\n"
    imports = "".join(f"import {ns}.{f}\n" for f in files)
    for j in range(0, len(parts), CHUNK):
        ks = range(j, min(j + CHUNK, len(parts)))
        body = "\n".join(f"def P{i} : Prop := {parts[i]}\ntheorem c{i} : P{i} := by unfold P{i}; decide" for i in ks)
        c = j // CHUNK
        files[f"Chunk{c}"] = (f"{imports}{opts}\nnamespace {ns}\n\n{body}\n\n"
                              f"def C{c} : Prop := {tree([f'P{i}' for i in ks], '({} ∧ {})')}\n"
                              f"theorem chunk{c} : C{c} := by unfold C{c}; exact {tree([f'c{i}' for i in ks], '⟨{}, {}⟩')}\n\nend {ns}\n")
    m = sum(f.startswith("Chunk") for f in files)
    files["Main"] = ("".join(f"import {ns}.Chunk{c}\n" for c in range(m)) + f"namespace {ns}\n\n"
                     f"/-- Every formula holds in the model: C_j is the conjunction of chunk j's formulas P_i. -/\n"
                     f"theorem countermodel : {tree([f'C{c}' for c in range(m)], '({} ∧ {})')} :=\n"
                     f"  {tree([f'chunk{c}' for c in range(m)], '⟨{}, {}⟩')}\n\nend {ns}\n")
    return files


if __name__ == "__main__":  # cm.py problem.p [DIR]: one file to stdout, or Lean modules DIR/<name>/*.lean
    out = emit(sys.argv[1], *model(sys.argv[1]))
    if isinstance(out, str) and len(sys.argv) < 3:
        print(out, end="")
    else:
        ns = re.sub(r"\W", "_", os.path.basename(sys.argv[1]).rsplit(".", 1)[0])
        os.makedirs(d := os.path.join(sys.argv[2], ns), exist_ok=True)
        for f, text in (out if isinstance(out, dict) else {"Main": out}).items():
            open(os.path.join(d, f + ".lean"), "w").write(text)
        print(f"{len(out) if isinstance(out, dict) else 1} Lean modules in {d}")
