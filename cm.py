"""TPTP problem -> Vampire finite model -> Lean 4 counter-model, checked by `decide`.
Usage: python3 cm.py problem.p > Problem.lean   (Vampire on PATH, or set VAMPIRE)"""
import hashlib, itertools, os, re, subprocess, sys
from functools import cache

OPS = {"&": "∧", "|": "∨", "=>": "→", "<=>": "↔"}
QUOTED = r"'(?:[^'\\]|\\.)*'"  # a quoted name; it may contain `%` and escaped quotes
TOKENS = rf"<~>|<=>|=>|<=|~\||~&|!=|{QUOTED}|\"(?:[^\"\\\\]|\\\\.)*\"|[\w$]+|\S"
UNSUPPORTED = {"<~>", "<=", "~|", "~&"}  # connectives cm.py does not translate: rejected, never misread
NAME = rf"(?:{QUOTED}|\w+)"  # a symbol in Vampire's model output, possibly quoted


def unsupported(k):
    """Reject a token outside the supported syntax, rather than translate it wrongly."""
    if k in UNSUPPORTED or k[0] in "\"0123456789" or (k[0] == "$" and k not in ("$true", "$false")):
        raise ValueError(f"unsupported TPTP syntax: {k!r} (see README: supported features)")


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
        if peek(*UNSUPPORTED):
            unsupported(nxt())
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
        unsupported(k)
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

    out = form()
    if t:  # every token must be consumed: trailing input means the formula was misread
        raise ValueError(f"unparsed TPTP input after a formula: {' '.join(t[::-1][:6])!r}")
    return out


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
    if m := re.search(r"\b(tff|thf|tcf|tpi|include)\s*\(", src):  # never certify a silently shortened problem
        raise ValueError(f"unsupported TPTP: {m[1]}(...) in {path}; cm.py reads self-contained fof/cnf only")
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


OPCODE = {"&": 5, "|": 6, "=>": 7, "<=>": 8}


def tokens(s, ids):
    """A TPTP formula as the token stream that CM.decode reads (prefix order; see Checker.lean).
    Variables become de Bruijn indices; symbols become numbers from `ids` ({"pred"|"fn"|"const": {name: id}})."""
    t = re.findall(TOKENS, s)[::-1]
    nxt, peek = t.pop, lambda *k: t and t[-1] in k

    def form(env):
        a = unit(env)
        while peek(*OPCODE):
            a = [OPCODE[nxt()], *a, *unit(env)]
        if peek(*UNSUPPORTED):
            unsupported(nxt())
        return a

    def unit(env):
        k = nxt()
        if k == "~":
            return [4, *unit(env)]
        if k in "!?":
            nxt()
            vs = [v for v in iter(nxt, "]") if v != ","]
            nxt()
            body = unit(vs[::-1] + env)  # the last-bound variable is index 0
            return [9 if k == "!" else 10] * len(vs) + body
        if k == "(":
            a = form(env)
            nxt()
            return a
        unsupported(k)
        if k in ("$true", "$false"):
            return [2 if k == "$true" else 3]
        args = args_of(env)
        if peek("=", "!="):  # an equation between terms
            positive, rhs = nxt() == "=", nxt()
            e = [1, *head(k, args, env), *term(rhs, env)]
            return e if positive else [4, *e]
        return [0, ids["pred"][k.strip("'")], len(args), *(x for a in args for x in a)]

    def args_of(env):
        if not peek("("):
            return []
        nxt()
        args = [term(nxt(), env)]
        while nxt() == ",":
            args.append(term(nxt(), env))
        return args

    def head(k, args, env):
        unsupported(k)
        if k[0] != "'" and k[0].isupper():
            return [0, env.index(k)]
        name = k.strip("'")
        return [2, ids["fn"][name], len(args), *(x for a in args for x in a)] if args else [1, ids["const"][name]]

    def term(k, env):
        return head(k, args_of(env), env)

    out = form([])
    if t:
        raise ValueError(f"unparsed TPTP input after a formula: {' '.join(t[::-1][:6])!r}")
    return out


def nesting(toks):
    """How deep the decoder recurses on one formula's tokens: an upper bound, the number of tokens."""
    return len(toks)


def as_fact(toks):
    """(polarity, predicate, constant ids) if the tokens are a ground literal over constants, else None."""
    sign, t = (0, toks[1:]) if toks[:1] == [4] else (1, toks)
    if t[:1] != [0] or len(t) != 3 + 2 * t[2] or any(t[3 + 2 * j] != 1 for j in range(t[2])):
        return None
    return sign, t[1], [t[4 + 2 * j] for j in range(t[2])]


def emit_reflect(path, n, consts, tables, block=4096, facts_per_block=128, per_part=32):
    """A certificate checked by the verified evaluator in Checker.lean: the model as packed tables, the problem
    as packed token streams of about `block` tokens, each block proved by one `decide +kernel`."""
    name = os.path.basename(path).rsplit(".", 1)[0]
    ns, forms = re.sub(r"\W", "_", name), problem(path)
    preds = {f: i for i, f in enumerate(sorted(f for f, t in tables.items() if isinstance(next(iter(t.values())), bool)))}
    preds |= {c: len(preds) + i for i, c in enumerate(sorted(c for c, v in consts.items() if isinstance(v, bool)))}
    fns = {f: i for i, f in enumerate(sorted(f for f, t in tables.items() if not isinstance(next(iter(t.values())), bool)))}
    cs = {c: i for i, c in enumerate(sorted(c for c, v in consts.items() if not isinstance(v, bool)))}
    w = max(n - 1, 1).bit_length()
    pack = lambda xs, width: sum(x << (i * width) for i, x in enumerate(xs))
    idx = lambda a: sum((x - 1) * n ** j for j, x in enumerate(a))
    masks = [0] * len(preds)
    for f, i in preds.items():
        masks[i] = (1 if consts[f] else 0) if f in consts else sum(1 << idx(a) for a, v in tables[f].items() if v)
    fn_tables = [0] * len(fns)
    for f, i in fns.items():
        fn_tables[i] = sum((v - 1) << (idx(a) * w) for a, v in tables[f].items())
    cvals = [consts[c] - 1 for c in sorted(cs, key=cs.get)]
    K = 4096  # constants per packed block: shifts stay small
    cblocks = [pack(cvals[j:j + K], w) for j in range(0, len(cvals), K)] or [0]
    mw = max([m.bit_length() for m in masks] + [1])

    def bsearch(var, xs, lo=0):
        """xs[var] as a balanced tree of comparisons: O(log n), where a `match` on literals is a chain, O(n)."""
        if len(xs) <= 1:
            return str(xs[0]) if xs else "0"  # no symbols of this kind
        mid = len(xs) // 2
        return f"if {var} < {lo + mid} then {bsearch(var, xs[:mid], lo)} else {bsearch(var, xs[mid:], lo + mid)}"
    ids = {"pred": preds, "fn": fns, "const": cs}
    data = [([4] if r == "conjecture" else []) + tokens(f, ids) for r, f in forms]
    facts, data = [d for d in data if as_fact(d)], [d for d in data if not as_fact(d)]  # facts go in fact tables
    tw = max(max((x for d in data for x in d), default=0), 10).bit_length()  # token width
    out = [f"-- Generated by cm.py --reflect from {name}.p: a {n}-element model, checked by Checker's CM.Fm.check.",
           "import Checker", "set_option maxRecDepth 100000", "set_option linter.unusedVariables false", "set_option maxHeartbeats 0", "open CM",
           f"namespace {ns}\n",
           f"def M : Model where\n  n := {n}\n"
           f"  const c := get ({bsearch('c / ' + str(K), cblocks)}) (c % {K}) {w}\n"
           f"  fn f args := get ({bsearch('f', fn_tables)}) (index {n} args) {w}\n"
           f"  pred p args := get (get {pack(masks, mw)} p {mw}) (index {n} args) 1 == 1\n",  # O(1) packed lookup
           "/-- The functions the problem uses, with their arities: `M.valid` checks they map the domain into itself. -/",
           f"def fns : List (Nat × Nat) := [{', '.join(f'({i}, {len(next(iter(tables[f])))})' for f, i in sorted(fns.items(), key=lambda x: x[1]))}]",
           "theorem valid : M.valid fns = true := by decide +kernel\n"]
    blocks = []  # (Lean declarations, decoded formulas, proof of Holds)
    if facts:
        K = max(len(as_fact(d)[2]) for d in facts)
        recs = [[sign, p, *args, *[0] * (K - len(args))] for sign, p, args in map(as_fact, facts)]
        fw = max(max(x for r in recs for x in r), 1).bit_length()
        arity = [0] * len(preds)
        for d in facts:
            arity[as_fact(d)[1]] = len(as_fact(d)[2])
        aw = max(K, 1).bit_length()
        out.append(f"/-- The arity of each predicate used in a fact table. -/\ndef ar (p : Nat) : Nat := get {pack(arity, aw)} p {aw}\n")
        for b in range(0, len(recs), facts_per_block):
            rs = recs[b:b + facts_per_block]
            j = b // facts_per_block
            blocks.append((f"/-- {len(rs)} ground facts, {K + 2} fields of {fw} bits each. -/\ndef F{j} : Nat := {pack([x for r in rs for x in r], fw)}\n"
                           f"theorem hf{j} : Good M fns (decodeFacts F{j} {fw} {K} ar {len(rs)}) := good_facts M fns _ _ _ _ _ (by decide +kernel)\n",
                           f"decodeFacts F{j} {fw} {K} ar {len(rs)}", f"hf{j}"))
    parts, cur, size = [], [], 0
    for d in data:  # blocks of about `block` tokens, so each shift touches a small number
        if cur and size + len(d) > block:
            parts.append(cur)
            cur, size = [], 0
        cur.append(d)
        size += len(d)
    parts.append(cur) if cur else None
    for b, fs in enumerate(parts):
        depth = max(map(nesting, fs)) + 2
        blocks.append((f"/-- {len(fs)} formulas, as {tw}-bit tokens. -/\ndef D{b} : Nat := {pack([x for d in fs for x in d], tw)}\n"
                       f"theorem h{b} : Good M fns (decode D{b} {tw} {len(fs)} {depth}) := good_of_check M fns _ (by decide +kernel)\n",
                       f"decode D{b} {tw} {len(fs)} {depth}", f"h{b}"))
    doc = f"/-- Every formula of {name}.p, decoded; `#eval` it to read them. A conjecture appears negated. -/"
    if len(blocks) <= per_part:  # one file
        out += [d for d, _, _ in blocks]
        out += [doc, f"def problem : List Fm := {tree([t for _, t, _ in blocks], '({} ++ {})')}",
                f"theorem good : Good M fns problem :=\n  {tree([p for _, _, p in blocks], '(good_append {} {})')}",
                f"/-- The ordinary first-order structure on `Fin M.n` satisfies every formula of {name}.p (a conjecture negated). -/",
                "theorem countermodel : ∀ φ ∈ problem, φ.Sat (M.toStructure (Model.valid_pos valid)) ⟨0, Model.valid_pos valid⟩ [] :=\n"
                "  countermodel_of_good M fns problem valid good"]
        return "\n".join(out) + f"\n\nend {ns}\n"
    # Modules, aggregated as a tree: Base (the model), Part k (blocks, their list and its proof), Main.
    head = "\n".join(out[:out.index(f"namespace {ns}\n")])
    files = {"Base": "\n".join(out) + f"\n\nend {ns}\n"}
    opts = "\n".join(l for l in head.split("\n") if l.startswith("set_option"))
    for k in range(0, len(blocks), per_part):
        bs, c = blocks[k:k + per_part], k // per_part
        files[f"Part{c}"] = (f"import {ns}.Base\n{opts}\nopen CM\nnamespace {ns}\n\n" + "\n".join(d for d, _, _ in bs)
                             + f"\ndef part{c} : List Fm := {tree([t for _, t, _ in bs], '({} ++ {})')}\n"
                             f"theorem hpart{c} : Good M fns part{c} := {tree([p for _, _, p in bs], '(good_append {} {})')}\n\nend {ns}\n")
    m = len(files) - 1
    files["Main"] = ("".join(f"import {ns}.Part{c}\n" for c in range(m)) + f"open CM\nnamespace {ns}\n\n{doc}\n"
                     f"def problem : List Fm := {tree([f'part{c}' for c in range(m)], '({} ++ {})')}\n"
                     f"theorem good : Good M fns problem :=\n  {tree([f'hpart{c}' for c in range(m)], '(good_append {} {})')}\n"
                     f"theorem countermodel : ∀ φ ∈ problem, φ.Sat (M.toStructure (Model.valid_pos valid)) ⟨0, Model.valid_pos valid⟩ [] :=\n"
                     f"  countermodel_of_good M fns problem valid good\n\nend {ns}\n")
    return files


if __name__ == "__main__":  # cm.py [--reflect] problem.p [DIR]: one file to stdout, or Lean modules DIR/<name>/*.lean
    reflect = sys.argv[1] == "--reflect"
    args = sys.argv[2:] if reflect else sys.argv[1:]
    out = (emit_reflect if reflect else emit)(args[0], *model(args[0]))
    sys.argv = [sys.argv[0], *args]
    if isinstance(out, str) and len(sys.argv) < 3:
        print(out, end="")
    else:
        ns = re.sub(r"\W", "_", os.path.basename(sys.argv[1]).rsplit(".", 1)[0])
        os.makedirs(d := os.path.join(sys.argv[2], ns), exist_ok=True)
        for f, text in (out if isinstance(out, dict) else {"Main": out}).items():
            open(os.path.join(d, f + ".lean"), "w").write(text)
        print(f"{len(out) if isinstance(out, dict) else 1} Lean modules in {d}")
