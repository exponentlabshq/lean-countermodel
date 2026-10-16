"""Is cm.py sound, faithful and general? Lean, an independent Python evaluator and known answers must agree."""
import glob, itertools, os, random, re, shutil, subprocess, pytest
from functools import cache
from concurrent.futures import ThreadPoolExecutor
from cm import TOKENS, VARS, emit, emit_reflect, model, problem, statements

# Each test says what it needs, so the translator's rejection and preprocessing tests run without Vampire or Lean.
needs_vampire = pytest.mark.skipif(not shutil.which(os.getenv("VAMPIRE", "vampire")), reason="needs vampire")
needs_lake = pytest.mark.skipif(not shutil.which("lake"), reason="needs lake")
EXAMPLES = sorted(glob.glob("examples/*.p"))
run = lambda *a: subprocess.run(a, capture_output=True, text=True)


def holds(s, n, consts, tables, env={}):
    """Evaluate a TPTP formula in a finite model by brute force. Written separately from cm.lean."""
    t = re.findall(TOKENS, s)[::-1]
    nxt, peek = t.pop, lambda *k: t and t[-1] in k
    op = {"&": bool.__and__, "|": bool.__or__, "=>": lambda a, b: not a or b, "<=>": bool.__eq__}

    def form():  # each parser returns a function of the variable assignment
        a = unit()
        while peek(*op):
            a = (lambda a, o, b: lambda v: o(a(v), b(v)))(a, op[nxt()], unit())
        return a

    def unit():
        k = nxt()
        if k == "~":
            return (lambda a: lambda v: not a(v))(unit())
        if k in "!?":
            nxt()
            xs = [x for x in iter(nxt, "]") if x != ","]
            nxt()
            body, q = unit(), all if k == "!" else any
            return lambda v: q(body({**v, **dict(zip(xs, es))}) for es in itertools.product(range(1, n + 1), repeat=len(xs)))
        if k == "(":
            return (form(), nxt())[0]
        a = term(k)
        if peek("=", "!="):
            eq, b = nxt() == "=", term(nxt())
            return lambda v: (a(v) == b(v)) == eq
        return a

    def term(k):
        if k[0] == "$":
            return lambda v: k == "$true"
        quoted, k, args = k[0] == "'", k.strip("'"), []
        if peek("("):
            nxt()
            args.append(term(nxt()))
            while nxt() == ",":
                args.append(term(nxt()))
        if k[0].isupper() and not quoted:
            return lambda v: v[k]
        return lambda v: tables[k][tuple(a(v) for a in args)] if args else consts[k]

    f = form()
    if t:  # the whole formula must be consumed: trailing tokens are an error, never ignored
        raise ValueError(f"unparsed tokens after a formula: {t[::-1][:5]}")
    return f(env)


# The oracle's own reader of source records. It shares no code with cm.statements: a separate lexer and a token-level
# record matcher, written to the TPTP grammar for annotated formulas. Peer review found that an earlier oracle copied
# cm.py's record regex, so both silently skipped the same records; this one counts records independently.
ORACLE_LEX = re.compile(r"""(?P<ws>\s+)|(?P<comment>%[^\n]*)|(?P<sq>'(?:[^'\\]|\\.)*')|(?P<dq>"(?:[^"\\]|\\.)*")
                            |(?P<word>[A-Za-z0-9_$]+)|(?P<op><~>|<=>|=>|<=|~\||~&|!=|.)""", re.X | re.S)
ORACLE_ROLES = ("axiom", "hypothesis", "definition", "assumption", "lemma", "theorem", "corollary", "plain",
                "negated_conjecture", "conjecture")


def records(text):
    """[(kind, name, role, formula)] for every record of a TPTP text, or ValueError: nothing may be left over."""
    toks = [(m.lastgroup, m[0]) for m in ORACLE_LEX.finditer(text) if m.lastgroup not in ("ws", "comment")]
    if any(a == "/" and b == "*" for (_, a), (_, b) in zip(toks, toks[1:])):
        raise ValueError("block comment")
    out, i = [], 0
    while i < len(toks):
        if toks[i] not in (("word", "fof"), ("word", "cnf")) or toks[i + 1:i + 2] != [("op", "(")]:
            raise ValueError(f"not a fof/cnf record: {toks[i:i + 3]}")
        kind, args, cur, depth, i = toks[i][1], [], [], 0, i + 2
        while True:
            if i >= len(toks):
                raise ValueError("unterminated record")
            t = toks[i][1]
            i += 1
            if t in "([" and toks[i - 1][0] == "op":
                depth += 1
            elif t in ")]" and toks[i - 1][0] == "op":
                if depth == 0:
                    args.append(cur)
                    break
                depth -= 1
            elif t == "," and depth == 0:
                args.append(cur)
                cur = []
                continue
            cur.append(t)
        if toks[i:i + 1] != [("op", ".")]:
            raise ValueError("record not closed by '.'")
        i += 1
        if len(args) < 3 or len(args[0]) != 1 or len(args[1]) != 1 or args[1][0] not in ORACLE_ROLES or not args[2]:
            raise ValueError(f"malformed record: {args[:2]}")
        out.append((kind, args[0][0], args[1][0], " ".join(args[2])))
    return out


def raw(path):
    """[(role, formula)] for every source record, read by the oracle's own reader; cnf clauses closed by ∀."""
    return [(r, f"![{','.join(sorted(VARS(f)))}]: ({f})" if k == "cnf" and VARS(f) else f) for k, _, r, f in records(open(path).read())]


def countermodel(path, n, consts, tables):
    """Python's verdict on the *original* formulas, independent of the rewriting: axioms hold, the conjecture fails."""
    return all(holds(f, n, consts, tables) != (r == "conjecture") for r, f in raw(path))


def lean_accepts(path, m, tmp, emitter=emit):
    file = tmp / f"{os.path.basename(path)[:-2]}_{emitter.__name__}_{id(m)}.lean"
    file.write_text(emitter(path, *m))
    return run("lake", "env", "lean", str(file)).returncode == 0


M = cache(model)


@needs_vampire
@pytest.mark.parametrize("p", EXAMPLES)
def test_compiles_to_committed_file(p):
    assert run("python3", "cm.py", p).stdout == open(f"Cm/{os.path.basename(p)[:-2]}.lean").read()


@needs_vampire
@pytest.mark.parametrize("p", EXAMPLES)
def test_reflects_to_committed_file(p):
    """Refl/ holds the reflected certificate of every example; recheck.sh replays both libraries from scratch."""
    assert run("python3", "cm.py", "--reflect", p).stdout == open(f"Refl/{os.path.basename(p)[:-2]}.lean").read()


@needs_lake
def test_kernel_accepts_with_propext_only():
    assert run("lake", "build").returncode == 0
    out = run("lake", "env", "lean", "Axioms.lean").stdout.splitlines()
    assert len(out) == len(EXAMPLES) and all(l.endswith("[propext]") for l in out)


@needs_vampire
@pytest.mark.parametrize("p", EXAMPLES)
def test_python_agrees_it_is_a_countermodel(p):
    assert countermodel(p, *M(p))


@needs_vampire
def test_circle_of_fifths_is_the_known_answer():
    """Minimal model: exactly 12 notes, and up-a-fifth is x -> x+7 (mod 12) under C=0, up-a-fourth its inverse."""
    n, consts, t = M("examples/circle_of_fifths.p")
    note, x = {}, consts["c"]
    for k in range(12):
        note[x], x = 7 * k % 12, t["f"][(x,)]
    assert n == 12 and len(set(note.values())) == 12
    assert all(note[t["f"][(y,)]] == (note[y] + 7) % 12 and note[t["g"][(y,)]] == (note[y] + 5) % 12 for y in note)


@needs_vampire
@needs_lake
def test_mutants_lean_and_python_agree(tmp_path):
    """Corrupt one table entry at a time: Lean must accept exactly the mutants Python says are still counter-models."""
    rnd, cases = random.Random(0), []
    for p in EXAMPLES:
        n, consts, tables = M(p)
        for _ in range(2):
            f = rnd.choice(sorted(tables))
            args = rnd.choice(sorted(tables[f]))
            v = tables[f][args]
            new = not v if isinstance(v, bool) else rnd.choice([e for e in range(1, n + 1) if e != v])
            cases.append((p, (n, consts, {**tables, f: {**tables[f], args: new}})))
    with ThreadPoolExecutor() as pool:
        lean = list(pool.map(lambda c: lean_accepts(*c, tmp_path), cases))
    assert lean == [countermodel(p, *m) for p, m in cases]
    assert not all(lean)  # the corruption actually breaks some models


@needs_vampire
def test_a_theorem_has_no_counter_model(tmp_path):
    (tmp_path / "t.p").write_text("fof(a, axiom, ![X]: p(X)).\nfof(c, conjecture, p(k)).\n")
    assert run("python3", "cm.py", str(tmp_path / "t.p")).returncode != 0


@needs_vampire
@pytest.mark.parametrize("p", EXAMPLES)
def test_rewriting_preserves_meaning(p):
    """Each miniscoped formula agrees with the original, on the model and on every one-entry mutation of it."""
    n, consts, tables = M(p)
    source, rewritten = raw(p), problem(p)
    assert len(source) == len(rewritten)  # one rewritten formula per source record, none dropped
    other = lambda v: not v if isinstance(v, bool) else v % n + 1
    models = [tables] + [{**tables, f: {**t, a: other(v)}} for f, t in tables.items() for a, v in t.items()]
    for (_, f), (_, g) in zip(source, rewritten):
        assert all(holds(f, n, consts, m) == holds(g, n, consts, m) for m in models)


@needs_vampire
@needs_lake
def test_large_problems_split_into_modules(tmp_path):
    """Above CM_CHUNK formulas, cm.py writes Base, chunk and Main modules aggregated as a tree; lake must accept them."""
    for f in ("lean-toolchain",):
        (tmp_path / f).write_text(open(f).read())
    (tmp_path / "lakefile.toml").write_text('name = "t"\ndefaultTargets = ["nakamura_a12"]\n\n[[lean_lib]]\nname = "nakamura_a12"\nglobs = ["nakamura_a12.+"]\n')
    env = {**os.environ, "CM_CHUNK": "2"}
    assert subprocess.run(["python3", os.path.abspath("cm.py"), os.path.abspath("examples/nakamura_a12.p"), str(tmp_path)],
                          env=env, capture_output=True, text=True).stdout.startswith("9 Lean modules")  # 13 formulas, no constants: 7 chunks, Base, Main
    assert subprocess.run(["lake", "build"], cwd=tmp_path, capture_output=True).returncode == 0
    (tmp_path / "ax.lean").write_text("import nakamura_a12.Main\n#print axioms nakamura_a12.countermodel\n")
    out = subprocess.run(["lake", "env", "lean", "ax.lean"], cwd=tmp_path, capture_output=True, text=True).stdout
    assert "sorryAx" not in out and "countermodel" in out


@needs_vampire
@needs_lake
def test_constants_split_into_name_modules(tmp_path):
    """Constants go in their own modules (Names*), so no file passes Lean's ~20,000-declaration limit."""
    (tmp_path / "lean-toolchain").write_text(open("lean-toolchain").read())
    (tmp_path / "lakefile.toml").write_text('name = "t"\ndefaultTargets = ["quoted_capture"]\n\n[[lean_lib]]\nname = "quoted_capture"\nglobs = ["quoted_capture.+"]\n')
    out = subprocess.run(["python3", os.path.abspath("cm.py"), os.path.abspath("examples/quoted_capture.p"), str(tmp_path)],
                         env={**os.environ, "CM_CHUNK": "1"}, capture_output=True, text=True).stdout
    assert (tmp_path / "quoted_capture" / "Names0.lean").exists() and "Lean modules" in out
    assert subprocess.run(["lake", "build"], cwd=tmp_path, capture_output=True).returncode == 0


@needs_vampire
def test_vampire_cache_is_transparent(tmp_path):
    """With CM_CACHE set, the second run reads Vampire's answer from the cache and emits the same Lean."""
    env = {**os.environ, "CM_CACHE": str(tmp_path)}
    first = subprocess.run(["python3", "cm.py", "examples/group_comm.p"], env=env, capture_output=True, text=True).stdout
    assert len(os.listdir(tmp_path)) == 1
    second = subprocess.run(["python3", "cm.py", "examples/group_comm.p"], env=env, capture_output=True, text=True).stdout
    assert first == second == open("Cm/group_comm.lean").read()


@needs_vampire
@needs_lake
@pytest.mark.parametrize("p", EXAMPLES)
def test_reflected_certificate(p, tmp_path):
    """The same model, certified through the verified evaluator (Checker.lean) instead of one decide per formula."""
    assert run("lake", "build", "Checker").returncode == 0
    assert lean_accepts(p, M(p), tmp_path, emit_reflect)


@needs_vampire
@needs_lake
def test_reflected_mutants_agree_with_python(tmp_path):
    """Corrupt one table entry at a time: the reflected certificate must accept exactly what Python accepts.
    This checks cm.py's translation into Fm data, the part of the reflected path that is trusted."""
    rnd, cases = random.Random(1), []
    for p in EXAMPLES:
        n, consts, tables = M(p)
        for _ in range(2):
            f = rnd.choice(sorted(tables))
            args = rnd.choice(sorted(tables[f]))
            v = tables[f][args]
            new = not v if isinstance(v, bool) else rnd.choice([e for e in range(1, n + 1) if e != v])
            cases.append((p, (n, consts, {**tables, f: {**tables[f], args: new}})))
    assert run("lake", "build", "Checker").returncode == 0
    with ThreadPoolExecutor() as pool:
        lean = list(pool.map(lambda c: lean_accepts(*c, tmp_path, emit_reflect), cases))
    assert lean == [countermodel(p, *m) for p, m in cases]
    assert not all(lean)


@needs_vampire
@needs_lake
def test_ablation_finds_what_a_conclusion_needs(tmp_path):
    """p(c) needs axiom `a` (a certified counter-model without it) and not `b`; an underivable target never 'needs'."""
    from ablate import ablate, table
    t = tmp_path / "t.p"
    t.write_text("fof(a, axiom, p(c)).\nfof(b, axiom, q(c)).\nfof(c1, conjecture, p(c)).\nfof(c2, conjecture, r(c)).\n")
    report = ablate(str(t), str(tmp_path / "out"))
    v = {(r["target"], r["without"]): r["verdict"] for r in report["results"]}
    assert v[("c1", None)] == "follows" and v[("c1", "a")] == "does not follow" and v[("c1", "b")] == "follows"
    assert v[("c2", None)] == "does not follow" and report["minimal"] == {"c1": ["a"]}
    assert "**needed**" in table(report) and "still does not follow" in table(report)


@needs_lake
def test_boundary_cases_are_rejected_by_the_kernel():
    """tests/Boundary.lean: invalid models and ill-formed or malformed formulas cannot produce a certificate."""
    assert run("lake", "build", "Checker").returncode == 0
    out = run("lake", "env", "lean", "tests/Boundary.lean")
    assert out.returncode == 0, out.stdout + out.stderr


def test_quoted_and_plain_names_are_the_same_symbol():
    """TPTP: 'cat' and cat are one symbol; 'X' is a constant, never the variable X."""
    from cm import lean
    assert lean("p('cat')") == lean("p(cat)")
    assert lean("![X]: p('X', X)") == "(∀ X' : T, («p» «'X'» X'))"


@pytest.mark.parametrize("formula", ["(p <~> q)", "(p <= q)", "(p ~| q)", "(p ~& q)", "$distinct(a,b)", "p(3)", 'p("s")'])
def test_unsupported_syntax_is_rejected_not_misread(formula):
    """TPTP features outside the supported core must raise, in both translators, never translate to a different formula."""
    from cm import lean, tokens
    with pytest.raises(ValueError):
        lean(formula)
    with pytest.raises(ValueError):
        tokens(formula, {"pred": {"p": 0, "q": 1}, "fn": {}, "const": {"a": 0, "b": 1}})


@pytest.mark.parametrize("stmt", ["tff(t, type, a: $i).", "include('Axioms/X.ax')."])
def test_typed_statements_and_includes_are_rejected(tmp_path, stmt):
    """A problem cm.py cannot read completely is refused, rather than certified as a silently shortened problem."""
    p = tmp_path / "t.p"
    p.write_text(stmt + "\nfof(a, axiom, p(c)).\nfof(c, conjecture, q(c)).\n")
    with pytest.raises(ValueError):
        problem(str(p))


def test_a_symbol_at_two_arities_is_rejected(tmp_path):
    """TPTP's p/1 and p/2 are different symbols; the model tables are keyed by name, so such a problem is refused."""
    p = tmp_path / "t.p"
    p.write_text("fof(a, axiom, p(c)).\nfof(b, axiom, p(c, c)).\nfof(g, conjecture, q(c)).\n")
    with pytest.raises(ValueError):
        problem(str(p))


def test_benchmark_records_unsupported_input(tmp_path, monkeypatch):
    """An input cm.py refuses stays in the benchmark denominator as 'unsupported input', and one that crashes the
    translator as 'cm.py error': neither stops the run or silently drops the problem."""
    import bench
    monkeypatch.setattr(bench, "DIR", str(tmp_path))
    (tmp_path / "problems").mkdir()
    monkeypatch.setenv("VAMPIRE", str(tmp_path / "no-such-vampire"))  # must be classified before Vampire runs
    for src in ("fof(a, axiom, (p <~> q)).\n", "fof(a, axiom, ![X]: (p(X) ~| q(X))).\n", "fof(a, axiom, p(\"s\")).\n"):
        (tmp_path / "problems" / "X.p").write_text(src)
        assert bench.run_hybrid("X.p")["verdict"] == "unsupported input", src
    deep = "fof(a, axiom, " + "~(" * 3000 + "p" + ")" * 3000 + ").\n"  # deeper than Python's recursion limit (KRS290-1)
    (tmp_path / "problems" / "X.p").write_text(deep)
    assert bench.run_hybrid("X.p")["verdict"] == "cm.py error"


@needs_vampire
@needs_lake
@pytest.mark.parametrize("v", ["T", "True", "False", "Nat", "Decidable"])
def test_variables_cannot_capture_lean_names(v, tmp_path):
    """A TPTP variable named like the domain type or a Lean constant must not shadow it (GEG001+1 uses `T`)."""
    p = tmp_path / f"v_{v}.p"
    p.write_text(f"fof(a, axiom, ![{v}]: ?[Y]: (r({v}, Y) & $true)).\nfof(b, axiom, ~r(c, c)).\n")
    out = tmp_path / "Out.lean"
    out.write_text(run("python3", "cm.py", str(p)).stdout)
    assert run("lake", "env", "lean", str(out)).returncode == 0


def test_include_expansion(tmp_path):
    """bench.expand: plain includes are inlined; comments and quoted names are left alone; a selective include stays
    in place and cm.py refuses it; an unresolved, nested or non-Axioms include raises. Nothing is silently dropped."""
    from bench import expand
    files = {"A.ax": "fof(ax, axiom, p(a)).\n", "N.ax": "include('Axioms/A.ax').\n"}
    def read(f):
        return files[f] if f in files else open(tmp_path / "missing" / f).read()
    assert expand("include('Axioms/A.ax').\nfof(c, conjecture, q).\n", read) == "fof(ax, axiom, p(a)).\n\nfof(c, conjecture, q).\n"
    assert expand("include( 'Axioms/A.ax' ) .\n", read) == files["A.ax"] + "\n"  # TPTP allows the spaces
    for unchanged in ("% include('Axioms/A.ax').\n",  # BOO008-3 and RNG025-9 comment their includes out
                      "/* include('Axioms/A.ax'). */\n", "fof(f, axiom, p('include(')).\n"):
        assert expand(unchanged, read) == unchanged
    selective = "include('Axioms/A.ax', [ax]).\nfof(c, conjecture, q).\n"
    assert expand(selective, read) == selective
    (p := tmp_path / "sel.p").write_text(selective)
    with pytest.raises(ValueError):
        problem(str(p))
    for bad in ("include('Axioms/Missing.ax').\n", "include('Axioms/N.ax').\n", "include('Other/A.ax').\n"):
        with pytest.raises(ValueError):
            expand(bad, read)


def test_block_comments_are_rejected(tmp_path):
    """cm.py strips `%` comments only; a `/* … */` comment is refused rather than read as formulas."""
    p = tmp_path / "t.p"
    p.write_text("/* fof(hidden, axiom, ~p(a)). */\nfof(a, axiom, p(a)).\nfof(c, conjecture, q(a)).\n")
    with pytest.raises(ValueError):
        problem(str(p))
    p.write_text("fof(a, axiom, p('/*')).\nfof(c, conjecture, q(a)).\n")  # inside a quoted name it is just a name
    assert len(problem(str(p))) == 2


def test_shallow_certificate_proves_a_nonempty_domain():
    """An inductive type with no constructors is empty, and `∀ x, False` holds over it; a first-order domain is
    nonempty. emit refuses a 0-element model, and every shallow certificate proves `Nonempty T` in its statement."""
    with pytest.raises(ValueError):
        emit("examples/group_comm.p", 0, {}, {})
    for p in EXAMPLES:
        assert "theorem countermodel : Nonempty T ∧ " in open(f"Cm/{os.path.basename(p)[:-2]}.lean").read()


@pytest.mark.skipif(not os.path.isdir("bench/sources"), reason="needs bench/sources (bench/inputs.py rebuild)")
def test_benchmark_inputs_match_their_sources():
    """Every benchmark input is its TPTP original with includes expanded by bench.expand, byte for byte, and both
    match the SHA-256s recorded in bench/inputs.json (taken from the official TPTP release)."""
    import json, hashlib
    from bench import expand
    sha = lambda b: hashlib.sha256(b).hexdigest()
    m = json.load(open("bench/inputs.json"))
    read = lambda f: open(f"bench/axioms/{f}", encoding="latin-1").read()
    for f, h in m["problems"].items():
        src = open(f"bench/sources/{f}", "rb").read()
        assert sha(src) == h["source"], f
        if h.get("expanded"):
            assert sha(open(f"bench/problems/{f}", "rb").read()) == h["expanded"] == sha(expand(src.decode("latin-1"), read).encode("latin-1")), f
    for f, h in m["axioms"].items():
        assert sha(open(f"bench/axioms/{f}", "rb").read()) == h, f


# Round-4 review: two contradictory files whose first axiom the old record regex dropped (a quoted name with a hyphen;
# a comment between `fof` and `(`). Both are legal TPTP and have no model at all.
DROPPED = ["fof('critical-axiom', axiom, p(a)).\nfof(negative, axiom, ~p(a)).\n",
           "fof % legal comment between tokens\n(critical, axiom, p(a)).\nfof(negative, axiom, ~p(a)).\n"]
RECORD_COUNTS = [  # (source, records): hand-checked
    (DROPPED[0], 2), (DROPPED[1], 2),
    ("fof ( a , axiom , p ) .\n", 1),
    ("fof(a, axiom, p, file('x.p', a)).\n", 1),  # annotations are not part of the formula
    ("fof(1, axiom, p).\nfof('thm.bool.TRUTH', axiom, q).\nfof('it\\'s', axiom, r).\n", 3),  # SWW-style names
    ("fof('50%', axiom, p % ). fof(b, axiom, q).\n   ).\n", 1),  # '%' in a name, and a comment hiding a fake record
    ("cnf(c, negated_conjecture, ~ r(X) | s(X)).\n", 1),
]
REJECTED = ["hello.\n", "fof(a, axiom).\n", "fof(a, unknown, p).\n", "tff(a, axiom, p).\n", "include('Axioms/A.ax').\n",
            "fof(a, axiom, p)\n", "fof(a, axiom, (p).\n", "fof(a, axiom, p).\n/* fof(b, axiom, q). */\n", "fof(a b, axiom, p).\n"]


@pytest.mark.parametrize("src,n", RECORD_COUNTS)
def test_every_record_is_accounted_for(src, n, tmp_path):
    """cm.statements and the oracle's own reader each find exactly the hand-counted records."""
    (p := tmp_path / "t.p").write_text(src)
    assert len(statements(str(p))) == n == len(records(src)) == len(problem(str(p)))


def test_annotations_are_not_formulas(tmp_path):
    (p := tmp_path / "t.p").write_text("fof(a, axiom, p, file('x.p', a)).\n")
    assert statements(str(p))[0]["formula"].strip() == "p" == records(p.read_text())[0][3]


@pytest.mark.parametrize("src", REJECTED)
def test_unreadable_records_are_rejected_not_skipped(src, tmp_path):
    """Text that is not a complete, supported fof/cnf record makes both readers refuse the whole file."""
    (p := tmp_path / "t.p").write_text(src)
    with pytest.raises(ValueError):
        statements(str(p))
    with pytest.raises(ValueError):
        records(src)


@needs_lake
@pytest.mark.parametrize("src", DROPPED)
def test_a_model_of_part_of_the_problem_is_rejected(src, tmp_path):
    """The reviewer's protocol: a candidate that satisfies only ~p(a). The oracle, the shallow certificate and the
    reflected certificate must all reject it, because the dropped axiom p(a) is now part of the problem."""
    (p := tmp_path / "t.p").write_text(src)
    wrong = (1, {"a": 1}, {"p": {(1,): False}})
    assert len(problem(str(p))) == 2 and not countermodel(str(p), *wrong)
    assert run("lake", "build", "Checker").returncode == 0
    assert not lean_accepts(str(p), wrong, tmp_path, emit)
    assert not lean_accepts(str(p), wrong, tmp_path, emit_reflect)


@needs_lake
def test_source_symbols_cannot_collide_with_generated_names(tmp_path):
    """Symbols named like the shallow emitter's own declarations (c0, P0, C0, chunk0, countermodel) still certify."""
    (p := tmp_path / "t.p").write_text("fof(a, axiom, c0 = countermodel).\nfof(b, axiom, p0(c0) & chunk0).\n"
                                       "fof(g, conjecture, q(countermodel)).\n")
    m = (1, {"c0": 1, "countermodel": 1, "chunk0": True}, {"p0": {(1,): True}, "q": {(1,): False}})
    assert countermodel(str(p), *m)
    assert run("lake", "build", "Checker").returncode == 0
    assert lean_accepts(str(p), m, tmp_path, emit) and lean_accepts(str(p), m, tmp_path, emit_reflect)


def test_a_failing_finder_is_not_a_search_outcome(tmp_path):
    """A finder that prints no SZS status and exits non-zero is an error: never 'no model', never cached."""
    (fake := tmp_path / "vampire").write_text("#!/bin/sh\necho 'segmentation fault' >&2\nexit 3\n")
    fake.chmod(0o755)
    (p := tmp_path / "t.p").write_text("fof(a, axiom, p(a)).\n")
    env = {**os.environ, "VAMPIRE": str(fake), "CM_CACHE": str(tmp_path / "cache")}
    out = subprocess.run(["python3", "cm.py", str(p)], env=env, capture_output=True, text=True)
    assert out.returncode != 0 and "vampire failed" in out.stderr and "no finite" not in out.stderr
    assert not (tmp_path / "cache").exists() or not os.listdir(tmp_path / "cache")


def test_benchmark_reports_a_failing_finder_as_finder_error(tmp_path, monkeypatch):
    """The benchmark's classification of the same failure: 'finder error', neither 'no model' nor a crash."""
    import bench
    monkeypatch.setattr(bench, "DIR", str(tmp_path))
    (tmp_path / "problems").mkdir()
    (fake := tmp_path / "vampire").write_text("#!/bin/sh\necho 'segmentation fault' >&2\nexit 3\n")
    fake.chmod(0o755)
    monkeypatch.setenv("VAMPIRE", str(fake))
    (tmp_path / "problems" / "X.p").write_text("fof(a, axiom, p(a)).\nfof(b, axiom, ~q(a)).\n")
    r = bench.run_hybrid("X.p")
    assert r["verdict"] == "finder error" and "vampire failed" in r["why"], r


def test_a_timeout_is_a_search_outcome_not_a_failure(tmp_path, monkeypatch):
    """Vampire 5.1 reports a timeout as 'Termination reason: Time limit', exit 1, no SZS status (observed on
    SWV495-1.040): the benchmark records 'no model', and the timeout is not cached."""
    import bench
    monkeypatch.setattr(bench, "DIR", str(tmp_path))
    (tmp_path / "problems").mkdir()
    (fake := tmp_path / "vampire").write_text("#!/bin/sh\nprintf '%% Termination reason: Time limit\\n%% Time elapsed: 30.0 s\\n'\nexit 1\n")
    fake.chmod(0o755)
    monkeypatch.setenv("VAMPIRE", str(fake))
    monkeypatch.setenv("CM_CACHE", str(tmp_path / "cache"))
    (tmp_path / "problems" / "X.p").write_text("fof(a, axiom, p(a)).\nfof(b, axiom, ~q(a)).\n")
    r = bench.run_hybrid("X.p")
    assert r["verdict"] == "no model" and "Time limit" in r["why"], r
    assert not (tmp_path / "cache").exists() or not os.listdir(tmp_path / "cache")


def test_fidelity_check_flags_a_model_of_part_of_the_problem(tmp_path, monkeypatch):
    """bench/fidelity.py must call the reviewer's wrong model NOT FAITHFUL: it reads the whole original file."""
    import sys, cm
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "bench"))
    from fidelity import check
    (p := tmp_path / "t.p").write_text(DROPPED[0])
    monkeypatch.setattr(cm, "model", lambda path: (1, {"a": 1}, {"p": {(1,): False}}))
    assert check(str(p))[0].startswith("NOT FAITHFUL")


# Round-4 review: bounded validation of the rewrite on adversarial forms. Every interpretation of the signature
# (constants a, b; unary p, q; binary r) on domains of size 1 and 2: 8 + 1,024 structures per formula. Original
# (read by the oracle) and rewritten (problem()) must agree on every one. Bounded validation, not a general proof.
ADVERSARIAL = [("fof", f) for f in [
    "![X,Y]: (p(X) | q(Y))",                        # independent variables: scope splits
    "![X]: (p(X) | ![X]: q(X))",                    # a repeated (shadowed) variable name
    "![X,Y]: (p(X) | r(X,Y))",                      # ∀ moved across ∨
    "![X]: (p(X) => ![Y]: (q(Y) => r(X,Y)))",       # implication flattening
    "![X]: (p(a) | q(a))",                          # vacuous quantification
    "![X]: (p(X) | ?[Y]: r(X,Y))",                  # ∃ under ∀
    "![X,Y]: (r(X,Y) | r(Y,X) | X = Y)",            # equality
    "![X]: ~ (p(X) & ~ q(X))",                      # negated conjunction
    "![X]: (p(X) <=> q(X))",                        # equivalence: must not be flattened
    "![X,Y]: ((p(X) & q(Y)) => r(X,Y))",
    "![X]: (![Y]: r(X,Y) | p(X))",                  # a quantified first literal
    "![X,Y,Z]: (~ r(X,Y) | ~ r(Y,Z) | r(X,Z))",
    "![X]: (p(X) | ![Y]: (q(Y) | r(Y,X)))",
    "?[X]: (p(X) | q(X))",
    "![X]: (p(X) | p(X))",
]] + [("cnf", f) for f in ["~ r(X,Y) | ~ r(Y,Z) | r(X,Z)", "p(X) | q(Y)", "X = a | r(X,X)"]]


def small_structures():
    for n in (1, 2):
        E = range(1, n + 1)
        tuples1, tuples2 = [(x,) for x in E], list(itertools.product(E, repeat=2))
        for a, b in itertools.product(E, repeat=2):
            for pv in itertools.product((False, True), repeat=n):
                for qv in itertools.product((False, True), repeat=n):
                    for rv in itertools.product((False, True), repeat=n * n):
                        yield n, {"a": a, "b": b}, {"p": dict(zip(tuples1, pv)), "q": dict(zip(tuples1, qv)), "r": dict(zip(tuples2, rv))}


@pytest.mark.parametrize("kind,f", ADVERSARIAL)
def test_rewriting_is_equivalent_on_every_small_structure(kind, f, tmp_path):
    (p := tmp_path / "t.p").write_text(f"{kind}(f, axiom, {f}).\n")
    (_, original), = raw(str(p))
    (_, rewritten), = problem(str(p))
    checked = 0
    for n, consts, tables in small_structures():
        assert holds(original, n, consts, tables) == holds(rewritten, n, consts, tables), (f, rewritten, n, consts, tables)
        checked += 1
    assert checked == 8 + 1024


def clause_holds(clause, n, consts, tables):
    """A cnf clause ∀X̄ (L1 | … | Lk), evaluated by searching for a falsifying assignment instead of enumerating all
    n^|X̄| of them: bind the variables of one literal at a time, keep only bindings that make that literal false, and
    succeed (clause false) when every literal is false. Independent of cm.py (the oracle's own lexer and variable
    detection), and validated against holds() by test_clause_search_agrees_with_brute_force."""
    toks = [m[0] for m in ORACLE_LEX.finditer(clause) if m.lastgroup not in ("ws", "comment")]
    lits, cur, depth = [], [], 0
    for t in toks:  # split at top-level '|'
        depth += t in "([" and len(t) == 1
        depth -= t in ")]" and len(t) == 1
        if t == "|" and depth == 0:
            lits.append(cur)
            cur = []
        else:
            cur.append(t)
    lits.append(cur)
    var = lambda t: t[0].isupper() and t[0] != "'"
    lits = [(" ".join(l), sorted({t for t in l if var(t)})) for l in lits]

    def falsify(rest, env):  # is there an extension of env making every literal in rest false?
        if not rest:
            return True
        # the literal with the fewest unbound variables first: most pruning
        i = min(range(len(rest)), key=lambda j: len([v for v in rest[j][1] if v not in env]))
        text, vs = rest[i]
        free = [v for v in vs if v not in env]
        for vals in itertools.product(range(1, n + 1), repeat=len(free)):
            e = {**env, **dict(zip(free, vals))}
            if not holds(text, n, consts, tables, e) and falsify(rest[:i] + rest[i + 1:], e):
                return True
        return False

    return not falsify(lits, {})


def test_clause_search_agrees_with_brute_force():
    """clause_holds and holds agree on every adversarial cnf clause, and on clauses with repeated and unused variables,
    over all 1,032 small structures."""
    clauses = [f for k, f in ADVERSARIAL if k == "cnf"] + ["~ p(X) | q(X) | r(X,Y)", "p(a) | ~ q(b)", "r(X,X) | ~ r(Y,Y) | X = Y"]
    for c in clauses:
        closed = f"![{','.join(sorted(VARS(c)))}]: ({c})" if VARS(c) else c
        for n, consts, tables in small_structures():
            assert clause_holds(c, n, consts, tables) == holds(closed, n, consts, tables), (c, n, consts, tables)
