"""Is cm.py sound, faithful and general? Lean, an independent Python evaluator and known answers must agree."""
import glob, itertools, os, random, re, shutil, subprocess, pytest
from functools import cache
from concurrent.futures import ThreadPoolExecutor
from cm import TOKENS, VARS, emit, emit_reflect, model, problem, uncomment

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

    return form()(env)


def raw(path):
    """[(role, formula)] read straight from the source, without cm.py's rewriting; cnf clauses closed by ∀."""
    src = uncomment(open(path).read())
    fs = re.findall(r"(fof|cnf)\(\s*[\w']+\s*,\s*(\w+)\s*,(.*?)\)\s*\.(?=\s*(?:fof|cnf)\(|\s*$)", src, re.S)
    return [(r, f"![{','.join(sorted(VARS(f)))}]: ({f})" if k == "cnf" and VARS(f) else f) for k, r, f in fs]


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
    raw = re.findall(r"(fof|cnf)\(\s*[\w']+\s*,\s*\w+\s*,(.*?)\)\s*\.(?=\s*(?:fof|cnf)\(|\s*$)", uncomment(open(p).read()), re.S)
    raw = [f"![{','.join(sorted(VARS(f)))}]: ({f})" if k == "cnf" and VARS(f) else f for k, f in raw]
    other = lambda v: not v if isinstance(v, bool) else v % n + 1
    models = [tables] + [{**tables, f: {**t, a: other(v)}} for f, t in tables.items() for a, v in t.items()]
    for f, (_, g) in zip(raw, problem(p)):
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
