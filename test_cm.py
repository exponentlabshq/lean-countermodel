"""Is cm.py sound, faithful and general? Lean, an independent Python evaluator and known answers must agree."""
import glob, itertools, os, random, re, shutil, subprocess, pytest
from functools import cache
from concurrent.futures import ThreadPoolExecutor
from cm import TOKENS, VARS, emit, emit_reflect, model, problem, uncomment

pytestmark = pytest.mark.skipif(not shutil.which(os.getenv("VAMPIRE", "vampire")) or not shutil.which("lake"),
                                reason="needs vampire and lake")
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


def countermodel(path, n, consts, tables):
    """Python's verdict: every axiom holds and the conjecture fails."""
    return all(holds(f, n, consts, tables) != (r == "conjecture") for r, f in problem(path))


def lean_accepts(path, m, tmp, emitter=emit):
    file = tmp / f"{os.path.basename(path)[:-2]}_{emitter.__name__}_{id(m)}.lean"
    file.write_text(emitter(path, *m))
    return run("lake", "env", "lean", str(file)).returncode == 0


M = cache(model)


@pytest.mark.parametrize("p", EXAMPLES)
def test_compiles_to_committed_file(p):
    assert run("python3", "cm.py", p).stdout == open(f"Cm/{os.path.basename(p)[:-2]}.lean").read()


def test_kernel_accepts_with_propext_only():
    assert run("lake", "build").returncode == 0
    out = run("lake", "env", "lean", "Axioms.lean").stdout.splitlines()
    assert len(out) == len(EXAMPLES) and all(l.endswith("[propext]") for l in out)


@pytest.mark.parametrize("p", EXAMPLES)
def test_python_agrees_it_is_a_countermodel(p):
    assert countermodel(p, *M(p))


def test_circle_of_fifths_is_the_known_answer():
    """Minimal model: exactly 12 notes, and up-a-fifth is x -> x+7 (mod 12) under C=0, up-a-fourth its inverse."""
    n, consts, t = M("examples/circle_of_fifths.p")
    note, x = {}, consts["c"]
    for k in range(12):
        note[x], x = 7 * k % 12, t["f"][(x,)]
    assert n == 12 and len(set(note.values())) == 12
    assert all(note[t["f"][(y,)]] == (note[y] + 7) % 12 and note[t["g"][(y,)]] == (note[y] + 5) % 12 for y in note)


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


def test_a_theorem_has_no_counter_model(tmp_path):
    (tmp_path / "t.p").write_text("fof(a, axiom, ![X]: p(X)).\nfof(c, conjecture, p(k)).\n")
    assert run("python3", "cm.py", str(tmp_path / "t.p")).returncode != 0


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


def test_constants_split_into_name_modules(tmp_path):
    """Constants go in their own modules (Names*), so no file passes Lean's ~20,000-declaration limit."""
    (tmp_path / "lean-toolchain").write_text(open("lean-toolchain").read())
    (tmp_path / "lakefile.toml").write_text('name = "t"\ndefaultTargets = ["quoted_capture"]\n\n[[lean_lib]]\nname = "quoted_capture"\nglobs = ["quoted_capture.+"]\n')
    out = subprocess.run(["python3", os.path.abspath("cm.py"), os.path.abspath("examples/quoted_capture.p"), str(tmp_path)],
                         env={**os.environ, "CM_CHUNK": "1"}, capture_output=True, text=True).stdout
    assert (tmp_path / "quoted_capture" / "Names0.lean").exists() and "Lean modules" in out
    assert subprocess.run(["lake", "build"], cwd=tmp_path, capture_output=True).returncode == 0


def test_vampire_cache_is_transparent(tmp_path):
    """With CM_CACHE set, the second run reads Vampire's answer from the cache and emits the same Lean."""
    env = {**os.environ, "CM_CACHE": str(tmp_path)}
    first = subprocess.run(["python3", "cm.py", "examples/group_comm.p"], env=env, capture_output=True, text=True).stdout
    assert len(os.listdir(tmp_path)) == 1
    second = subprocess.run(["python3", "cm.py", "examples/group_comm.p"], env=env, capture_output=True, text=True).stdout
    assert first == second == open("Cm/group_comm.lean").read()


@pytest.mark.parametrize("p", EXAMPLES)
def test_reflected_certificate(p, tmp_path):
    """The same model, certified through the verified evaluator (Checker.lean) instead of one decide per formula."""
    assert run("lake", "build", "Checker").returncode == 0
    assert lean_accepts(p, M(p), tmp_path, emit_reflect)


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
