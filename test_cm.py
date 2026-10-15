"""Is cm.py sound, faithful and general? Lean, an independent Python evaluator and known answers must agree."""
import glob, itertools, os, random, re, shutil, subprocess, pytest
from functools import cache
from concurrent.futures import ThreadPoolExecutor
from cm import TOKENS, VARS, emit, model, problem

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
        k, args = k.strip("'"), []
        if peek("("):
            nxt()
            args.append(term(nxt()))
            while nxt() == ",":
                args.append(term(nxt()))
        if k[0].isupper():
            return lambda v: v[k]
        return lambda v: tables[k][tuple(a(v) for a in args)] if args else consts[k]

    return form()(env)


def countermodel(path, n, consts, tables):
    """Python's verdict: every axiom holds and the conjecture fails."""
    return all(holds(f, n, consts, tables) != (r == "conjecture") for r, f in problem(path))


def lean_accepts(path, m, tmp):
    file = tmp / f"{os.path.basename(path)[:-2]}_{id(m)}.lean"
    file.write_text(emit(path, *m))
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
    raw = re.findall(r"(fof|cnf)\(\s*[\w']+\s*,\s*\w+\s*,(.*?)\)\s*\.(?=\s*(?:fof|cnf)\(|\s*$)", re.sub(r"%.*", "", open(p).read()), re.S)
    raw = [f"![{','.join(sorted(VARS(f)))}]: ({f})" if k == "cnf" and VARS(f) else f for k, f in raw]
    other = lambda v: not v if isinstance(v, bool) else v % n + 1
    models = [tables] + [{**tables, f: {**t, a: other(v)}} for f, t in tables.items() for a, v in t.items()]
    for f, (_, g) in zip(raw, problem(p)):
        assert all(holds(f, n, consts, m) == holds(g, n, consts, m) for m in models)
