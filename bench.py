"""Benchmark on TPTP problems with a model (status SAT or CSA, from bench/eligible.tsv), in fof or cnf.
Usage: python3 bench.py N [WORKERS]   -> fetch and run N more problems, append to bench/results.jsonl"""
import html, json, os, queue, random, re, subprocess, sys, threading, time, urllib.request
from concurrent.futures import ThreadPoolExecutor
from cm import QUOTED, VARS, lean as translate, problem

SEE, DIR = "https://tptp.org/cgi-bin/SeeTPTP?Category=", "bench"


def get(q, tries=4):
    """A TPTP page as text; polite (0.5 s apart) and retried, since the server sometimes times out."""
    for k in range(tries):
        try:
            time.sleep(0.5 * 4 ** k)
            return html.unescape(re.sub(r"<[^>]*>", "", urllib.request.urlopen(SEE + q, timeout=30).read().decode("latin-1")))
        except OSError:
            if k == tries - 1:
                raise


INCLUDE = rf"({QUOTED})|%.*|/\*[\s\S]*?\*/|include\(\s*'([^']*)'\s*(,[^)]*)?\)\s*\."


def expand(src, read):
    """src with each plain `include('Axioms/F').` replaced by read(F), so the problem is self-contained.
    Quoted names and comments are never read as includes. A selective include (`include('Axioms/F', [names]).`) is
    left in place, so cm.py refuses the problem as unsupported input. A path outside Axioms/, a missing file or an
    included file that itself includes raises ValueError: the problem is never certified as a shortened problem."""
    def one(m):
        if m[2] is None or m[3]:  # a quoted name, a comment or a selective include: unchanged
            return m[0]
        if not m[2].startswith("Axioms/") or "/" in m[2][7:]:
            raise ValueError(f"unsupported TPTP: include of {m[2]!r}, outside Axioms/")
        try:
            text = read(m[2][7:])
        except OSError:
            raise ValueError(f"unsupported TPTP: unresolved include {m[2]!r}")
        if any(n[2] is not None for n in re.finditer(INCLUDE, text)):
            raise ValueError(f"unsupported TPTP: nested include in {m[2]!r}")
        return text
    return re.sub(INCLUDE, one, src)


def source(category, f):
    """A TPTP file exactly as distributed: from a local copy of the TPTP release in $TPTP if set, else the web page."""
    if root := os.getenv("TPTP"):
        return open(f"{root}/{category}/{f[:3] + '/' if category == 'Problems' else ''}{f}", encoding="latin-1").read()
    src = get(f"{category}&Domain={f[:3]}&File={f}" if category == "Problems" else f"{category}&File={f}")
    return src[src.index("%-----"):]


def fetch(name):
    """A problem with its includes inlined, so it is self-contained. The original is kept in bench/sources/."""
    src = source("Problems", name)
    open(f"{DIR}/sources/{name}", "w", encoding="latin-1").write(src)
    return expand(src, axioms)


def axioms(f):
    """An axiom file, fetched once: many problems share the same axiom sets."""
    if not os.path.exists(path := f"{DIR}/axioms/{f}"):
        open(path, "w", encoding="latin-1").write(source("Axioms", f))
    return open(path, encoding="latin-1").read()


def pick(n, seen):
    """n problems not yet run, sampled from the TPTP status index: no rejected downloads."""
    names = [l.split("\t")[0] + ".p" for l in open(f"{DIR}/eligible.tsv")]
    return random.Random(len(seen)).sample([f for f in names if f not in seen], n)


def run(f):
    p, t = f"{DIR}/problems/{f}", time.time()
    cm = subprocess.run(["python3", "-X", "int_max_str_digits=0", "cm.py", p], capture_output=True, text=True,
                        env={"CM_CACHE": f"{DIR}/vampire-cache", **os.environ})  # Vampire's answers are reused across Lean versions
    r = {"problem": f, "lang": "cnf" if "-" in f else "fof", "cm_s": round(time.time() - t, 1)}
    if cm.returncode:
        return {**r, "verdict": "no model" if "no finite" in cm.stderr else "unsupported input" if "unsupported TPTP" in cm.stderr
                else "finder error" if "vampire failed" in cm.stderr else "cm.py error", "why": cm.stderr.strip()[-300:]}
    r["size"] = int(re.search(r"a (\d+)-element", cm.stdout)[1])
    r["work"] = max(r["size"] ** len(set(re.findall(r"\b[A-Z]\w*", f))) for _, f in problem(p))  # decide's cases, worst formula
    stem = f"{DIR}/lean/{f[:-2].replace('-', '_').replace('.', '_')}"
    for tactic in ("decide", "native_decide"):  # kernel only; then also trusting Lean's compiler
        open(lf := f"{stem}.{tactic}.lean", "w").write(cm.stdout.replace(":= by decide\n", f":= by {tactic}\n"))
        t, lean = time.time(), subprocess.Popen(["lake", "env", "lean", lf], stdout=subprocess.PIPE, text=True, start_new_session=True)
        try:
            out = lean.communicate(timeout=60)[0]
            ok, why = lean.returncode == 0, out.strip()[:300]
        except subprocess.TimeoutExpired:  # kill lake *and* the lean process under it
            os.killpg(lean.pid, 9)
            ok, why = False, "lean timeout (60 s)"
        r[f"{tactic}_s"] = round(time.time() - t, 1)
        if ok:
            return {**r, "verdict": "certified" if tactic == "decide" else "certified (native)", "why": ""}
        if "timeout" not in why:  # fail fast: native_decide is only faster, so it can't fix an error
            break
    return {**r, "verdict": "lean rejected", "why": why}


def lean(args, timeout, env=None):
    """(ok, output) of one Lean process; on timeout, kill lake *and* the lean process under it."""
    proc = subprocess.Popen(args, stdout=subprocess.PIPE, text=True, start_new_session=True, env=env)
    try:
        out = proc.communicate(timeout=timeout)[0]
        return proc.returncode == 0, out.strip()[:300]
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, 9)
        return False, f"lean timeout ({timeout} s)"


def run_reflect(f):
    """Certify through the verified checker (Checker.lean): one kernel-only attempt, modules for large problems."""
    p, t = f"{DIR}/problems/{f}", time.time()
    stem, ns = f"{DIR}/lean/{f[:-2].replace('-', '_').replace('.', '_')}", re.sub(r"\W", "_", f[:-2])
    cm = subprocess.run(["python3", "-X", "int_max_str_digits=0", "cm.py", "--reflect", p, f"{DIR}/lean"],
                        capture_output=True, text=True, env={"CM_CACHE": f"{DIR}/vampire-cache", **os.environ})
    r = {"problem": f, "lang": "cnf" if "-" in f else "fof", "cm_s": round(time.time() - t, 1), "method": "reflect"}
    if cm.returncode:
        return {**r, "verdict": "no model" if "no finite" in cm.stderr else "unsupported input" if "unsupported TPTP" in cm.stderr
                else "finder error" if "vampire failed" in cm.stderr else "cm.py error", "why": cm.stderr.strip()[-300:]}
    d = f"{DIR}/lean/{ns}"
    first = open(f"{d}/{'Base' if os.path.exists(d + '/Base.lean') else 'Main'}.lean").readline()
    r["size"] = int(re.search(r"a (\d+)-element", first)[1])
    t = time.time()
    if not os.path.exists(d + "/Base.lean"):  # one file
        ok, why = lean(["lake", "env", "lean", f"{d}/Main.lean"], 60)
    else:  # modules: Base, then the parts in parallel, then Main
        path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], capture_output=True, text=True).stdout.strip()
        env = {**os.environ, "LEAN_PATH": f"{path}:{DIR}/olean"}
        os.makedirs(f"{DIR}/olean/{ns}", exist_ok=True)
        build = lambda m: lean(["lake", "env", "lean", "-o", f"{DIR}/olean/{ns}/{m}.olean", f"{d}/{m}.lean"], 600, env)
        parts = sorted((m[:-5] for m in os.listdir(d) if m.startswith("Part")), key=lambda m: int(m[4:]))
        ok, why = build("Base")
        if ok:
            with ThreadPoolExecutor(4) as pool:
                bad = [w for o, w in pool.map(build, parts) if not o]
            ok, why = (False, bad[0]) if bad else build("Main")
    r["reflect_s"] = round(time.time() - t, 1)
    return {**r, "verdict": "certified" if ok else "lean rejected", "why": "" if ok else why}


def fact_share(p):
    """The share of formulas that are ground literals: the checker's strong case."""
    fs = problem(p)
    lit = re.compile(r"^\(*\s*(~)?\s*\(*\s*([\w']+|'[^']*')\s*(\([^()]*\))?\s*\)*\s*$")
    return sum(not VARS(f) and bool(lit.match(f.strip())) for _, f in fs) / max(len(fs), 1)


def run_hybrid(f, threshold=0.9):
    """Reflection for fact-heavy problems; one theorem per formula (shallow decide) for the rest. Inputs cm.py refuses
    (unsupported TPTP features) are recorded as such and stay in the denominator."""
    try:  # translate every formula first, so unsupported syntax is classified before Vampire runs, not after
        for _, g in problem(f"{DIR}/problems/{f}"):
            translate(g)
        share = fact_share(f"{DIR}/problems/{f}")
    except ValueError as e:
        return {"problem": f, "verdict": "unsupported input", "why": str(e)[:300], "method": "-"}
    except Exception as e:  # e.g. RecursionError on deep nesting: recorded as a failure, never allowed to stop the run
        return {"problem": f, "verdict": "cm.py error", "why": f"{type(e).__name__} in the translator: {str(e)[:200]}", "method": "-"}
    r = run_reflect(f) if share >= threshold else run(f)
    return {**r, "method": "reflect" if share >= threshold else "shallow", "fact_share": round(share, 3)}


if __name__ == "__main__":
    for d in ("problems", "sources", "lean", "axioms"):
        os.makedirs(f"{DIR}/{d}", exist_ok=True)
    log, n, workers = f"{DIR}/results.jsonl", int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 2
    seen = [json.loads(l)["problem"] for l in open(log)] if os.path.exists(log) else []
    todo, lock = queue.Queue(maxsize=workers), threading.Lock()

    def produce():  # network-bound: download while the workers compute
        try:
            for f in pick(n, seen):
                try:
                    if not os.path.exists(path := f"{DIR}/problems/{f}"):
                        open(path, "w").write(fetch(f))
                    todo.put(f)
                except Exception as e:  # one bad download is recorded, not fatal
                    with lock:
                        open(log, "a").write(json.dumps({"problem": f, "verdict": "fetch error", "why": repr(e)[:300]}) + "\n")
        finally:  # always release the workers, or they wait forever
            for _ in range(workers):
                todo.put(None)

    def consume():  # CPU-bound: Vampire, cm.py and Lean
        while (f := todo.get()) is not None:
            r = run(f)
            with lock:
                open(log, "a").write(json.dumps(r) + "\n")
                print(f"{r['problem']:<18} {r['verdict']:<20} size={r.get('size', '-'):<4} {r['why'][:70]}", flush=True)

    t = time.time()
    threading.Thread(target=produce, daemon=True).start()
    with ThreadPoolExecutor(workers) as pool:
        list(pool.map(lambda _: consume(), range(workers)))
    print(f"{n} problems in {time.time() - t:.0f} s with {workers} workers")
