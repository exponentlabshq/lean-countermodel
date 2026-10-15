"""Benchmark on TPTP problems with a model (status SAT or CSA, from bench/eligible.tsv), in fof or cnf.
Usage: python3 bench.py N [WORKERS]   -> fetch and run N more problems, append to bench/results.jsonl"""
import html, json, os, queue, random, re, subprocess, sys, threading, time, urllib.request
from concurrent.futures import ThreadPoolExecutor
from cm import problem

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


def fetch(name):
    """A problem with its includes inlined, so it is self-contained."""
    src = get(f"Problems&Domain={name[:3]}&File={name}")
    return re.sub(r"include\('Axioms/([^']+)'\)\.", lambda m: axioms(m[1]), src[src.index("%-----"):])


def axioms(f):
    """An axiom file, downloaded once: many problems share the same axiom sets."""
    if not os.path.exists(path := f"{DIR}/axioms/{f}"):
        src = get(f"Axioms&File={f}")
        open(path, "w").write(src[src.index("%-----"):])
    return open(path).read()


def pick(n, seen):
    """n problems not yet run, sampled from the TPTP status index: no rejected downloads."""
    names = [l.split("\t")[0] + ".p" for l in open(f"{DIR}/eligible.tsv")]
    return random.Random(len(seen)).sample([f for f in names if f not in seen], n)


def run(f):
    p, t = f"{DIR}/problems/{f}", time.time()
    cm = subprocess.run(["python3", "cm.py", p], capture_output=True, text=True,
                        env={"CM_CACHE": f"{DIR}/vampire-cache", **os.environ})  # Vampire's answers are reused across Lean versions
    r = {"problem": f, "lang": "cnf" if "-" in f else "fof", "cm_s": round(time.time() - t, 1)}
    if cm.returncode:
        return {**r, "verdict": "no model" if "no finite" in cm.stderr else "cm.py error", "why": cm.stderr.strip()[-300:]}
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


if __name__ == "__main__":
    for d in ("problems", "lean", "axioms"):
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
