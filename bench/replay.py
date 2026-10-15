"""Fresh kernel replay of every strictly certified benchmark certificate (whitepaper §6.2): the certificates bench.py
wrote in bench/lean are recompiled as modules under bench/replay, every `countermodel` theorem's axioms are printed,
and one aggregate module per set is replayed from scratch by `leanchecker --fresh`, imports included.

Usage, in the frozen worktree after bench/frozen.py:  python3 bench/replay.py OUT
Reads OUT/results-final-<set>.jsonl; writes OUT/replay-<set>.jsonl (one record per certificate) and OUT/replay.log."""
import json, os, re, shutil, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

B = os.path.dirname(os.path.abspath(__file__))
R = f"{B}/replay"
OUT = sys.argv[1]
PATH = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], capture_output=True, text=True).stdout.strip()
ENV = {**os.environ, "LEAN_PATH": f"{PATH}:{R}"}
log = open(f"{OUT}/replay.log", "w")


def sh(args, timeout=3600):
    """(ok, output, seconds) of one Lean process."""
    t = time.time()
    p = subprocess.run(args, capture_output=True, text=True, env=ENV, timeout=timeout)
    return p.returncode == 0, (p.stdout + p.stderr).strip(), round(time.time() - t, 1)


def compile_(mod):
    """R/<mod path>.lean -> .olean, with R as the root so the module is named `mod`."""
    f = f"{R}/{mod.replace('.', '/')}"
    return sh(["lake", "env", "lean", f"--root={R}", "-o", f + ".olean", f + ".lean"])


def certificate(r):
    """The certificate of one result as modules under R; returns (namespace, top module, ok, seconds)."""
    f = r["problem"]
    ns = re.sub(r"\W", "_", f[:-2])  # cm.py's namespace for the problem
    if r["method"] == "shallow":
        shutil.copy(f"{B}/lean/{f[:-2].replace('-', '_').replace('.', '_')}.decide.lean", f"{R}/{ns}.lean")
        ok, out, s = compile_(ns)
        return ns, ns, ok, s
    src = f"{B}/lean/{ns}"
    if not os.path.exists(f"{src}/Base.lean"):  # one reflected file
        shutil.copy(f"{src}/Main.lean", f"{R}/{ns}.lean")
        ok, out, s = compile_(ns)
        return ns, ns, ok, s
    shutil.copytree(src, f"{R}/{ns}", dirs_exist_ok=True)  # modules: Base, parts in parallel, Main
    t = time.time()
    parts = sorted((m[:-5] for m in os.listdir(f"{R}/{ns}") if m.startswith("Part")), key=lambda m: int(m[4:]))
    ok = compile_(f"{ns}.Base")[0]
    if ok:
        with ThreadPoolExecutor(4) as pool:
            ok = all(o for o, _, _ in pool.map(lambda m: compile_(f"{ns}.{m}"), parts))
    ok = ok and compile_(f"{ns}.Main")[0]
    return ns, f"{ns}.Main", ok, round(time.time() - t, 1)


if __name__ == "__main__":
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()
    shutil.rmtree(R, ignore_errors=True)
    os.makedirs(R)
    for name in sorted(n[len("results-final-"):-6] for n in os.listdir(OUT) if n.startswith("results-final-")):
        rs = [json.loads(l) for l in open(f"{OUT}/results-final-{name}.jsonl")]
        rs = [r for r in rs if r["verdict"] == "certified"]  # each record keeps the commit it ran at
        recs = []
        for r in rs:
            ns, mod, ok, s = certificate(r)
            recs.append({"problem": r["problem"], "method": r["method"], "run_commit": r.get("commit"), "module": mod, "compiled": ok, "compile_s": s})
            print(name, r["problem"], "compiled" if ok else "COMPILE FAILED", s, file=log, flush=True)
        agg = "Replay_" + re.sub(r"\W", "_", name)
        good = [c for c in recs if c["compiled"]]
        open(f"{R}/{agg}.lean", "w").write("".join(f"import {c['module']}\n" for c in good) + "".join(
            f"#print axioms {re.sub(r'[^A-Za-z0-9_]', '_', c['problem'][:-2])}.countermodel\n" for c in good))
        ok, out, s = compile_(agg)
        axioms = dict(re.findall(r"'([\w.]+)\.countermodel' depends on axioms: \[([^\]]*)\]", out))
        axioms |= {ns: "" for ns in re.findall(r"'([\w.]+)\.countermodel' does not depend on any axioms", out)}  # none at all
        print(f"== axioms {name}\n{out}", file=log, flush=True)
        fok, fout, fs = sh(["lake", "env", "leanchecker", "--fresh", agg], timeout=4 * 3600)
        print(f"== leanchecker --fresh {agg}: {'ok' if fok else 'FAILED'} in {fs} s\n{fout}", file=log, flush=True)
        for c in recs:
            ns = re.sub(r"[^A-Za-z0-9_]", "_", c["problem"][:-2])
            c.update(commit=commit, axioms=[a for a in axioms[ns].replace(" ", "").split(",") if a] if ns in axioms else None,
                     fresh=fok and c["compiled"], fresh_module=agg, fresh_s=fs)
        open(f"{OUT}/replay-{name}.jsonl", "w").write("".join(json.dumps(c) + "\n" for c in recs))
        bad = [c["problem"] for c in recs if not c["fresh"] or c["axioms"] is None
               or any(a not in ("propext", "Quot.sound", "Classical.choice") for a in c["axioms"])]
        print(name, f"{len(recs)} strict certificates; aggregate compiled in {s} s; leanchecker --fresh "
              f"{'ok' if fok else 'FAILED'} in {fs} s; outside standard axioms or not replayed: {bad}", flush=True)
