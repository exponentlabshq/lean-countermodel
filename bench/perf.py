"""Controlled performance comparison: shallow vs reflected certificates, same Lean, same workers, clean builds.

Usage: python3 bench/perf.py PROBLEM.p REPS [WORKERS]   -> appends one JSON line per run to bench/perf.jsonl

Definitions (also written into each record):
- wall: elapsed time of the whole run: generating Lean (models from the Vampire cache), compiling every module in
  dependency order (Base, Names*, then Chunk*/Part* in parallel, then Main), and the final `#print axioms` check.
- cpu: user + system time summed over every process the run started.
- peak_rss_process: the largest single process's maximum resident set size.
- peak_rss_aggregate: the largest total resident set size of concurrently running Lean processes, sampled every 0.2 s.
Run on a quiet machine: other load inflates wall time."""
import json, os, platform, re, resource, shutil, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def machine():
    sh = lambda *a: subprocess.run(a, capture_output=True, text=True).stdout.strip()
    return {"cpu": sh("sysctl", "-n", "machdep.cpu.brand_string") or platform.processor(),
            "cores": os.cpu_count(), "memory_gb": round(int(sh("sysctl", "-n", "hw.memsize") or 0) / 2**30),
            "os": f"{platform.system()} {platform.mac_ver()[0] or platform.release()}",
            "lean": sh("lake", "env", "lean", "--version"), "vampire": sh(os.getenv("VAMPIRE", "vampire"), "--version").split("\n")[0],
            "commit": sh("git", "-C", ROOT, "rev-parse", "--short", "HEAD")}


class Sampler(threading.Thread):
    """Samples the summed RSS of running lean processes, for the aggregate peak."""
    def __init__(self):
        super().__init__(daemon=True)
        self.peak, self.stop = 0, False

    def run(self):
        while not self.stop:
            out = subprocess.run(["ps", "-axo", "rss=,comm="], capture_output=True, text=True).stdout
            total = sum(int(l.split()[0]) * 1024 for l in out.splitlines() if l.strip().endswith("lean"))
            self.peak = max(self.peak, total)
            time.sleep(0.2)


def run(problem, method, workers):
    work = tempfile.mkdtemp(prefix=f"perf-{method}-")
    env = {**os.environ, "CM_CACHE": os.path.join(ROOT, "bench", "vampire-cache")}
    t0, ru0 = time.time(), resource.getrusage(resource.RUSAGE_CHILDREN)
    sampler = Sampler(); sampler.start()
    args = ["python3", "-X", "int_max_str_digits=0", os.path.join(ROOT, "cm.py")] + (["--reflect"] if method == "reflected" else [])
    gen = subprocess.run(args + [problem, work], capture_output=True, text=True, env=env)
    assert gen.returncode == 0, gen.stderr[-500:]
    ns = os.listdir(work)[0]
    mods = sorted(f[:-5] for f in os.listdir(os.path.join(work, ns)))
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], capture_output=True, text=True, cwd=ROOT).stdout.strip()
    lean_bin = subprocess.run(["lake", "env", "which", "lean"], capture_output=True, text=True, cwd=ROOT).stdout.strip()
    lenv = {**os.environ, "LEAN_PATH": f"{lean_path}:{work}/build"}
    os.makedirs(f"{work}/build/{ns}", exist_ok=True)
    peak_proc = [0]

    def build(m):
        p = subprocess.run(["/usr/bin/time", "-l", lean_bin, "-o", f"{work}/build/{ns}/{m}.olean", f"{work}/{ns}/{m}.lean"],
                           capture_output=True, text=True, env=lenv, cwd=work)
        rss = re.search(r"(\d+)\s+maximum resident set size", p.stderr)
        peak_proc[0] = max(peak_proc[0], int(rss[1]) if rss else 0)
        return p.returncode == 0

    stage = lambda pre: [m for m in mods if m.startswith(pre)]
    ok = all(map(build, stage("Base")))
    with ThreadPoolExecutor(workers) as pool:
        ok = ok and all(pool.map(build, stage("Names")))
        ok = ok and all(pool.map(build, stage("Chunk") + stage("Part")))
    ok = ok and build("Main")
    open(f"{work}/ax.lean", "w").write(f"import {ns}.Main\n#print axioms {ns}.countermodel\n")
    ax = subprocess.run([lean_bin, f"{work}/ax.lean"], capture_output=True, text=True, env=lenv, cwd=work).stdout.strip()
    sampler.stop = True; sampler.join()
    ru1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    shutil.rmtree(work)
    return {"problem": os.path.basename(problem), "method": method, "workers": workers, "ok": ok, "axioms": ax,
            "modules": len(mods), "wall_s": round(time.time() - t0, 1),
            "cpu_s": round(ru1.ru_utime + ru1.ru_stime - ru0.ru_utime - ru0.ru_stime, 1),
            "peak_rss_process_mb": round(peak_proc[0] / 2**20), "peak_rss_aggregate_mb": round(sampler.peak / 2**20)}


if __name__ == "__main__":
    problem, reps = sys.argv[1], int(sys.argv[2])
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    info = machine()
    for rep in range(reps):
        for method in ("shallow", "reflected"):  # interleaved, so slow drift in load affects both alike
            r = {**run(problem, method, workers), "rep": rep, "machine": info, "definitions": __doc__.split("Definitions")[1].strip()}
            open(os.path.join(ROOT, "bench", "perf.jsonl"), "a").write(json.dumps(r) + "\n")
            print(f"rep {rep} {method:9} ok={r['ok']} wall {r['wall_s']:7.1f} s  cpu {r['cpu_s']:7.1f} s  "
                  f"peak/process {r['peak_rss_process_mb']} MB  peak/aggregate {r['peak_rss_aggregate_mb']} MB", flush=True)
