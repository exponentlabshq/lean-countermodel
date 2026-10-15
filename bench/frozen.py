"""The frozen evaluation (whitepaper §6.2, §6.2.1): rerun the development and held-out sets at one commit.

Usage, from a clean worktree of the commit under test (so the code cannot change mid-run):
    git worktree add --detach ../frozen <commit> && cd ../frozen
    ln -s <repo>/bench/problems bench/problems; ln -s <repo>/bench/vampire-cache bench/vampire-cache
    lake build Checker && python3 bench/frozen.py <repo>/bench
Writes OUT/results-final-dev.jsonl and OUT/results-final-heldout.jsonl, each record tagged with the commit.
Development problems are read from OUT/results.jsonl (the original sampling log), held-out from OUT/heldout-sample.json."""
import json, os, subprocess, sys, time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import bench

OUT = sys.argv[1]
commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()
sets = {"final-dev": [json.loads(l)["problem"] for l in open(f"{OUT}/results.jsonl")],
        "final-heldout": json.load(open(f"{OUT}/heldout-sample.json"))["problems"]}
for name, probs in sets.items():
    t = time.time()
    with ThreadPoolExecutor(2) as pool:
        rs = list(pool.map(bench.run_hybrid, probs))
    for r in rs:
        r["commit"] = commit
    open(f"{OUT}/results-{name}.jsonl", "w").write("".join(json.dumps(r) + "\n" for r in rs))
    print(name, "commit", commit, Counter(r["verdict"] for r in rs), f"in {time.time() - t:.0f} s", flush=True)
