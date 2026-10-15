"""The frozen evaluation (whitepaper §6.2, §6.2.1, §6.2.2): run all three samples at one commit.

Usage, from a clean worktree of the commit under test (so the code cannot change mid-run):
    git worktree add --detach ../frozen <commit> && cd ../frozen
    for d in problems sources axioms vampire-cache; do ln -s <repo>/bench/$d bench/$d; done
    lake build && python3 bench/frozen.py <repo>/bench [dev second third] && python3 bench/replay.py <repo>/bench
Writes OUT/results-final-{dev,second,third}.jsonl, each record tagged with the commit and the SHA-256 of the input it
ran on (bench/inputs.json). Development problems come from OUT/results.jsonl (the original sampling log), the second
sample from OUT/heldout-sample.json, the third from OUT/third-sample.json."""
import hashlib, json, os, subprocess, sys, time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import bench

OUT = sys.argv[1]
commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()
sets = {"final-dev": [json.loads(l)["problem"] for l in open(f"{OUT}/results.jsonl")],
        "final-second": json.load(open(f"{OUT}/heldout-sample.json"))["problems"],
        "final-third": json.load(open(f"{OUT}/third-sample.json"))["problems"]}
sets = {k: v for k, v in sets.items() if len(sys.argv) < 3 or k[len("final-"):] in sys.argv[2:]}  # optional: only the named sets
inputs = json.load(open(f"{OUT}/inputs.json"))["problems"]
for d in ("lean", "olean"):  # certificates are written here; a fresh worktree has neither (both are git-ignored)
    os.makedirs(f"bench/{d}", exist_ok=True)
for name, probs in sets.items():
    t = time.time()
    with ThreadPoolExecutor(2) as pool:
        rs = list(pool.map(bench.run_hybrid, probs))
    for r in rs:
        r["commit"] = commit
        r["input_sha256"] = hashlib.sha256(open(f"bench/problems/{r['problem']}", "rb").read()).hexdigest()
        assert r["input_sha256"] == (inputs[r["problem"]]["expanded"] or inputs[r["problem"]]["source"]), r["problem"]
    open(f"{OUT}/results-{name}.jsonl", "w").write("".join(json.dumps(r) + "\n" for r in rs))
    print(name, "commit", commit, Counter(r["verdict"] for r in rs), f"in {time.time() - t:.0f} s", flush=True)
