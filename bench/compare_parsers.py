"""Compare what an earlier cm.py and the current one read from every benchmark input (whitepaper §6.2.2).

Usage: python3 bench/compare_parsers.py OLD_COMMIT OUT.json   (default commit 30ad4f3, the third-sample run)
For each input it records the number of records problem() returns under both versions and whether the translated
formulas (lean()) are identical; inputs over 5 MB are compared as exact record lists instead."""
import glob, json, os, subprocess, sys, tempfile
from concurrent.futures import ProcessPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def load(old_dir):
    sys.path[:0] = [old_dir, ROOT]
    import cm_old, cm
    return cm_old, cm


def one(args):
    f, old_dir = args
    cm_old, cm = load(old_dir)
    r = {"file": os.path.relpath(f, ROOT)}
    big = os.path.getsize(f) > 5_000_000
    got = {}
    for tag, mod in (("old", cm_old), ("new", cm)):
        try:
            p = mod.problem(f)
            got[tag] = p if big else [(role, mod.lean(x)) for role, x in p]
            r[tag] = len(p)
        except Exception as e:
            got[tag], r[tag] = None, f"{type(e).__name__}: {str(e)[:160]}"
    if got["old"] is None or got["new"] is None:
        r["status"] = "rejected by both" if got["old"] is None and got["new"] is None else "rejection changed"
    else:
        r["status"] = "identical" if got["old"] == got["new"] else "changed"
    return r


if __name__ == "__main__":
    commit, out = (sys.argv[1], sys.argv[2]) if len(sys.argv) > 2 else ("30ad4f3", sys.argv[1])
    old_dir = tempfile.mkdtemp()
    open(os.path.join(old_dir, "cm_old.py"), "w").write(subprocess.run(["git", "show", f"{commit}:cm.py"], cwd=ROOT,
                                                                        capture_output=True, text=True, check=True).stdout)
    files = sorted(glob.glob(f"{ROOT}/bench/problems/*.p")) + sorted(glob.glob(f"{ROOT}/examples/*.p")) + sorted(glob.glob(f"{ROOT}/ablation/*.p"))
    with ProcessPoolExecutor(4) as ex:
        rs = list(ex.map(one, [(f, old_dir) for f in files]))
    from collections import Counter
    summary = Counter(r["status"] for r in rs)
    json.dump({"old_commit": commit, "summary": summary, "inputs": rs}, open(out, "w"), indent=1)
    print(dict(summary))
    for r in rs:
        if r["status"] != "identical":
            print(f"  {r['file']}: {r['status']}, old {r['old']} | new {r['new']}")
