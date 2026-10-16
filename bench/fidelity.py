"""Source-fidelity check of every certified benchmark result (whitepaper §6.2.2), independent of cm.py's reading.

Usage: python3 bench/fidelity.py OUT [SECONDS]   (CM_CACHE and VAMPIRE as for bench.py; default 120 s per problem)
For each record of OUT/results-final-{dev,second,third}.jsonl whose verdict is certified or certified (native), it
takes the model Lean certified (cm.model, read from the cached Vampire answer), and has the test oracle read the
*original* problem file with its own record reader (test_cm.records/raw: no code shared with cm.statements or
problem) and evaluate every formula by brute force (test_cm.holds): every non-conjecture formula must hold and the
conjecture must fail. Writes OUT/fidelity.jsonl: faithful, NOT FAITHFUL, or unchecked (time limit or error).
Exit 1 if any certified result is not faithful."""
import json, os, sys, time
from concurrent.futures import ProcessPoolExecutor, TimeoutError as Timeout

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)


def check(path):
    """(verdict, formulas checked, seconds) for one problem."""
    import cm, test_cm
    t = time.time()
    n, consts, tables = cm.model(path)
    fs = test_cm.raw(path)
    bad = [i for i, (role, f) in enumerate(fs) if test_cm.holds(f, n, consts, tables) == (role == "conjecture")]
    return ("faithful" if not bad else f"NOT FAITHFUL: formulas {bad[:5]}"), len(fs), round(time.time() - t, 1)


if __name__ == "__main__":
    out, limit = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 120
    todo = [(s, json.loads(l)) for s in ("dev", "second", "third") if os.path.exists(f"{out}/results-final-{s}.jsonl")
            for l in open(f"{out}/results-final-{s}.jsonl")]
    todo = [(s, r) for s, r in todo if r["verdict"] in ("certified", "certified (native)")]
    todo.sort(key=lambda x: os.path.getsize(f"{ROOT}/bench/problems/{x[1]['problem']}"))  # the million-fact problem last
    recs = []
    for s, r in todo:  # one process per problem, so a time limit can stop a runaway evaluation
        with ProcessPoolExecutor(1) as ex:
            fut = ex.submit(check, f"{ROOT}/bench/problems/{r['problem']}")
            try:
                verdict, n, secs = fut.result(timeout=limit)
            except Timeout:
                verdict, n, secs = f"unchecked: time limit {limit} s", None, limit
                for p in ex._processes.values():
                    p.kill()
            except Exception as e:
                verdict, n, secs = f"unchecked: {type(e).__name__}: {str(e)[:120]}", None, None
        rec = {"sample": s, "problem": r["problem"], "verdict_in_run": r["verdict"], "commit": r.get("commit"),
               "fidelity": verdict, "source_formulas": n, "seconds": secs}
        recs.append(rec)
        print(f"{s:6} {r['problem']:<18} {verdict} ({n} formulas, {secs} s)", flush=True)
    open(f"{out}/fidelity.jsonl", "w").write("".join(json.dumps(x) + "\n" for x in recs))
    from collections import Counter
    print(Counter(x["fidelity"].split(":")[0] for x in recs))
    sys.exit(1 if any(x["fidelity"].startswith("NOT") for x in recs) else 0)
