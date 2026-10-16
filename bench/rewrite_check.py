"""Bounded validation of the rewrite (miniscoping, cnf closure) on the benchmark (whitepaper §6.2.2).

Usage: python3 bench/rewrite_check.py OUT [SECONDS]   (CM_CACHE and VAMPIRE as for bench.py; default 60 s per problem)
For every problem of OUT/results-final-{dev,second,third}.jsonl for which Vampire found a model, it pairs each source
record, read by the test oracle (test_cm.raw: its own reader, cnf clauses closed by ∀), with the formula problem()
produced for it, and marks a formula *rewritten* when problem() changed its text. Each rewritten formula is then
evaluated, original against rewritten, with the oracle's brute-force evaluator (test_cm.holds) on
  (a) the found model, (b) up to 50 one-entry mutations of it, and (c) 10 random structures of the same signature
      with domain sizes 1 to 3 (seeded by the problem name),
and any disagreement is recorded. Writes OUT/rewrite-check.jsonl. This is bounded validation on these structures,
not a proof of equivalence. Exit 1 on any disagreement."""
import json, os, random, sys, time
from concurrent.futures import ProcessPoolExecutor, TimeoutError as Timeout

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
MODEL = ("certified", "certified (native)", "lean rejected")


def structures(n, consts, tables, seed):
    """The model, its one-entry mutations (at most 50) and 10 random structures of the same signature."""
    yield "model", n, consts, tables
    muts = [(f, a) for f in sorted(tables) for a in sorted(tables[f])][:50]
    other = lambda v: not v if isinstance(v, bool) else v % n + 1
    for f, a in muts:
        yield "mutation", n, consts, {**tables, f: {**tables[f], a: other(tables[f][a])}}
    rnd = random.Random(seed)
    for _ in range(10):
        m = rnd.randint(1, 3)
        val = lambda v: rnd.random() < 0.5 if isinstance(v, bool) else rnd.randint(1, m)
        import itertools
        yield ("random", m, {c: val(v) for c, v in consts.items()},
               {f: {a: val(v) for a in itertools.product(range(1, m + 1), repeat=len(next(iter(t))))} for f, (t, v) in
                ((f, (t, next(iter(t.values())))) for f, t in tables.items())})


def check(path):
    import cm, test_cm
    t0 = time.time()
    source, rewritten = test_cm.raw(path), cm.problem(path)
    verbatim = [r["formula"] for r in cm.statements(path)]
    assert len(source) == len(rewritten) == len(verbatim)
    changed = [i for i, (_, g) in enumerate(rewritten) if g != verbatim[i]]
    n, consts, tables = cm.model(path)
    evals, bad = {"model": 0, "mutation": 0, "random": 0}, []
    for kind, m, c, t in structures(n, consts, tables, os.path.basename(path)):
        for i in changed:
            if test_cm.holds(source[i][1], m, c, t) != test_cm.holds(rewritten[i][1], m, c, t):
                bad.append({"formula": i, "structure": kind, "source": source[i][1][:200], "rewritten": rewritten[i][1][:200]})
            evals[kind] += 1
    return {"formulas": len(source), "rewritten": len(changed), "evaluations": evals, "disagreements": bad[:5],
            "status": "agree" if not bad else "DISAGREE", "seconds": round(time.time() - t0, 1)}


if __name__ == "__main__":
    out, limit = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 60
    todo = [(s, json.loads(l)) for s in ("dev", "second", "third") if os.path.exists(f"{out}/results-final-{s}.jsonl")
            for l in open(f"{out}/results-final-{s}.jsonl")]
    todo = [(s, r) for s, r in todo if r["verdict"] in MODEL]
    todo.sort(key=lambda x: os.path.getsize(f"{ROOT}/bench/problems/{x[1]['problem']}"))
    recs = []
    for s, r in todo:
        with ProcessPoolExecutor(1) as ex:
            fut = ex.submit(check, f"{ROOT}/bench/problems/{r['problem']}")
            try:
                rec = fut.result(timeout=limit)
            except Timeout:
                rec = {"status": f"unchecked: time limit {limit} s"}
                for p in ex._processes.values():
                    p.kill()
            except Exception as e:
                rec = {"status": f"unchecked: {type(e).__name__}: {str(e)[:120]}"}
        rec = {"sample": s, "problem": r["problem"], "verdict_in_run": r["verdict"], **rec}
        recs.append(rec)
        print(f"{s:6} {r['problem']:<18} {rec['status']}  rewritten {rec.get('rewritten')}/{rec.get('formulas')}  {rec.get('evaluations')}", flush=True)
    open(f"{out}/rewrite-check.jsonl", "w").write("".join(json.dumps(x) + "\n" for x in recs))
    from collections import Counter
    print(Counter(x["status"].split(":")[0] for x in recs))
    print("rewritten formulas checked:", sum(x.get("rewritten") or 0 for x in recs if x["status"] == "agree"),
          "of", sum(x.get("formulas") or 0 for x in recs if x["status"] == "agree"), "formulas in fully checked problems")
    sys.exit(1 if any(x["status"] == "DISAGREE" for x in recs) else 0)
