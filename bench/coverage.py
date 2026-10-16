"""Coverage report for every certified benchmark result (whitepaper §6.2.2), with each check kept separate.

Usage: python3 bench/coverage.py OUT [SECONDS]   (after fidelity.py, rewrite_check.py and replay.py; CM_CACHE, VAMPIRE)
Writes OUT/coverage.json and OUT/coverage.md. One row per certified result (strict or native-assisted), with:
  original_satisfaction  bench/fidelity.py: the oracle reads the original file and evaluates every original formula
                         in the certified model (faithful / NOT FAITHFUL / unchecked)
  rewrite_agreement      bench/rewrite_check.py: rewritten formulas agree with their originals on the model, its
                         mutations and random structures (bounded; agree / DISAGREE / unchecked)
  compilation            bench/replay.py: the certificate recompiled as a module (compiled / COMPILE FAILED)
  kernel_replay          bench/replay.py: leanchecker --fresh (passed / FAILED / not recorded); strict certificates
                         only, native-assisted ones are not replayed. Run after all jobs finish, so no state is "pending".
For each result whose original_satisfaction is unchecked, two further checks, reported separately and never combined
into a conclusion about the original formulas:
  record_identity        cm.statements and the oracle's records consume the whole file and agree record by record on
                         kind, name, role and formula tokens (read with the oracle's lexer)
  rewritten_satisfaction the oracle evaluates the *rewritten* formulas (problem()) in the model; this shows the model
                         satisfies the rewritten problem, not the originals"""
import json, os, sys, time
from concurrent.futures import ProcessPoolExecutor, TimeoutError as Timeout

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)


def record_identity(path):
    import cm, test_cm
    ours, theirs = cm.statements(path), test_cm.records(open(path).read())
    toks = lambda f: " ".join(m[0] for m in test_cm.ORACLE_LEX.finditer(f) if m.lastgroup not in ("ws", "comment"))
    if len(ours) != len(theirs):
        return f"DIFFERENT: {len(ours)} records against {len(theirs)}"
    for i, (a, (k, name, role, f)) in enumerate(zip(ours, theirs)):
        if (a["kind"], a["name"], a["role"], toks(a["formula"])) != (k, name, role, f):
            return f"DIFFERENT at record {i} ({a['name']})"
    return f"identical: {len(ours)} records"


def rewritten_satisfaction(path):
    import cm, test_cm
    n, consts, tables = cm.model(path)
    fs = cm.problem(path)
    bad = [i for i, (role, f) in enumerate(fs) if test_cm.holds(f, n, consts, tables) == (role == "conjecture")]
    return "satisfied" if not bad else f"NOT SATISFIED: formulas {bad[:5]}"


def bounded(fn, path, limit):
    """{result, time_cap_s, seconds}: the check's own outcome, or 'unchecked' with the reason."""
    t = time.time()
    with ProcessPoolExecutor(1) as ex:
        fut = ex.submit(fn, path)
        try:
            res = fut.result(timeout=limit)
        except Timeout:
            for p in ex._processes.values():
                p.kill()
            res = f"unchecked: time limit {limit} s"
        except Exception as e:
            res = f"unchecked: {type(e).__name__}: {str(e)[:120]}"
    return {"result": res, "time_cap_s": limit, "seconds": round(time.time() - t, 1)}


if __name__ == "__main__":
    out, limit = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 300
    jl = lambda f: [json.loads(l) for l in open(f)] if os.path.exists(f) else []
    fid = {r["problem"]: r for r in jl(f"{out}/fidelity.jsonl")}
    rew = {r["problem"]: r for r in jl(f"{out}/rewrite-check.jsonl")}
    rep = {r["problem"]: r for s in ("dev", "second", "third") for r in jl(f"{out}/replay-{s}.jsonl")}
    import subprocess
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    if subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "bench/coverage.py", "bench/fidelity.py", "bench/rewrite_check.py",
                       "cm.py", "test_cm.py"], cwd=ROOT).returncode:
        commit += " (+uncommitted changes)"
    runs = sorted({r.get("commit") for s in ("dev", "second", "third") for r in jl(f"{out}/results-final-{s}.jsonl")} - {None})
    rows = []
    for s in ("dev", "second", "third"):
        for r in jl(f"{out}/results-final-{s}.jsonl"):
            if r["verdict"] not in ("certified", "certified (native)"):
                continue
            p = r["problem"]
            row = {"sample": s, "problem": p, "assurance": "strict" if r["verdict"] == "certified" else "native-assisted",
                   "original_satisfaction": fid.get(p, {}).get("fidelity", "not recorded"),
                   "rewrite_agreement": rew.get(p, {}).get("status", "not recorded"),
                   "compilation": ("compiled" if rep[p]["compiled"] else "COMPILE FAILED") if p in rep else
                   ("not replayed (native-assisted)" if r["verdict"] != "certified" else "not recorded"),
                   "kernel_replay": ("passed" if rep[p]["fresh"] else "FAILED") if p in rep and rep[p].get("fresh") is not None
                   else ("not replayed (native-assisted)" if r["verdict"] != "certified" else "not recorded")}
            if not row["original_satisfaction"].startswith(("faithful", "NOT")):
                path = f"{ROOT}/bench/problems/{p}"
                row["record_identity"] = bounded(record_identity, path, limit)
                row["rewritten_satisfaction"] = bounded(rewritten_satisfaction, path, limit)
            rows.append(row)
            print(row, flush=True)
    json.dump({"report_code_commit": commit, "evaluation_commits": runs,
               "sources": ["results-final-{dev,second,third}.jsonl", "fidelity.jsonl", "rewrite-check.jsonl", "replay-{dev,second,third}.jsonl", "replay.log"],
               "rows": rows}, open(f"{out}/coverage.json", "w"), indent=1)
    from collections import Counter
    lines = ["# Coverage of the certified benchmark results", "",
             f"Evaluation runs at {', '.join(runs)}; report generated by bench/coverage.py at {commit[:7]} from "
             "results-final-*.jsonl, fidelity.jsonl, rewrite-check.jsonl and replay-*.jsonl.", "",
             "Each check is reported separately. *unchecked* means neither verified nor failed; *not recorded* means no outcome "
             "is available. Record identity and rewritten satisfaction are supplementary: they never establish that the "
             "original formulas hold.", ""]
    for a in ("strict", "native-assisted"):
        sub = [x for x in rows if x["assurance"] == a]
        lines += [f"## {a} ({len(sub)})", ""]
        for key in ("original_satisfaction", "rewrite_agreement", "compilation", "kernel_replay"):
            lines.append(f"- **{key}:** " + ", ".join(f"{v} {k}" for k, v in Counter(x[key].split(":")[0] for x in sub).items()))
        lines.append("")
    ex = [x for x in rows if not x["original_satisfaction"].startswith("faithful") or not x["rewrite_agreement"].startswith("agree")
          or x["kernel_replay"] not in ("passed", "not replayed (native-assisted)")]
    lines += ["## Named exceptions", "", "| Sample | Problem | Assurance | Original satisfaction | Rewrite agreement | Compilation | Kernel replay | Record identity | Rewritten satisfaction |",
              "|---|---|---|---|---|---|---|---|---|"]
    lines += [f"| {x['sample']} | {x['problem']} | {x['assurance']} | {x['original_satisfaction']} | {x['rewrite_agreement']} | {x['compilation']} | {x['kernel_replay']} | "
              f"{x.get('record_identity', {}).get('result', '')} | {x.get('rewritten_satisfaction', {}).get('result', '')} |" for x in ex]
    open(f"{out}/coverage.md", "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))
