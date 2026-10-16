"""Axiom ablation: what each conclusion of a theory depends on, with Lean-certified counter-models.

Usage: python3 ablate.py theory.p [OUTDIR]
theory.p holds definitions (role `definition`, always kept), axioms (role `axiom`, ablated one at a time) and
one or more conjectures (the targets). For each target it asks whether the target follows from all axioms, and
then, for each axiom, whether it still follows without that axiom. It also finds one subset-minimal sufficient set by greedy deletion (not necessarily a smallest one, or the only one).

"Does not follow" is backed by a finite counter-model that Lean's kernel certifies (cm.py), so it is trusted.
"Follows" rests on a Vampire proof, which is not certified here; the report labels it as such."""
import json, os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from cm import statements as cm_statements

VAMPIRE = os.getenv("VAMPIRE", "vampire")


ROLES = {"definition": "kept", "axiom": "ablated", "hypothesis": "ablated", "conjecture": "target"}  # the ablation language


def statements(path):
    """[(id, role, text, name)] for every record of the theory, read by cm.statements (total and fail-closed).
    id is collision-free (the record's position plus a filename-safe form of its name) and is used for job keys and
    file paths; name is the source name, used in the report. A role outside the ablation language, or two records
    with the same source name, is rejected: no accepted record is ever dropped from an experiment."""
    recs, seen = cm_statements(path), set()
    for r in recs:
        if r["role"] not in ROLES:
            raise ValueError(f"ablate.py: record {r['name']} (line {r['line']}) has role {r['role']!r}; ablation reads only "
                             f"{', '.join(sorted(ROLES))} and refuses the theory rather than drop a premise")
        if r["name"] in seen:
            raise ValueError(f"ablate.py: two records named {r['name']}; record names must identify experiments")
        seen.add(r["name"])
    return [(f"r{i:03d}_{re.sub(r'[^A-Za-z0-9_]', '_', r['name'].strip(chr(39)))}", r["role"], r["text"], r["name"])
            for i, r in enumerate(recs)]


def write(path, keep, target):
    """A problem with the kept statements and one conjecture."""
    open(path, "w").write("\n".join(k[2] for k in keep) + "\n" + target[2] + "\n")
    return path


def proves(path, seconds=30):
    """True if Vampire proves the conjecture, False if it finds the problem counter-satisfiable, None if unknown."""
    out = subprocess.run([VAMPIRE, "--mode", "casc", "-t", str(seconds), path], capture_output=True, text=True).stdout
    status = re.search(r"SZS status (\w+)", out)
    return {"Theorem": True, "CounterSatisfiable": False}.get(status[1] if status else None)


def certify(path):
    """(size, axioms) if cm.py finds a counter-model and Lean's kernel accepts it, else None."""
    cm = subprocess.run(["python3", "cm.py", path], capture_output=True, text=True)
    if cm.returncode:
        return None
    lean = path[:-2] + ".lean"
    open(lean, "w").write(cm.stdout + f"\n#print axioms {re.search(r'^namespace (\S+)', cm.stdout, re.M)[1]}.countermodel\n")
    out = subprocess.run(["lake", "env", "lean", lean], capture_output=True, text=True)
    if out.returncode:
        return None
    return int(re.search(r"a (\d+)-element", cm.stdout)[1]), re.search(r"axioms: \[([^\]]*)\]|does not depend", out.stdout)[0]


def verdict(path):
    """'follows' (Vampire proof), 'counter-model n' (certified), or 'unknown'."""
    if proves(path):
        return {"verdict": "follows", "evidence": "Vampire proof (not certified)"}
    cert = certify(path)
    if cert:
        return {"verdict": "does not follow", "evidence": f"{cert[0]}-element counter-model, kernel-checked ({cert[1]})", "size": cert[0]}
    return {"verdict": "unknown", "evidence": "no proof and no certified counter-model within the limits"}


def ablate(path, outdir):
    st = statements(path)
    defs = [s for s in st if ROLES[s[1]] == "kept"]
    axioms = [s for s in st if ROLES[s[1]] == "ablated"]
    targets = [s for s in st if ROLES[s[1]] == "target"]
    os.makedirs(outdir, exist_ok=True)
    jobs = [(t, None) for t in targets] + [(t, a) for t in targets for a in axioms]

    def run(job):  # keyed and written by collision-free ids; reported by source names
        t, drop = job
        keep = defs + [a for a in axioms if a is not drop]
        p = write(os.path.join(outdir, f"{t[0]}__without_{drop[0] if drop else 'nothing'}.p"), keep, t)
        return (t[0], drop[0] if drop else None), verdict(p)

    with ThreadPoolExecutor(4) as pool:
        results = dict(pool.map(run, jobs))
    assert len(results) == len(jobs), "every experiment must have its own result"
    name = {s[0]: s[3] for s in st}
    minimal = {}
    for t in targets:  # greedy deletion: drop every axiom whose removal still lets Vampire prove the target
        if results[(t[0], None)]["verdict"] != "follows":
            continue
        need = list(axioms)
        for a in axioms:
            trial = [x for x in need if x is not a]
            if proves(write(os.path.join(outdir, f"{t[0]}__minimal.p"), defs + trial, t)):
                need = trial
        minimal[t[3]] = [a[3] for a in need]
    return {"theory": path, "definitions": [d[3] for d in defs], "axioms": [a[3] for a in axioms],
            "targets": [t[3] for t in targets], "minimal": minimal,
            "results": [{"target": name[t], "without": name[d] if d else None, **v} for (t, d), v in results.items()]}


def table(report):
    """The dependency map as Markdown: one row per axiom, one column per target."""
    cell, full = {}, {r["target"]: r["verdict"] for r in report["results"] if r["without"] is None}
    for r in report["results"]:
        v, t = r["verdict"], r["target"]
        if r["without"] is None:
            c = "follows" if v == "follows" else f"does **not** follow ({r['size']}-elt)" if "size" in r else "?"
        elif full[t] != "follows":  # removing an axiom cannot make an underivable target need it
            c = "still does not follow" if v == "does not follow" else "?"
        else:
            c = f"**needed** ({r['size']}-elt)" if v == "does not follow" else "not needed" if v == "follows" else "?"
        cell[(r["without"], t)] = c
    ts = report["targets"]
    head = "| Without ↓ / target → | " + " | ".join(f"`{t}`" for t in ts) + " |\n|---|" + "---|" * len(ts) + "\n"
    full = "| *(nothing removed)* | " + " | ".join(cell[(None, t)] for t in ts) + " |\n"
    rows = "".join(f"| `{a}` | " + " | ".join(cell[(a, t)] for t in ts) + " |\n" for a in report["axioms"])
    mins = "".join(f"\n- Subset-minimal sufficient set (greedy) for `{t}`: " + ", ".join(f"`{a}`" for a in m) for t, m in report["minimal"].items())
    return head + full + rows + mins + "\n"


if __name__ == "__main__":
    out = sys.argv[2] if len(sys.argv) > 2 else "ablation/out"
    report = ablate(sys.argv[1], out)
    json.dump(report, open(os.path.join(out, "report.json"), "w"), indent=1)
    print(table(report))
