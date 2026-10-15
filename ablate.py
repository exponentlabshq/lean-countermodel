"""Axiom ablation: what each conclusion of a theory depends on, with Lean-certified counter-models.

Usage: python3 ablate.py theory.p [OUTDIR]
theory.p holds definitions (role `definition`, always kept), axioms (role `axiom`, ablated one at a time) and
one or more conjectures (the targets). For each target it asks whether the target follows from all axioms, and
then, for each axiom, whether it still follows without that axiom. It also finds one subset-minimal sufficient set by greedy deletion (not necessarily a smallest one, or the only one).

"Does not follow" is backed by a finite counter-model that Lean's kernel certifies (cm.py), so it is trusted.
"Follows" rests on a Vampire proof, which is not certified here; the report labels it as such."""
import json, os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from cm import uncomment

VAMPIRE = os.getenv("VAMPIRE", "vampire")


def statements(path):
    """[(name, role, text)] for every fof statement."""
    src = uncomment(open(path).read())
    return [(m[1], m[2], m[0].strip()) for m in re.finditer(r"fof\(\s*(\w+)\s*,\s*(\w+)\s*,.*?\)\s*\.(?=\s*fof\(|\s*$)", src, re.S)]


def write(path, keep, target):
    """A problem with the kept statements and one conjecture."""
    open(path, "w").write("\n".join(t for _, _, t in keep) + "\n" + target[2] + "\n")
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
    defs = [s for s in st if s[1] == "definition"]
    axioms = [s for s in st if s[1] in ("axiom", "hypothesis")]
    targets = [s for s in st if s[1] == "conjecture"]
    os.makedirs(outdir, exist_ok=True)
    jobs = [(t, None) for t in targets] + [(t, a) for t in targets for a in axioms]

    def run(job):
        t, drop = job
        keep = defs + [a for a in axioms if a is not drop]
        p = write(os.path.join(outdir, f"{t[0]}__without_{drop[0] if drop else 'nothing'}.p"), keep, t)
        return (t[0], drop[0] if drop else None), verdict(p)

    with ThreadPoolExecutor(4) as pool:
        results = dict(pool.map(run, jobs))
    minimal = {}
    for t in targets:  # greedy deletion: drop every axiom whose removal still lets Vampire prove the target
        if results[(t[0], None)]["verdict"] != "follows":
            continue
        need = list(axioms)
        for a in axioms:
            trial = [x for x in need if x is not a]
            if proves(write(os.path.join(outdir, f"{t[0]}__minimal.p"), defs + trial, t)):
                need = trial
        minimal[t[0]] = [a[0] for a in need]
    return {"theory": path, "definitions": [d[0] for d in defs], "axioms": [a[0] for a in axioms],
            "targets": [t[0] for t in targets], "minimal": minimal,
            "results": [{"target": t, "without": d, **v} for (t, d), v in results.items()]}


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
