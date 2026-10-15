"""The benchmark's inputs, rebuilt from the official TPTP release and checked against fixed SHA-256s.

Usage:
    python3 bench/inputs.py verify TPTP_DIR [TARBALL]   rebuild bench/sources, bench/axioms and bench/problems from an
                                                        unpacked release (e.g. TPTP-v9.3.1/) and compare every file with
                                                        the committed bench/inputs.json; with TARBALL, also check the
                                                        release digest. Exit 1 on any mismatch. Never rewrites the manifest.
    python3 bench/inputs.py record TPTP_DIR [TARBALL]   rebuild the same files and write what was observed to
                                                        bench/inputs.candidate.json (never to bench/inputs.json)
Each problem of the development, second and third samples is copied verbatim to bench/sources/, the axiom files it
includes to bench/axioms/, and its expansion by bench.expand to bench/problems/. test_cm.py checks all three against
bench/inputs.json once they exist."""
import hashlib, json, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from bench import expand

B = os.path.dirname(os.path.abspath(__file__))
sha = lambda b: hashlib.sha256(b).hexdigest()


def names():
    """Every problem the benchmark has used, in a fixed order."""
    sets = [[json.loads(l)["problem"] for l in open(f"{B}/results.jsonl")],
            json.load(open(f"{B}/heldout-sample.json"))["problems"]]
    if os.path.exists(f"{B}/third-sample.json"):
        sets.append(json.load(open(f"{B}/third-sample.json"))["problems"])
    return [f for s in sets for f in s]


def rebuild(root):
    """Copy and expand every input from the release at root; return what was observed."""
    for d in ("sources", "axioms", "problems"):
        os.makedirs(f"{B}/{d}", exist_ok=True)
    used, problems = {}, {}

    def read(f):  # an axiom file from the release, copied verbatim
        data = open(f"{root}/Axioms/{f}", "rb").read()
        used[f] = sha(data)
        open(f"{B}/axioms/{f}", "wb").write(data)
        return data.decode("latin-1")

    for f in names():
        data = open(f"{root}/Problems/{f[:3]}/{f}", "rb").read()
        open(f"{B}/sources/{f}", "wb").write(data)
        try:
            out = expand(data.decode("latin-1"), read).encode("latin-1")
            problems[f] = {"source": sha(data), "expanded": sha(out)}
        except ValueError as e:  # refused at expansion: recorded, and bench.py reports it as unsupported input
            out = data
            problems[f] = {"source": sha(data), "expanded": None, "refused": str(e)}
        open(f"{B}/problems/{f}", "wb").write(out)
    return problems, dict(sorted(used.items()))


if __name__ == "__main__":
    if len(sys.argv) < 3 or sys.argv[1] not in ("verify", "record"):
        sys.exit(__doc__)
    mode, root, tarball = sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else None
    release = os.path.basename(os.path.normpath(root))
    problems, axioms = rebuild(root)
    if mode == "record":
        meta = {"release": release, "url": f"https://tptp.org/TPTP/Distribution/{release}.tgz"}
        if tarball:
            meta["tarball_bytes"], meta["tarball_sha256"] = os.path.getsize(tarball), sha(open(tarball, "rb").read())
        meta["includes_in_comments"] = sorted(f for f in problems if re.search(r"%.*include\(", open(f"{B}/sources/{f}", encoding="latin-1").read()))
        json.dump({**meta, "problems": problems, "axioms": axioms}, open(f"{B}/inputs.candidate.json", "w"), indent=1)
        print(f"{len(problems)} problems, {len(axioms)} axiom files recorded in bench/inputs.candidate.json")
        sys.exit(0)
    expected, bad = json.load(open(f"{B}/inputs.json")), []
    if release != expected["release"]:
        bad.append(f"release {release}, expected {expected['release']}")
    if tarball and sha(open(tarball, "rb").read()) != expected["tarball_sha256"]:
        bad.append(f"tarball digest differs from {expected['tarball_sha256']}")
    for f, h in expected["problems"].items():
        got = problems.get(f)
        if got is None or got["source"] != h["source"] or got["expanded"] != h["expanded"]:
            bad.append(f"problem {f}")
    bad += [f"axiom file {f}" for f, h in expected["axioms"].items() if axioms.get(f) != h]
    bad += [f"unexpected problem {f}" for f in problems if f not in expected["problems"]]
    if bad:
        sys.exit("MISMATCH against bench/inputs.json:\n  " + "\n  ".join(bad))
    print(f"verified: {len(problems)} problems and {len(axioms)} axiom files match bench/inputs.json"
          + (" and the release tarball digest" if tarball else ""))
