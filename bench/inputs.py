"""The benchmark's inputs, rebuilt from the official TPTP release and recorded with their SHA-256s.

Usage:
    python3 bench/inputs.py TPTP_DIR [TARBALL]   rebuild bench/sources, bench/axioms and bench/problems from an unpacked
                                                 TPTP release (e.g. TPTP-v9.3.1/); write bench/inputs.json
Each problem in the development, second and third samples is copied verbatim to bench/sources/, the axiom files it includes to bench/axioms/, and its expansion by
bench.expand to bench/problems/. test_cm.py checks all three against bench/inputs.json."""
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


if __name__ == "__main__":
    root, tarball = sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None
    for d in ("sources", "axioms", "problems"):
        os.makedirs(f"{B}/{d}", exist_ok=True)
    used = {}

    def read(f):  # an axiom file from the release, copied verbatim
        data = open(f"{root}/Axioms/{f}", "rb").read()
        used[f] = sha(data)
        open(f"{B}/axioms/{f}", "wb").write(data)
        return data.decode("latin-1")

    problems = {}
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
    release = os.path.basename(os.path.normpath(root))
    meta = {"release": release, "url": f"https://tptp.org/TPTP/Distribution/{release}.tgz"}
    if tarball:
        meta["tarball_bytes"], meta["tarball_sha256"] = os.path.getsize(tarball), sha(open(tarball, "rb").read())
    meta["includes_in_comments"] = sorted(f for f in problems if re.search(r"%.*include\(", open(f"{B}/sources/{f}", encoding="latin-1").read()))
    json.dump({**meta, "problems": problems, "axioms": dict(sorted(used.items()))}, open(f"{B}/inputs.json", "w"), indent=1)
    print(f"{len(problems)} problems, {len(used)} axiom files from {release}; "
          f"{sum(1 for h in problems.values() if h['expanded'] is None)} refused at expansion")
