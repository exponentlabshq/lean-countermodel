"""Build the reviewer's evidence folder: every tracked file at HEAD, one file each (no archives), plus the two official
TPTP originals behind the include defect, history and diffs, and 01_MANIFEST.json (repository path, size and
SHA-256 of every file). The folder's README and restore script are kept beside it, not generated here.

Usage: python3 paper/make_review_package.py OUT_DIR    (OUT_DIR must not contain an earlier manifest)"""
import hashlib, json, os, subprocess, sys

O = sys.argv[1]
os.makedirs(O, exist_ok=True)
if os.path.exists(os.path.join(O, "01_MANIFEST.json")):
    sys.exit(f"{O} already has a manifest; build into a fresh directory")
git = lambda *a: subprocess.run(["git", *a], capture_output=True, check=True).stdout
C = git("rev-parse", "HEAD").decode().strip()
if git("status", "--porcelain", "--untracked-files=no").strip():
    sys.exit("tracked files have uncommitted changes; commit first so the package matches one commit")
sha = lambda b: hashlib.sha256(b).hexdigest()
PAPER = {"paper/whitepaper.pdf", "paper/whitepaper.md", "paper/response-to-review-round3.md", "paper/response-to-review-round2.md",
         "paper/response-to-review.md", "paper/make_review_package.py"}
SKIP = {".gitignore", "bench/slice10000.p"}  # slice: 648 KB, derived from NLP263+1; listed under "excluded" with its hash
files = []


def kind(p):
    if p.startswith(("Cm/", "Refl/", "nakamura/AutoCM/")) or p == "bench/inputs.json":
        return "generated output (committed)"
    if p.startswith("paper/"):
        return "manuscript, response or packaging script"
    if p.startswith(("examples/", "ablation/")):
        return "input or recorded result"
    if p.startswith("bench/") and not p.endswith(".py"):
        return "recorded log or data"
    return "exact source or configuration"


def put(data, path, k, note=None):
    name = path.replace("/", "__") + ("" if "." in os.path.basename(path) else ".txt")
    open(os.path.join(O, name), "wb").write(data)
    files.append({"upload_name": name, "repo_path": path, "kind": k, "bytes": len(data), "sha256": sha(data), **({"note": note} if note else {})})


for p in git("ls-files").decode().split():
    if p in SKIP or (p.startswith("paper/") and p not in PAPER):
        continue
    put(git("show", f"HEAD:{p}"), p, kind(p))

inputs = json.load(open("bench/inputs.json"))
for f in ("BOO008-3.p", "RNG025-9.p"):  # outside bench/sources, so the input-integrity test still skips until all 300 are rebuilt
    data = open(f"bench/sources/{f}", "rb").read()
    assert sha(data) == inputs["problems"][f]["source"], f
    put(data, f"evidence/tptp-v9.3.1-originals/{f}", "official TPTP v9.3.1 original (git-ignored in the repository)",
        f"SHA-256 equals bench/inputs.json problems[{f}].source")

put(git("log", "--format=%H %P%n  %ad  %s", "--date=iso-strict", "c68baed^..HEAD"), "history/git-log-review-rounds-2-3.txt",
    "recorded git history", "from the round-2 tag (c68baed) to this package's commit: hash, parents, date, subject")
put(git("diff", "900818d", "acb343b"), "history/diff-900818d-acb343b.patch.txt", "recorded diff",
    "freeze commit to the commit that ran the development and second samples")
put(git("diff", "acb343b", "30ad4f3", "--", "bench.py", "cm.py", "Checker.lean", "bench/frozen.py", "bench/replay.py", "test_cm.py"),
    "history/diff-acb343b-30ad4f3-code.patch.txt", "recorded diff", "code between the development/second-sample run and the third-sample run")
put(git("diff", "62d43d6", "30ad4f3", "--", "cm.py", "Checker.lean"), "history/diff-62d43d6-30ad4f3-certificate-code.patch.txt",
    "recorded diff", "certificate-generating code between the timed commit and the final evaluation commit")
put(git("diff", "30ad4f3", C, "--", "cm.py", "bench.py", "Checker.lean", "test_cm.py", "tests", "bench/frozen.py", "bench/replay.py",
        "bench/inputs.py", "bench/perf.py", "recheck.sh"),
    "history/diff-30ad4f3-package-code.patch.txt", "recorded diff", "code changes after the third-sample run, up to this package")

json.dump({"commit": C, "files": sorted(files, key=lambda e: e["upload_name"]), "excluded": [
    {"what": "TPTP v9.3.1 release", "url": inputs["url"], "bytes": inputs.get("tarball_bytes"), "sha256": inputs.get("tarball_sha256"),
     "regenerate": "download and unpack, then: python3 bench/inputs.py TPTP-v9.3.1 TPTP-v9.3.1.tgz (rebuilds and checks every input against bench/inputs.json)"},
    {"what": "bench/slice10000.p, the first 10,000 statements of NLP263+1 (slice timings)", "bytes": os.path.getsize("bench/slice10000.p"),
     "sha256": sha(open("bench/slice10000.p", "rb").read())},
    {"what": "generated benchmark certificates (bench/lean, including the 253-module NLP263+1 reflected tree) and .olean files",
     "regenerate": "bench/frozen.py, then bench/replay.py, at the recorded commits (usage in each file)"},
    {"what": "Vampire answer cache (bench/vampire-cache)",
     "regenerate": "rebuilt by cm.py when CM_CACHE is set; keys are SHA-256 of input + flags + Vampire version (third-sample keys in bench/third-cache-provenance.json)"}]},
    open(os.path.join(O, "01_MANIFEST.json"), "w"), indent=1)
print(f"{len(files)} files, {sum(e['bytes'] for e in files):,} bytes, commit {C}")
