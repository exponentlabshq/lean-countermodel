"""Build the round-4 delta package: every file added or changed between the round-3 package commit and HEAD, one file
each (no archives), named round4__<path with / as __>, plus the nine round-4 inputs (original and expanded), and
round4__MANIFEST.json (base and repaired commits; path, size and SHA-256 of every file; deleted and renamed paths).
apply_round4.py, kept beside the folder, applies it to a tree restored from the round-3 package.

Usage: python3 paper/make_round4_package.py OUT_DIR [BASE_COMMIT]   (default base 27494892, the round-3 package)"""
import hashlib, json, os, subprocess, sys

O, BASE = sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "27494892f023d908726a643312d2cefd20eb032e"
os.makedirs(O, exist_ok=True)
if os.path.exists(os.path.join(O, "round4__MANIFEST.json")):
    sys.exit(f"{O} already has a manifest; build into a fresh directory")
git = lambda *a: subprocess.run(["git", *a], capture_output=True, check=True).stdout
if git("status", "--porcelain", "--untracked-files=no").strip():
    sys.exit("tracked files have uncommitted changes; commit first")
HEAD = git("rev-parse", "HEAD").decode().strip()
BASE = git("rev-parse", BASE).decode().strip()
sha = lambda b: hashlib.sha256(b).hexdigest()
SKIP = {".gitignore"}
files = []


def put(data, path, kind, note=None):
    name = "round4__" + path.replace("/", "__") + ("" if "." in os.path.basename(path) else ".txt")
    open(os.path.join(O, name), "wb").write(data)
    files.append({"upload_name": name, "repo_path": path, "kind": kind, "bytes": len(data), "sha256": sha(data), **({"note": note} if note else {})})


deleted, renamed = [], []
for line in git("diff", "--name-status", "-M", BASE, HEAD).decode().splitlines():
    st, *paths = line.split("\t")
    if st.startswith("R"):
        renamed.append({"from": paths[0], "to": paths[1]})
        path = paths[1]
    elif st == "D":
        deleted.append(paths[0])
        continue
    else:
        path = paths[0]
    if path in SKIP or path.startswith("paper/peer-review") or path.endswith("assessment_whitepaper_2.md"):
        continue
    kind = "added" if st == "A" else "renamed" if st.startswith("R") else "changed"
    put(git("show", f"{HEAD}:{path}"), path, f"{kind} at {HEAD[:7]}")

inputs = json.load(open("bench/inputs.json"))
cmp_ = {os.path.basename(r["file"]): r for r in json.load(open("bench/parser-comparison.json"))["inputs"]}
for f in sorted(p for p, r in cmp_.items() if r["status"] == "changed"):
    src, exp = open(f"bench/sources/{f}", "rb").read(), open(f"bench/problems/{f}", "rb").read()
    assert sha(src) == inputs["problems"][f]["source"] and sha(exp) == inputs["problems"][f]["expanded"], f
    put(src, f"evidence/round4/inputs/original/{f}", "official TPTP v9.3.1 original (git-ignored in the repository)",
        f"SHA-256 equals bench/inputs.json problems[{f}].source; records read before/after the repair: {cmp_[f]['old']} / {cmp_[f]['new']}")
    put(exp, f"evidence/round4/inputs/expanded/{f}", "expanded input as evaluated (git-ignored in the repository)",
        f"SHA-256 equals bench/inputs.json problems[{f}].expanded")

json.dump({"base_commit": BASE, "repaired_commit": HEAD, "files": sorted(files, key=lambda e: e["upload_name"]),
           "deleted_since_base": deleted, "renamed_since_base": renamed,
           "not_included": ["files unchanged since the base commit (they are in the round-3 package)",
                            "the TPTP release, the Vampire cache, generated benchmark certificate trees and .olean files "
                            "(regenerate with bench/inputs.py, bench/frozen.py and bench/replay.py at the repaired commit)"]},
          open(os.path.join(O, "round4__MANIFEST.json"), "w"), indent=1)
print(f"{len(files)} files, {sum(e['bytes'] for e in files):,} bytes; {len(deleted)} deleted, {len(renamed)} renamed; {BASE[:7]} -> {HEAD[:7]}")
