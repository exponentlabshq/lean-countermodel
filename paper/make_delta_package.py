"""Build a review delta: every file added or changed between BASE and HEAD, one file each (no archives), named
<PREFIX>__<path with / as __>, and <PREFIX>__MANIFEST.json with the base and new commits, each file's repository path,
size and SHA-256, the previous SHA-256 of each changed file, and the paths deleted or renamed since BASE.

Usage: python3 paper/make_delta_package.py OUT_DIR BASE PREFIX [PATH=COMMIT ...]
Each PATH=COMMIT also accepts PATH's content at COMMIT as a valid previous version (for a reviewer's tree that holds
an older copy of that one file).
Apply with apply_delta.py (beside the package): it checks every hash, including the previous version of each changed
file in the target tree, before changing anything."""
import hashlib, json, os, subprocess, sys

O, BASE, PREFIX = sys.argv[1], sys.argv[2], sys.argv[3]
ALSO = dict(a.split("=", 1) for a in sys.argv[4:])
os.makedirs(O, exist_ok=True)
manifest = os.path.join(O, f"{PREFIX}__MANIFEST.json")
if os.path.exists(manifest):
    sys.exit(f"{O} already has a manifest; build into a fresh directory")
git = lambda *a: subprocess.run(["git", *a], capture_output=True, check=True).stdout
if git("status", "--porcelain", "--untracked-files=no").strip():
    sys.exit("tracked files have uncommitted changes; commit first")
HEAD, BASE = git("rev-parse", "HEAD").decode().strip(), git("rev-parse", BASE).decode().strip()
sha = lambda b: hashlib.sha256(b).hexdigest()
files, deleted, renamed = [], [], []
for line in git("diff", "--name-status", "-M", BASE, HEAD).decode().splitlines():
    st, *paths = line.split("\t")
    if st == "D":
        deleted.append(paths[0])
        continue
    old, path = (paths[0], paths[1]) if st.startswith("R") else (paths[0], paths[0])
    if st.startswith("R"):
        renamed.append({"from": old, "to": path})
    if path == ".gitignore":
        continue
    data = git("show", f"{HEAD}:{path}")
    prev = None if st == "A" else sha(git("show", f"{BASE}:{old}"))
    name = f"{PREFIX}__" + path.replace("/", "__") + ("" if "." in os.path.basename(path) else ".txt")
    open(os.path.join(O, name), "wb").write(data)
    files.append({"upload_name": name, "repo_path": path, "kind": "added" if st == "A" else "renamed" if st.startswith("R") else "changed",
                  "bytes": len(data), "sha256": sha(data), "previous_sha256": prev,
                  "also_accepted_previous_sha256": [sha(git("show", f"{ALSO[path]}:{path}"))] if path in ALSO else []})
json.dump({"base_commit": BASE, "new_commit": HEAD, "files": sorted(files, key=lambda e: e["upload_name"]),
           "deleted_since_base": deleted, "renamed_since_base": renamed}, open(manifest, "w"), indent=1)
print(f"{len(files)} files, {sum(e['bytes'] for e in files):,} bytes; {len(deleted)} deleted, {len(renamed)} renamed; {BASE[:7]} -> {HEAD[:7]}")
