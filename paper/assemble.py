"""Assemble paper/whitepaper/*.md into paper/whitepaper.md, with a generated list of tables and figures.
Fails if a {{placeholder}} or a citation without a reference remains.  Usage: python3 paper/assemble.py"""
import glob, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
parts = sorted(glob.glob(os.path.join(HERE, "whitepaper", "[0-9][0-9]-*.md")))
refs = open(os.path.join(HERE, "whitepaper", "references.md")).read()
body = "\n\n".join(open(p).read().strip() for p in parts)

# A table or figure is named after the nearest heading above it.
items, heading, in_code = [], None, False
for line in body.split("\n"):
    if line.startswith("```"):
        if not in_code and heading:
            kind = "Figure" if any(k in line for k in ("mermaid", "text", "```")) else None
            items.append(("Figure", heading)) if kind and line.strip() in ("```", "```mermaid", "```text") else None
        in_code = not in_code
    elif not in_code and re.match(r"#{2,4} ", line):
        heading = line.lstrip("#").strip()
    elif not in_code and line.startswith("|---") and heading:
        items.append(("Table", heading))
seen, listing = set(), []
for kind, h in items:
    if (kind, h) not in seen:
        seen.add((kind, h))
        listing.append(f"- {kind}: {h}")
body = body.replace("{{generated at assembly}}", "\n".join(listing), 1)

prose = re.sub(r"`[^`\n]*`", "", re.sub(r"```.*?```", "", body, flags=re.S))  # code is not prose
cited = {int(n) for c in re.findall(r"\[(\d+(?:\s*,\s*\d+)*)(?:,\s*§[^\]]*)?\]", prose) for n in re.findall(r"\d+", c)}
listed = {int(n) for n in re.findall(r"^(\d+)\. ", refs, re.M)}
problems = [f"placeholder: {m}" for m in re.findall(r"\{\{[^}]*\}\}", body)]
problems += [f"citation [{n}] has no reference" for n in sorted(cited - listed)]
out = body + "\n\n---\n\n## References\n\n" + refs.split("\n", 1)[1].strip() + "\n"
open(os.path.join(HERE, "whitepaper.md"), "w").write(out)
print(f"{len(parts)} sections, {len(listing)} tables/figures, {len(cited)} references cited, {len(out.split())} words")
for p in problems:
    print("  " + p)
sys.exit(1 if problems else 0)
