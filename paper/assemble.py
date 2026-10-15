"""Assemble paper/whitepaper/*.md into paper/whitepaper.md, with a generated list of tables and figures, and
typeset paper/whitepaper.pdf (pandoc + Tectonic, STIX Two fonts, LaTeX math) when both are installed.
Fails if a {{placeholder}} or a citation without a reference remains.  Usage: python3 paper/assemble.py"""
import glob, json, os, re, shutil, subprocess, sys

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


def pdf(md):
    """The print variant: title block from metadata, LaTeX's own contents, no Mermaid (an ASCII twin is kept)."""
    lines = md.split("\n")
    title = re.sub(r"^# ", "", lines[0])
    subtitle = next(l for l in lines if l.startswith("### "))[4:]
    authors = [a.replace("**", "").strip() for a in next(l for l in lines if l.startswith("**Michael")).split("·")]
    when = next(l for l in lines if l.startswith("*Whitepaper")).strip("*")
    body = md[md.index("## Abstract"):]
    body = re.sub(r"## Contents\n.*?### List of tables and figures", "## List of tables and figures", body, flags=re.S)
    body = re.sub(r"```mermaid\n.*?```\n", "", body, flags=re.S)
    meta = "---\n" + "\n".join([f"title: {json.dumps(title)}", f"subtitle: {json.dumps(subtitle)}",
                                  "author:"] + [f"  - {json.dumps(a)}" for a in authors] + [f"date: {json.dumps(when)}", "---", ""])
    src = os.path.join(HERE, "whitepaper-print.md")
    open(src, "w").write(meta + body)
    r = subprocess.run(["pandoc", src, "-o", os.path.join(HERE, "whitepaper.pdf"), "--pdf-engine=tectonic",
                        "-H", os.path.join(HERE, "pdf-header.tex"), "-V", "geometry:margin=2cm", "-V", "fontsize=10pt",
                        "-V", "colorlinks=true", "--toc", "--toc-depth=2"], capture_output=True, text=True)
    os.remove(src)
    missing = len(re.findall("Missing character", r.stderr))
    return r.returncode, missing


if shutil.which("pandoc") and shutil.which("tectonic"):
    code, missing = pdf(out)
    print(f"whitepaper.pdf: {'built' if code == 0 else f'FAILED (exit {code})'}, {missing} missing glyphs")
    problems += [f"PDF build failed (exit {code})"] * (code != 0) + [f"{missing} missing glyphs in the PDF"] * (missing > 0)
for p in problems:
    print("  " + p)
sys.exit(1 if problems else 0)
