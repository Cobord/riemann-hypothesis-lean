#!/usr/bin/env python3
"""Check that note/note.tex and the Lean library GroupoidCorr/ are in sync.

Conventions (see CLAUDE.md):
  * Every numbered environment in the note (definition, lemma, proposition,
    theorem, corollary) carries a \\label{KEY}.
  * An item that is formalized carries \\lean{Full.Decl.Name, ...}.
    An item that is deliberately not formalized yet carries \\notready.
  * \\leanok marks an item whose Lean declarations are fully proved
    (no sorry, only standard axioms).
  * In Lean, each declaration that realizes a note item has a docstring
    containing the tag  [note: KEY].

Checks:
  1. every labelled item has \\lean{...} or \\notready (error otherwise);
  2. every name in \\lean{...} exists in GroupoidCorr/ and is tagged with the
     same KEY;
  3. every Lean declaration tagged [note: KEY] is listed under that KEY;
  4. no declaration listed under a \\leanok item contains `sorry` in its source;
  5. with --axioms: run `lake env lean` on a generated file with
     `#print axioms` for each \\leanok declaration and fail if sorryAx or a
     non-standard axiom appears.

Exit status is nonzero on any error. Run from the project root:
    python3 scripts/check_sync.py [--axioms]
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NOTE = ROOT / "note" / "note.tex"
LEAN_DIR = ROOT / "GroupoidCorr"
ENVS = ("definition", "lemma", "proposition", "theorem", "corollary")
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|nonrec)\s+)*"
    r"(def|theorem|lemma|abbrev|structure|class|instance|inductive)\s+([^\s:(\[{]+)",
    re.M,
)
NS_RE = re.compile(r"^\s*namespace\s+(\S+)", re.M)
END_RE = re.compile(r"^\s*end\s+(\S+)", re.M)
TAG_RE = re.compile(r"\[note:\s*([A-Za-z0-9:_\-]+)\]")


def parse_note():
    text = NOTE.read_text(encoding="utf-8")
    items = {}
    env_re = re.compile(r"\\begin\{(" + "|".join(ENVS) + r")\}(.*?)\\end\{\1\}", re.S)
    for m in env_re.finditer(text):
        body = m.group(2)
        lab = re.search(r"\\label\{([^}]*)\}", body)
        if not lab:
            items.setdefault("__unlabelled__", []).append(body[:60])
            continue
        key = lab.group(1)
        names = []
        for lm in re.finditer(r"\\lean\{([^}]*)\}", body):
            names += [n.strip() for n in lm.group(1).split(",") if n.strip()]
        items[key] = {
            "env": m.group(1),
            "lean": names,
            "leanok": "\\leanok" in body,
            "notready": "\\notready" in body,
        }
    return items


def parse_lean():
    """Return {full_name: (tags, source_chunk)} for declarations in GroupoidCorr/."""
    decls = {}
    for path in sorted(LEAN_DIR.rglob("*.lean")):
        src = path.read_text(encoding="utf-8")
        # namespace tracking (simple, line based)
        events = []
        for m in NS_RE.finditer(src):
            events.append((m.start(), "ns", m.group(1)))
        for m in END_RE.finditer(src):
            events.append((m.start(), "end", m.group(1)))
        dms = list(DECL_RE.finditer(src))
        for i, m in enumerate(dms):
            stack = []
            for pos, kind, name in sorted(events):
                if pos > m.start():
                    break
                if kind == "ns":
                    stack.append(name)
                elif stack and stack[-1] == name:
                    stack.pop()
            short = m.group(2)
            full = ".".join(stack + [short]) if not short.startswith("_root_.") else short[7:]
            # docstring immediately before the declaration
            before = src[: m.start()]
            doc = ""
            idx = before.rfind("/--")
            if idx >= 0:
                close = before.find("-/", idx)
                if close >= 0 and before[close + 2:].strip() == "":
                    doc = before[idx + 3:close]
            end = dms[i + 1].start() if i + 1 < len(dms) else len(src)
            chunk = src[m.start():end]
            decls[full] = (TAG_RE.findall(doc), chunk, path.relative_to(ROOT))
    return decls


def main():
    errors, warnings = [], []
    items = parse_note()
    decls = parse_lean()

    for body in items.pop("__unlabelled__", []):
        errors.append(f"note: unlabelled environment starting {body!r}")

    listed = {}
    for key, it in items.items():
        if not it["lean"] and not it["notready"]:
            errors.append(f"note: {key} has neither \\lean{{...}} nor \\notready")
        if it["lean"] and it["notready"]:
            errors.append(f"note: {key} has both \\lean and \\notready")
        if it["leanok"] and not it["lean"]:
            errors.append(f"note: {key} is \\leanok but lists no Lean declaration")
        for name in it["lean"]:
            listed.setdefault(name, []).append(key)
            if name not in decls:
                errors.append(f"note: {key} lists {name}, which is not declared in GroupoidCorr/")
                continue
            tags, chunk, path = decls[name]
            if key not in tags:
                errors.append(f"lean: {name} ({path}) is listed under {key} but its docstring lacks [note: {key}]")
            if it["leanok"] and re.search(r"\bsorry\b", chunk):
                errors.append(f"lean: {name} is under \\leanok item {key} but contains sorry")
        if it["notready"]:
            warnings.append(f"not yet formalized: {key}")

    for name, (tags, chunk, path) in decls.items():
        for t in tags:
            if t not in items:
                errors.append(f"lean: {name} ({path}) tagged [note: {t}] but the note has no such label")
            elif name not in items[t]["lean"]:
                errors.append(f"lean: {name} tagged [note: {t}] but not listed in \\lean{{...}} of {t}")

    if "--axioms" in sys.argv and not errors:
        ok_names = sorted({n for k, it in items.items() if it["leanok"] for n in it["lean"]})
        if ok_names:
            probe = ROOT / "scripts" / "_axioms.lean"
            probe.write_text("import GroupoidCorr\n" + "".join(f"#print axioms {n}\n" for n in ok_names))
            res = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT, capture_output=True, text=True)
            out = res.stdout + res.stderr
            if res.returncode != 0:
                errors.append("axiom check failed to run:\n" + out)
            for blk in re.split(r"(?='\S+' depends on axioms|'\S+' does not depend)", out):
                m = re.match(r"'(\S+)' depends on axioms: \[(.*?)\]", blk, re.S)
                if m:
                    axs = {a.strip() for a in m.group(2).split(",") if a.strip()}
                    bad = axs - STD_AXIOMS
                    if bad:
                        errors.append(f"axioms: {m.group(1)} depends on {sorted(bad)}")

    total = len(items)
    done = sum(1 for it in items.values() if it["leanok"])
    formal = sum(1 for it in items.values() if it["lean"])
    print(f"note items: {total}; with Lean declarations: {formal}; fully proved (\\leanok): {done}")
    for w in warnings:
        print("  warning:", w)
    for e in errors:
        print("  ERROR:", e)
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
