#!/usr/bin/env python3
"""Per-declaration token and line similarity of the library against the Technion's PiPCF.lean.

Usage: python3 scripts/similarity_pipcf.py PATH/TO/PiPCF.lean OUT.json REF [REF ...]
where REF is a git revision or WORKTREE. For every declaration of ours it records the best
difflib ratio of its token sequence against any PiPCF declaration ("token_sim"), the same with
identifiers abstracted ("structure_sim"), and the whitespace-normalised lines of 12 or more
characters that also occur verbatim in PiPCF.lean ("shared_lines"). Comments are stripped first.
"""
import difflib, json, re, subprocess, sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from verify import strip_comments  # noqa: E402

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
                  r"(def|theorem|lemma|structure|abbrev|instance)\s+([^\s:({\[]+)", re.M)
TOK = re.compile(r"[A-Za-z_\u0370-\u03ff\u1d00-\u1dbf\u2080-\u209c][\w'\u2080-\u209c.!?]*|\d+|\S")
IDENT = re.compile(r"^[A-Za-z_\u0370-\u03ff]")
KEEP = {"by", "fun", "have", "show", "exact", "rw", "simp", "ring", "field_simp", "intro", "refine",
        "unfold", "linarith", "nlinarith", "positivity", "norm_num", "linear_combination", "calc",
        "obtain", "rcases", "induction", "with", "at", "only", "push_cast", "omega", "theorem", "def"}

def decls(text):
    text = strip_comments(text)
    ms = list(DECL.finditer(text))
    out = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        body = text[m.start():end]
        body = re.split(r"^(?:end\b|namespace\b|section\b|open\b)", body, flags=re.M)[0]
        out.append((m.group(2), body))
    return out

def toks(s): return TOK.findall(s)
def abstract(ts): return [t if (t in KEEP or not IDENT.match(t)) else "ID" for t in ts]
def norm_lines(s):
    return [" ".join(l.split()) for l in s.splitlines() if len(" ".join(l.split())) >= 12]

def compare(ours, theirs):
    tl = set(l for _, b in theirs for l in norm_lines(b))
    rows = []
    for name, body in ours:
        t = toks(body); ta = abstract(t)
        best = (0, None); besta = (0, None)
        for tn, tb in theirs:
            u = toks(tb)
            r = difflib.SequenceMatcher(None, t, u, autojunk=False).ratio()
            if r > best[0]: best = (r, tn)
            ra = difflib.SequenceMatcher(None, ta, abstract(u), autojunk=False).ratio()
            if ra > besta[0]: besta = (ra, tn)
        nl = norm_lines(body)
        shared = [l for l in nl if l in tl]
        rows.append({"decl": name, "tokens": len(t), "token_sim": round(best[0], 3),
                     "closest": best[1], "structure_sim": round(besta[0], 3),
                     "closest_structure": besta[1], "lines": len(nl), "shared_lines": shared})
    return rows

def main():
    root = pathlib.Path(__file__).resolve().parents[1]
    theirs = decls(pathlib.Path(sys.argv[1]).read_text())
    result = {}
    files = ["Exact", "Pincherle", "Series", "Problem21", "Euler21", "ReviewedProblem21"]
    for ref in sys.argv[3:]:
        result[ref] = {}
        for f in files:
            if ref == "WORKTREE":
                text = (root / "RamanujanChallenge" / f"{f}.lean").read_text()
            else:
                text = subprocess.run(["git", "show", f"{ref}:RamanujanChallenge/{f}.lean"],
                                      cwd=root, capture_output=True, text=True, check=True).stdout
            result[ref][f] = compare(decls(text), theirs)
    with open(sys.argv[2], 'w') as fh:
        json.dump(result, fh, indent=1, ensure_ascii=False)

main()
