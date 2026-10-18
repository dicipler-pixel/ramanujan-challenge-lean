#!/usr/bin/env python3
# SCRIPT: RAMANUJAN-CHALLENGE-LEAN-VERIFY-01
"""Audit the Ramanujan Challenge Lean library after `lake build`.

Why each check proves what it claims:

1. Axiom audit. `lake build` accepts a proof that uses `sorry` with only a
   warning, and a declared `axiom` would be accepted silently. `#print axioms`
   asks the kernel which axioms each theorem actually rests on. Requiring the
   answer to lie inside {propext, Classical.choice, Quot.sound} (the standard
   three every Mathlib theorem may use) rules out `sorry` (sorryAx), project
   axioms, and native_decide (Lean.ofReduceBool) for every named theorem.

2. Theorem inventory. The script discovers theorem and lemma names from the
   source files and fails unless every source module is configured and the names
   match the exact list in config.json, so a theorem cannot silently disappear
   from the audit or be swapped for another.

3. False controls. Each file in FalseControls/ states something deliberately
   false. It must FAIL to compile, and it must fail for a mathematical reason
   (unsolved goals, a failed tactic, a proposition proved false), not because of
   a typo, a missing name or a plain type mismatch. This shows the checker can say no: a pipeline that
   accepts everything would pass the first two checks and fail this one.

4. Hashes. The SHA-256 of every source file is written to the report, so anyone
   can confirm the checked files are the files in the repository.

5. Licence headers. Every library file must open with the exact Apache-2.0 header
   in config.json, so no file can silently fall outside the stated licence.

6. No placeholder token. No library file and no false control may contain the
   placeholder keyword anywhere, comments included, so the axiom audit is not the
   only line of defence and no stale remark survives a rewrite.

7. Main theorems. The headline results listed in config.json must be in the
   inventory, and their axiom sets are reported separately.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CONFIG = json.loads((pathlib.Path(__file__).resolve().parent / "config.json").read_text())
MODULES = [(m["module"], m["path"]) for m in CONFIG["modules"]]
EXPECTED_THEOREMS = CONFIG["expected_theorems"]
EXPECTED_FALSE_CONTROLS = CONFIG["expected_false_controls"]
ROOT_IMPORTS = CONFIG["root_imports"]
# Private helper lemmas cannot be named from another file, so they are not listed; their
# axioms are audited through every public theorem that uses them.
THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+)?(?:theorem|lemma)\s+([^\s:({\[]+)", re.M)
NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.M)
MATH_FAILURE = re.compile(
    r"unsolved goals|proved that the proposition.*false|tactic '.*' failed|"
    r"linarith failed|failed to prove|decide failed|norm_num failed|"
    r"made no progress|failed to simplify",
    re.S | re.I)
PLACEHOLDER_RE = re.compile(r"\bsorry\b", re.I)
INFRA_FAILURE = re.compile(
    r"unknown (?:module|identifier|constant|namespace)|unexpected token|"
    r"object file .* does not exist|invalid field", re.I)


LAST_OUTPUT = ""


def run(argv: list[str]) -> subprocess.CompletedProcess:
    global LAST_OUTPUT
    proc = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    LAST_OUTPUT = " ".join(argv) + "\n" + proc.stdout + proc.stderr
    return proc


def strip_comments(text: str) -> str:
    # Lean block comments nest. Preserve newlines so anchored declaration matching
    # remains meaningful. Preserve string literals rather than treating their text
    # as comment delimiters.
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        c = text[i]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif quoted:
            out.append(c)
            i += 1
            if c == "\\" and i < len(text):
                out.append(text[i])
                i += 1
            elif c == '"':
                quoted = False
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i))
            i = end
        else:
            out.append(c)
            quoted = c == '"'
            i += 1
    if depth:
        raise ValueError("unterminated Lean block comment")
    return "".join(out)


def theorems_in(path: pathlib.Path) -> list[str]:
    text = strip_comments(path.read_text())
    spaces = sorted(set(NAMESPACE_RE.findall(text)))
    if len(spaces) != 1:
        raise SystemExit(f"{path}: expected exactly one namespace, found {spaces}")
    return [f"{spaces[0]}.{name}" for name in THEOREM_RE.findall(text)]


def header_ok(text: str) -> bool:
    lines = text.splitlines()
    want = CONFIG["license_header"]
    return lines[:len(want)] == want


def placeholder_lines(text: str) -> list[int]:
    return [i + 1 for i, line in enumerate(text.splitlines()) if PLACEHOLDER_RE.search(line)]


def main() -> int:
    OUT.mkdir(exist_ok=True)
    (OUT / "report.json").unlink(missing_ok=True)
    version = run(["lean", "--version"])
    if version.returncode:
        raise SystemExit("Lean version check failed")
    report: dict = {"lean": version.stdout.strip(), "modules": {}}
    report["inputs"] = {
        rel: hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
        for rel in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "scripts/config.json")
    }
    actual_sources = {str(p.relative_to(ROOT)) for p in (ROOT / "RamanujanChallenge").glob("*.lean")}
    if actual_sources != {rel for _, rel in MODULES}:
        raise SystemExit("source modules differ from configured audit modules")

    # Licence headers and placeholder tokens.
    for _, rel in MODULES:
        text = (ROOT / rel).read_text()
        if not header_ok(text):
            raise SystemExit(f"{rel}: missing or altered Apache-2.0 header")
    for path in [ROOT / rel for _, rel in MODULES] + sorted((ROOT / "FalseControls").glob("*.lean")):
        bad_lines = placeholder_lines(path.read_text())
        if bad_lines:
            raise SystemExit(f"{path.relative_to(ROOT)}: placeholder keyword on lines {bad_lines}")
    report["license_headers"] = "ok"
    report["placeholder_free"] = True

    # Inventory and hashes.
    names: list[str] = []
    for module, rel in MODULES:
        path = ROOT / rel
        found = theorems_in(path)
        if not found:
            raise SystemExit(f"no theorems found in {module}")
        report["modules"][module] = {
            "file": rel,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "theorems": len(found),
        }
        names += found
    total = sum(v["theorems"] for v in report["modules"].values())
    if total != EXPECTED_THEOREMS:
        raise SystemExit(f"inventory changed: {total} theorems, expected {EXPECTED_THEOREMS}")
    if sorted(names) != sorted(CONFIG["expected_names"]):
        raise SystemExit("named declaration inventory changed; review config.json")
    report["theorems"] = total
    missing_main = sorted(set(CONFIG["main_theorems"]) - set(names))
    if missing_main:
        raise SystemExit(f"main theorems missing from inventory: {missing_main}")

    # Axiom audit.
    audit = OUT / "AxiomAudit.lean"
    lines = [f"import {m}" for m in ROOT_IMPORTS] + [""]
    lines += [f"#print axioms {name}" for name in names]
    audit.write_text("\n".join(lines) + "\n")
    proc = run(["lake", "env", "lean", str(audit.relative_to(ROOT))])
    log = proc.stdout + proc.stderr
    (OUT / "axioms.log").write_text(log)
    if proc.returncode != 0:
        print(log)
        raise SystemExit("axiom audit file did not compile")
    axioms: dict[str, list[str]] = {}
    for name in names:
        dep = re.search(re.escape(f"'{name}' depends on axioms: [") + r"([^\]]*)\]", log, re.S)
        none = f"'{name}' does not depend on any axioms" in log
        if dep:
            used = sorted(a.strip() for a in dep.group(1).replace("\n", " ").split(",") if a.strip())
        elif none:
            used = []
        else:
            raise SystemExit(f"no axiom report for {name}")
        bad = set(used) - ALLOWED
        if bad:
            raise SystemExit(f"{name} uses disallowed axioms {sorted(bad)}")
        axioms[name] = used
    report["axioms"] = axioms
    report["axiom_union"] = sorted({a for used in axioms.values() for a in used})
    report["main_theorem_axioms"] = {name: axioms[name] for name in CONFIG["main_theorems"]}

    # False controls.
    controls = {}
    for path in sorted((ROOT / "FalseControls").glob("*.lean")):
        proc = run(["lake", "env", "lean", str(path.relative_to(ROOT))])
        text = proc.stdout + proc.stderr
        (OUT / f"{path.stem}.log").write_text(text)
        if proc.returncode == 0:
            print(text)
            raise SystemExit(f"false control ACCEPTED: {path.name}")
        if INFRA_FAILURE.search(text) or not MATH_FAILURE.search(text):
            print(text)
            raise SystemExit(f"false control failed for the wrong reason: {path.name}")
        controls[path.stem] = "rejected"
    if len(controls) != EXPECTED_FALSE_CONTROLS:
        raise SystemExit(f"expected {EXPECTED_FALSE_CONTROLS} false controls, found {len(controls)}")
    report["false_controls"] = controls

    (OUT / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"OK: {total} theorems, "
          f"axioms used: {report['axiom_union']}, {len(controls)} false controls rejected")
    return 0


def annotate(message: str) -> None:
    """Surface a failure as a GitHub error annotation (readable without the log)."""
    flat = message.replace("%", "%25").replace("\r", "").replace("\n", "%0A")
    print(f"::error title=verify.py::{flat[:6000]}")


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SystemExit as exc:
        if exc.code not in (0, None):
            annotate(str(exc.code) + "%0A" + LAST_OUTPUT[-5000:])
        raise
