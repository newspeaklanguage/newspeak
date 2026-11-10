#!/usr/bin/env python3
"""Audit source provenance and emit the SpecTec migration ledger.

This is not a SpecTec parser or a semantic verifier; use the upstream checker
for that. The ledger deliberately reports unconverted definitions as pending.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ANNOTATION = re.compile(r"^;;\s+@(equation|partial|rule)\s+(\S+)\s*$")
DECLARATION = re.compile(r"^(syntax|def|relation|rule)\s+(\S+)")


@dataclass(frozen=True)
class Origin:
    kind: str
    label: str
    file: str
    line: int
    declaration: str


def latex_inventory(main: Path) -> dict[str, tuple[str, int]]:
    result: dict[str, tuple[str, int]] = {}
    visited: set[Path] = set()

    def read(path: Path) -> None:
        if path in visited:
            return
        visited.add(path)
        for line_number, raw in enumerate(path.read_text().splitlines(), 1):
            # Labels and input commands in comments are not source declarations.
            line = re.split(r"(?<!\\)%", raw, maxsplit=1)[0]
            for label in re.findall(r"\\label\{(eq:[^}]+)\}", line):
                if label in result:
                    raise ValueError(f"duplicate equation label: {label}")
                result[label] = (path.name, line_number)
            for rule in re.findall(r"\\rulelabel\{([^}]+)\}", line):
                # The same label also occurs in explanatory cross references.
                result.setdefault(rule, (path.name, line_number))
            for include in re.findall(r"\\input\{([^}]+)\}", line):
                child = path.parent / include
                read(child if child.suffix else child.with_suffix(".tex"))

    read(main)
    return result


def scan_source(path: Path, inventory: dict[str, tuple[str, int]]) -> list[Origin]:
    pending: list[tuple[str, str, int]] = []
    origins: list[Origin] = []
    for line_number, raw in enumerate(path.read_text().splitlines(), 1):
        annotation = ANNOTATION.fullmatch(raw)
        if annotation:
            kind, label = annotation.groups()
            if label not in inventory:
                raise ValueError(f"{path.name}:{line_number}: unknown LaTeX origin {label}")
            if ((kind == "rule" and label.startswith("eq:")) or
                (kind == "equation" and not label.startswith("eq:"))):
                raise ValueError(f"{path.name}:{line_number}: wrong origin kind {kind}")
            pending.append((kind, label, line_number))
        elif "@equation" in raw or "@partial" in raw or "@rule" in raw:
            raise ValueError(f"{path.name}:{line_number}: malformed annotation")
        declaration = DECLARATION.match(raw)
        if declaration and pending:
            decl_kind, name = declaration.groups()
            for kind, label, annotation_line in pending:
                if not label.startswith("eq:") and decl_kind != "rule":
                    raise ValueError(f"{path.name}:{annotation_line}: rule origin must annotate a rule")
                origins.append(Origin(kind, label, path.name, line_number, name))
            pending.clear()
    if pending:
        raise ValueError(f"{path.name}: orphaned origin annotation")
    return origins


def audit(root: Path = ROOT) -> tuple[str, str]:
    inventory = latex_inventory(root.parent / "newspeak-semantics.tex")
    sources = sorted(root.glob("[0-9][0-9]-*.spectec"))
    origins = [origin for path in sources for origin in scan_source(path, inventory)]
    # Overloading is forbidden. A function has one signature and may have
    # several disjoint equations; a relation may have many differently named rules.
    signatures: set[tuple[str, str]] = set()
    rules: set[str] = set()
    for path in sources:
        for line_number, raw in enumerate(path.read_text().splitlines(), 1):
            match = re.match(r"^(def\s+\$\w+\([^=]*\)\s*:\s*|relation\s+\w+\s*:)", raw)
            if match:
                kind, name = re.match(r"^(def|relation)\s+([^\s(:]+)", raw).groups()
                key = (kind, name)
                if key in signatures:
                    raise ValueError(f"{path.name}:{line_number}: overloaded signature {name}")
                signatures.add(key)
            match = re.match(r"^rule\s+(\S+)\s*:", raw)
            if match:
                name = match.group(1)
                if name in rules:
                    raise ValueError(f"{path.name}:{line_number}: duplicate rule {name}")
                rules.add(name)
    by_label: dict[str, list[Origin]] = {}
    for origin in origins:
        by_label.setdefault(origin.label, []).append(origin)
    statuses = {
        label: ("converted" if any(o.kind != "partial" for o in os) else "partial")
        for label, os in by_label.items()
    }
    counts = Counter(statuses.get(label, "pending") for label in inventory)
    lines = ["# LaTeX → SpecTec migration ledger", "",
             "Generated by `python3 tools/check_sources.py --write`.", "",
             "`converted` means a definition/rule has been transcribed, not that",
             "equivalence has been proved. `partial` marks an explicitly incomplete transcription.",
             "Every other source equation and named rule remains explicitly `pending`.", "",
             f"{counts['converted']} converted; {counts['partial']} partial; {counts['pending']} pending.", "",
             "| LaTeX origin | Status | SpecTec declaration |", "| --- | --- | --- |"]
    for label in inventory:
        tex, line = inventory[label]
        links = ", ".join(f"[{o.declaration}]({o.file}#L{o.line})" for o in by_label.get(label, [])) or "—"
        lines.append(f"| [{label}](../{tex}#L{line}) | {statuses.get(label, 'pending')} | {links} |")
    manifest = {
        "latex_sources": {name: hashlib.sha256((root.parent / name).read_bytes()).hexdigest()
                          for name in sorted({file for file, _ in inventory.values()})},
        "spectec_sources": {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in sources},
        "origins": [origin.__dict__ for origin in origins],
        "counts": dict(counts), "spectec_rules": len(rules),
    }
    return "\n".join(lines) + "\n", json.dumps(manifest, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate coverage files")
    args = parser.parse_args()
    markdown, manifest = audit()
    for name, text in (("COVERAGE.md", markdown), ("manifest.json", manifest)):
        path = ROOT / name
        if args.write:
            path.write_text(text)
        elif not path.exists() or path.read_text() != text:
            raise SystemExit(f"{name} is stale; run tools/check_sources.py --write")
    print(markdown.splitlines()[8])


if __name__ == "__main__":
    main()
