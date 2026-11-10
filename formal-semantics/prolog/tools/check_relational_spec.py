#!/usr/bin/env python3
"""Check the proof-facing Newspeak Prolog subset and emit traceability data.

This is intentionally a source checker, not a Prolog implementation.  It
guards the small trusted boundary between the readable clauses and the Lean
correspondence development: forbidden extra-logical constructs are rejected,
every clause is tied to LaTeX and Lean, and calls may target only predicates
defined in the source (plus the declarative `dif/2` constraint).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass, asdict
from pathlib import Path


ANNOTATION = re.compile(r"^%\s+@(latex|also|lean|mode|variant)\s+(.+?)\s*$")
MODE = re.compile(r"^([a-z][a-zA-Z0-9_]*)\(([-+,?](?:,[-+,?])*)?\)$")
LABEL = re.compile(r"\\label\{eq:([^}]+)\}")
RULE = re.compile(r"\\rulelabel\{([^}]+)\}")
FUNCTOR = re.compile(r"^\s*([a-z][a-zA-Z0-9_]*)\s*(?:\((.*)\))?\s*$", re.S)

FORBIDDEN = {
    "cut": re.compile(r"(?<![A-Za-z0-9_])!(?![=])"),
    "negation as failure": re.compile(r"\\\+"),
    "dynamic update": re.compile(r"\b(?:asserta?|retractall?|abolish)\s*\("),
    "meta-call": re.compile(r"\b(?:call|once|ignore|findall|bagof|setof)\s*\("),
    "instantiation test": re.compile(r"\b(?:var|nonvar|ground)\s*\("),
    "if-then or disjunction": re.compile(r"(?:->|;)"),
    "arithmetic evaluation": re.compile(r"\bis\b"),
    "I/O or process effect": re.compile(
        r"\b(?:write|writeln|format|open|close|consult|shell|halt)\s*\("
    ),
}

ALLOWED_EXTERNAL = {("dif", 2)}

EQUATION_DISPOSITIONS = {
    "encoded",
    "term-representation",
    "abstract-contract",
    "theorem-only",
    "deferred",
}


@dataclass(frozen=True)
class Clause:
    line: int
    latex: str
    also: tuple[str, ...]
    lean: str
    mode: str
    variant: str | None
    predicate: str
    arity: int
    normalized: str


@dataclass(frozen=True)
class EquationDisposition:
    label: str
    status: str
    rationale: str


def read_equation_dispositions(root: Path) -> tuple[dict[str, EquationDisposition], list[str]]:
    path = root / "EQUATION_DISPOSITIONS.tsv"
    errors: list[str] = []
    if not path.exists():
        return {}, ["EQUATION_DISPOSITIONS.tsv is missing"]
    result: dict[str, EquationDisposition] = {}
    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip() or raw.startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 3:
            errors.append(
                f"EQUATION_DISPOSITIONS.tsv:{line_number}: expected three tab-separated fields"
            )
            continue
        label, status, rationale = (field.strip() for field in fields)
        if label in result:
            errors.append(
                f"EQUATION_DISPOSITIONS.tsv:{line_number}: duplicate equation {label}"
            )
            continue
        if status not in EQUATION_DISPOSITIONS:
            errors.append(
                f"EQUATION_DISPOSITIONS.tsv:{line_number}: unknown status {status}"
            )
        if not rationale:
            errors.append(
                f"EQUATION_DISPOSITIONS.tsv:{line_number}: rationale is required"
            )
        result[label] = EquationDisposition(label, status, rationale)
    return result, errors


def split_top_level(text: str, delimiter: str = ",") -> list[str]:
    pieces: list[str] = []
    start = 0
    paren = bracket = 0
    for index, char in enumerate(text):
        if char == "(":
            paren += 1
        elif char == ")":
            paren -= 1
        elif char == "[":
            bracket += 1
        elif char == "]":
            bracket -= 1
        elif char == delimiter and paren == 0 and bracket == 0:
            pieces.append(text[start:index].strip())
            start = index + 1
        if paren < 0 or bracket < 0:
            raise ValueError(f"unbalanced term near {text!r}")
    if paren or bracket:
        raise ValueError(f"unbalanced term {text!r}")
    pieces.append(text[start:].strip())
    return pieces


def term_signature(term: str) -> tuple[str, int]:
    match = FUNCTOR.match(term.strip())
    if not match:
        raise ValueError(f"not a predicate call: {term!r}")
    name, arguments = match.groups()
    if arguments is None:
        return name, 0
    return name, len(split_top_level(arguments))


def normalize(clause: str) -> str:
    return re.sub(r"\s+", " ", clause.strip())


def remove_comments(source: str) -> str:
    return "\n".join(line.split("%", 1)[0] for line in source.splitlines())


def clauses_from(source: str) -> list[tuple[int, dict[str, str], str]]:
    """Return source clauses with the most recent complete annotation set."""
    result: list[tuple[int, dict[str, str], str]] = []
    metadata: dict[str, str] = {}
    buffer: list[str] = []
    start_line = 0
    depth = 0

    for line_number, raw in enumerate(source.splitlines(), 1):
        annotation = ANNOTATION.match(raw)
        if annotation and not buffer:
            metadata[annotation.group(1)] = annotation.group(2)
            continue
        code = raw.split("%", 1)[0].strip()
        if not code:
            continue
        if not buffer:
            start_line = line_number
        buffer.append(code)
        depth += code.count("(") + code.count("[")
        depth -= code.count(")") + code.count("]")
        if depth == 0 and code.endswith("."):
            result.append((start_line, metadata, " ".join(buffer)))
            metadata = {}
            buffer = []
    if buffer:
        raise ValueError(f"unterminated clause beginning at line {start_line}")
    return result


def body_calls(clause: str) -> list[tuple[str, int]]:
    text = clause[:-1].strip()
    if ":-" not in text:
        return []
    _head, body = text.split(":-", 1)
    return [term_signature(goal) for goal in split_top_level(body)]


def find_latex_references(formal_dir: Path) -> tuple[set[str], set[str]]:
    equations: set[str] = set()
    rules: set[str] = set()
    for path in formal_dir.glob("*.tex"):
        text = path.read_text(encoding="utf-8")
        equations.update(LABEL.findall(text))
        rules.update(RULE.findall(text))
    return equations, rules


def lean_reference_exists(lean_dir: Path, reference: str) -> bool:
    pieces = reference.split(".")
    meaningful = [piece for piece in pieces if piece not in {"Newspeak", "Program"}]
    lean_sources = list((lean_dir / "Newspeak").glob("*.lean"))
    lean_sources.append(lean_dir / "Newspeak.lean")
    texts = [path.read_text(encoding="utf-8") for path in lean_sources]
    # Constructors are accepted only if their enclosing declaration and the
    # constructor token both occur.  Structure projections and definitions use
    # the same conservative token-presence criterion.
    return all(any(re.search(rf"\b{re.escape(piece.rstrip('?'))}\b", text)
                   for text in texts) for piece in meaningful)


def latex_reference_error(
    reference: str, equations: set[str], rules: set[str]
) -> str | None:
    """Validate one rule/equation reference used by @latex or @also."""
    if reference.startswith("rule:"):
        name = reference.removeprefix("rule:")
        return None if name in rules else f"unknown LaTeX rule {name}"
    if reference.startswith("equation:"):
        name = reference.removeprefix("equation:")
        return None if name in equations else f"unknown LaTeX equation {name}"
    return "LaTeX reference must use rule: or equation:"


def clause_latex_references(clause: Clause) -> tuple[str, ...]:
    """Return the primary and any secondary LaTeX references of a clause."""
    return (clause.latex,) + clause.also


def check(root: Path) -> tuple[list[Clause], list[str]]:
    formal_dir = root.parent
    lean_dir = formal_dir / "lean"
    source_path = root / "newspeak.pl"
    source = source_path.read_text(encoding="utf-8")
    errors: list[str] = []

    code_without_comments = remove_comments(source)
    for description, pattern in FORBIDDEN.items():
        match = pattern.search(code_without_comments)
        if match:
            line = code_without_comments.count("\n", 0, match.start()) + 1
            errors.append(f"{source_path.name}:{line}: forbidden {description}")

    equations, rules = find_latex_references(formal_dir)
    parsed: list[Clause] = []
    raw_clauses = clauses_from(source)
    defined: set[tuple[str, int]] = set()

    for line, metadata, raw_clause in raw_clauses:
        text = raw_clause[:-1].strip()
        head = text.split(":-", 1)[0].strip()
        try:
            predicate, arity = term_signature(head)
        except ValueError as exc:
            errors.append(f"{source_path.name}:{line}: {exc}")
            continue
        defined.add((predicate, arity))

        for required in ("latex", "lean", "mode"):
            if required not in metadata:
                errors.append(
                    f"{source_path.name}:{line}: missing @{required} annotation"
                )
        if not all(key in metadata for key in ("latex", "lean", "mode")):
            continue

        latex = metadata["latex"]
        also = tuple(
            reference.strip() for reference in metadata.get("also", "").split(",")
            if reference.strip()
        )
        for annotation_name, reference in (
            [("@latex", latex)] + [("@also", reference) for reference in also]
        ):
            reference_error = latex_reference_error(reference, equations, rules)
            if reference_error:
                errors.append(
                    f"{source_path.name}:{line}: {annotation_name} {reference_error}"
                )
        if latex in also or len(set(also)) != len(also):
            errors.append(
                f"{source_path.name}:{line}: duplicate primary or secondary LaTeX reference"
            )

        mode_match = MODE.match(metadata["mode"])
        if not mode_match:
            errors.append(f"{source_path.name}:{line}: malformed @mode")
        else:
            mode_predicate = mode_match.group(1)
            signs = [] if mode_match.group(2) is None else mode_match.group(2).split(",")
            if mode_predicate != predicate or len(signs) != arity:
                errors.append(
                    f"{source_path.name}:{line}: @mode does not match {predicate}/{arity}"
                )

        if not lean_reference_exists(lean_dir, metadata["lean"]):
            errors.append(
                f"{source_path.name}:{line}: unresolved Lean reference {metadata['lean']}"
            )

        parsed.append(
            Clause(
                line=line,
                latex=latex,
                also=also,
                lean=metadata["lean"],
                mode=metadata["mode"],
                variant=metadata.get("variant"),
                predicate=predicate,
                arity=arity,
                normalized=normalize(raw_clause),
            )
        )

    for line, _metadata, raw_clause in raw_clauses:
        for signature in body_calls(raw_clause):
            if signature not in defined and signature not in ALLOWED_EXTERNAL:
                errors.append(
                    f"{source_path.name}:{line}: call to undefined or external "
                    f"predicate {signature[0]}/{signature[1]}"
                )

    dispositions, disposition_errors = read_equation_dispositions(root)
    errors.extend(disposition_errors)
    covered_equations = {
        reference.removeprefix("equation:")
        for clause in parsed for reference in clause_latex_references(clause)
        if reference.startswith("equation:")
    }
    unknown = sorted(set(dispositions) - equations)
    overlap = sorted(set(dispositions) & covered_equations)
    missing = sorted(equations - set(dispositions) - covered_equations)
    for label in unknown:
        errors.append(f"EQUATION_DISPOSITIONS.tsv: unknown equation {label}")
    for label in missing:
        errors.append(f"EQUATION_DISPOSITIONS.tsv: unclassified equation {label}")
    for label in overlap:
        errors.append(
            f"EQUATION_DISPOSITIONS.tsv: encoded equation {label} must not have a separate disposition"
        )
    for label, disposition in dispositions.items():
        if label not in equations:
            continue
        if disposition.status == "encoded":
            errors.append(
                f"EQUATION_DISPOSITIONS.tsv: {label} uses encoded status; remove the row "
                "because encoded status is inferred from checked clauses"
            )

    return parsed, errors


def manifest_payload(root: Path, clauses: list[Clause]) -> dict[str, object]:
    source_path = root / "newspeak.pl"
    digest = hashlib.sha256(source_path.read_bytes()).hexdigest()
    clause_rows: list[dict[str, object]] = []
    for clause in clauses:
        row = asdict(clause)
        # JSON has no tuple type.  Normalize here so an emitted manifest is
        # byte-for-byte comparable with the subsequently decoded value.
        row["also"] = list(clause.also)
        clause_rows.append(row)
    return {
        "schema": 1,
        "source": "newspeak.pl",
        "sha256": digest,
        "clauses": clause_rows,
    }


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def render_lean_manifest(root: Path, clauses: list[Clause]) -> str:
    payload = manifest_payload(root, clauses)
    rows = [
        "/- This file is generated by prolog/tools/check_relational_spec.py.",
        "   Do not edit it independently of prolog/newspeak.pl. -/",
        "",
        "namespace Newspeak",
        "namespace PrologBridge",
        "",
        "structure PrologClauseManifestEntry where",
        "  line : Nat",
        "  latex : String",
        "  also : List String",
        "  lean : String",
        "  mode : String",
        "  variant : Option String",
        "  predicate : String",
        "  arity : Nat",
        "  normalized : String",
        "deriving Repr, DecidableEq, BEq",
        "",
        f"def prologSourceSHA256 : String := {lean_string(str(payload['sha256']))}",
        "",
        "set_option maxRecDepth 100000 in",
        "def prologClauseManifest : List PrologClauseManifestEntry := [",
    ]
    for index, clause in enumerate(clauses):
        variant = (
            "none" if clause.variant is None
            else f"some {lean_string(clause.variant)}"
        )
        comma = "," if index + 1 < len(clauses) else ""
        rows.extend(
            [
                "  { " + f"line := {clause.line}",
                "    " + f"latex := {lean_string(clause.latex)}",
                "    " + "also := [" + ", ".join(
                    lean_string(reference) for reference in clause.also) + "]",
                "    " + f"lean := {lean_string(clause.lean)}",
                "    " + f"mode := {lean_string(clause.mode)}",
                "    " + f"variant := {variant}",
                "    " + f"predicate := {lean_string(clause.predicate)}",
                "    " + f"arity := {clause.arity}",
                "    " + f"normalized := {lean_string(clause.normalized)} }}{comma}",
            ]
        )
    rows.extend(["]", "", "end PrologBridge", "end Newspeak", ""])
    return "\n".join(rows)


def render_coverage(root: Path, clauses: list[Clause]) -> str:
    equations, rules = find_latex_references(root.parent)
    dispositions, errors = read_equation_dispositions(root)
    if errors:
        raise ValueError("invalid equation disposition file: " + "; ".join(errors))
    covered_rules = {
        reference.removeprefix("rule:")
        for clause in clauses for reference in clause_latex_references(clause)
        if reference.startswith("rule:")
    }
    covered_equations = {
        reference.removeprefix("equation:")
        for clause in clauses for reference in clause_latex_references(clause)
        if reference.startswith("equation:")
    }
    all_dispositions = dict(dispositions)
    for name in covered_equations:
        all_dispositions[name] = EquationDisposition(
            name, "encoded", "Represented by one or more checked Horn clauses.")
    rows = [
        "# Prolog bridge coverage",
        "",
        "This ledger is generated from the labels in the LaTeX sources and the",
        "annotations on the checked clauses, plus the checked disposition of every",
        "numbered equation. No equation is left implicit or unclassified.",
        "",
        f"Rules: **{len(covered_rules)} / {len(rules)}** represented.",
        f"Equations: **{len(covered_equations)} / {len(equations)}** encoded as clauses.",
        "",
        "## Named rules",
        "",
    ]
    rows.extend(
        f"- [{'x' if name in covered_rules else ' '}] `{name}`"
        for name in sorted(rules)
    )
    rows.extend(["", "## Equation dispositions", ""])
    for status in sorted(EQUATION_DISPOSITIONS):
        names = sorted(name for name in equations
            if all_dispositions[name].status == status)
        rows.append(f"- **{status}**: {len(names)}")
    rows.extend(["", "## Numbered equations", "",
        "| Equation | Disposition | Rationale |",
        "|---|---|---|"])
    rows.extend(
        f"| `eq:{name}` | `{all_dispositions[name].status}` | "
        f"{all_dispositions[name].rationale} |"
        for name in sorted(equations)
    )
    rows.append("")
    return "\n".join(rows)


def emit(root: Path, clauses: list[Clause]) -> None:
    payload = manifest_payload(root, clauses)
    digest = payload["sha256"]
    (root / "traceability.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    rows = [
        "# Prolog traceability manifest",
        "",
        f"Source SHA-256: `{digest}`",
        "",
        "| Line | Predicate | LaTeX | Also | Variant | Lean |",
        "|---:|---|---|---|---|---|",
    ]
    for clause in clauses:
        rows.append(
            f"| {clause.line} | `{clause.predicate}/{clause.arity}` | "
            f"`{clause.latex}` | `{', '.join(clause.also)}` | "
            f"`{clause.variant or ''}` | `{clause.lean}` |"
        )
    rows.append("")
    (root / "TRACEABILITY.md").write_text("\n".join(rows), encoding="utf-8")
    lean_path = root.parent / "lean" / "Newspeak" / "GeneratedPrologManifest.lean"
    lean_path.write_text(render_lean_manifest(root, clauses), encoding="utf-8")
    (root / "COVERAGE.md").write_text(
        render_coverage(root, clauses), encoding="utf-8"
    )


def generated_files_current(root: Path, clauses: list[Clause]) -> list[str]:
    errors: list[str] = []
    json_path = root / "traceability.json"
    markdown_path = root / "TRACEABILITY.md"
    lean_path = root.parent / "lean" / "Newspeak" / "GeneratedPrologManifest.lean"
    coverage_path = root / "COVERAGE.md"
    if (not json_path.exists() or not markdown_path.exists() or
            not lean_path.exists() or not coverage_path.exists()):
        return ["generated traceability files are missing; run with --write"]
    try:
        current = json.loads(json_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"cannot read generated traceability manifest: {exc}"]
    expected = manifest_payload(root, clauses)
    if current != expected:
        errors.append("traceability.json is stale; run checker with --write")
    digest_line = f"Source SHA-256: `{expected['sha256']}`"
    markdown = markdown_path.read_text(encoding="utf-8")
    if digest_line not in markdown:
        errors.append("TRACEABILITY.md is stale; run checker with --write")
    expected_lean = render_lean_manifest(root, clauses)
    if lean_path.read_text(encoding="utf-8") != expected_lean:
        errors.append("GeneratedPrologManifest.lean is stale; run checker with --write")
    expected_coverage = render_coverage(root, clauses)
    if coverage_path.read_text(encoding="utf-8") != expected_coverage:
        errors.append("COVERAGE.md is stale; run checker with --write")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write", action="store_true", help="refresh JSON and Markdown manifests"
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    clauses, errors = check(root)
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    if args.write:
        emit(root, clauses)
    else:
        generated_errors = generated_files_current(root, clauses)
        if generated_errors:
            for error in generated_errors:
                print(error, file=sys.stderr)
            return 1
    print(
        f"checked {len(clauses)} clauses in newspeak.pl; "
        "all constructs and traceability references are valid"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
