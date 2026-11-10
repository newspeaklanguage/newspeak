#!/usr/bin/env python3
"""Check and render the Newspeak slice with the pinned upstream SpecTec.

No ad-hoc parser replaces SpecTec. Regression evaluation also consumes the
upstream IL, not a separately maintained Python/Prolog encoding of the rules.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(*args: str | Path, cwd: Path = ROOT, capture: bool = False) -> str:
    command = [str(arg) for arg in args]
    # The user's python3 can run under Rosetta even though our opam/OCaml is
    # native ARM. Force the native launch preference for the compiler process;
    # otherwise Apple's assembler may incorrectly default to x86_64.
    if sys.platform == "darwin" and command[0] == str(ROOT / ".toolchain/opam"):
        binary = subprocess.run(["/usr/bin/file", "-b", command[0]],
                                capture_output=True, text=True, check=True).stdout
        if "arm64" in binary:
            command = ["/usr/bin/arch", "-arm64", *command]
    result = subprocess.run(command, cwd=cwd, check=True,
                            text=True, stdout=subprocess.PIPE if capture else None)
    return result.stdout if capture else ""


def main() -> None:
    pin = json.loads((ROOT / "toolchain.json").read_text())
    toolchain = ROOT / ".toolchain"
    upstream = toolchain / "upstream" / "spectec"
    opam = toolchain / "opam"
    if not opam.exists() or not upstream.exists():
        raise SystemExit("Run python3 tools/bootstrap.py first (requires downloads).")
    revision = run("git", "rev-parse", "HEAD", cwd=upstream, capture=True).strip()
    if revision != pin["revision"]:
        raise SystemExit(f"wrong SpecTec revision: {revision}; expected {pin['revision']}")
    run(sys.executable, "tools/check_sources.py")
    run(sys.executable, "-m", "unittest", "discover", "-s", "tools", "-p", "test_*.py")
    # Copy our test driver into the disposable upstream Dune workspace.
    # No patch to the upstream semantic checker is needed.
    driver_dir = upstream / "src/newspeak-regress"
    driver_dir.mkdir(exist_ok=True)
    shutil.copyfile(ROOT / "tools/regress.ml", driver_dir / "regress.ml")
    shutil.copyfile(ROOT / "tools/regress.dune", driver_dir / "dune")
    run(opam, "exec", f"--root={toolchain / 'opam-root'}", "--switch=newspeak", "--",
        "dune", "build", "src/exe-spectec/main.exe", "src/newspeak-regress/regress.exe", cwd=upstream)
    binary = upstream / "_build/default/src/exe-spectec/main.exe"
    regress = upstream / "_build/default/src/newspeak-regress/regress.exe"
    sources = sorted(ROOT.glob("[0-9][0-9]-*.spectec"))
    run(binary, "--check", *sources)
    run(binary, "--let-intro-mech", "--check", *sources)
    run(binary, "--all-passes", "--check", *sources)
    fixtures = sorted((ROOT / "tests").glob("*fixtures.spectec"))
    run(regress, ROOT / "tests/cases.tsv", *sources, *fixtures)
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    latex = build / "newspeak.generated.tex"
    ast = build / "newspeak.ast"
    normalized = build / "newspeak.mechanization.ast"
    run(binary, "--latex", *sources, "-o", latex)
    run(binary, "--ast", *sources, "-o", ast)
    run(binary, "--all-passes", "--ast", *sources, "-o", normalized)
    # Test deterministic generation, not just successful generation.
    for mode, output in ((["--latex"], latex), (["--ast"], ast),
                         (["--all-passes", "--ast"], normalized)):
        original = output.read_bytes()
        run(binary, *mode, *sources, "-o", output)
        if output.read_bytes() != original:
            raise SystemExit(f"nondeterministic output: {output.name}")
        # Different checkout paths must not change generated semantics.
        with tempfile.TemporaryDirectory(prefix="newspeak-spectec-") as directory:
            temp = Path(directory)
            for source in sources:
                shutil.copyfile(source, temp / source.name)
            run(binary, *mode, *(temp / source.name for source in sources), "-o", temp / output.name)
            if (temp / output.name).read_bytes() != original:
                raise SystemExit(f"path-dependent output: {output.name}")
    report = {
        "upstream_revision": revision,
        "note": "Checked/ rendered only; no Rocq code or equivalence proofs generated.",
        "artifacts": {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                      for path in (latex, ast, normalized)},
        "source_manifest_sha256": hashlib.sha256((ROOT / "manifest.json").read_bytes()).hexdigest(),
        "regression_count": sum(bool(line) and not line.startswith("#")
                                for line in (ROOT / "tests/cases.tsv").read_text().splitlines()),
        "test_inputs": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                        for path in [ROOT / "tests/cases.tsv", ROOT / "tools/regress.ml", *fixtures]},
        "external_pure_primitives": ["textConcatenate"],
        "test_harness_workaround": "Pinned IL suffix-list matcher corrected only in regress.ml",
    }
    (build / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("SpecTec checking, regressions, and repeatable mathematical/AST generation passed.")


if __name__ == "__main__":
    main()
