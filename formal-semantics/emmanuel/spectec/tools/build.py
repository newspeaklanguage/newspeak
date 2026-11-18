#!/usr/bin/env python3
"""Check and render the Emmanuel core with the pinned upstream SpecTec.

Forked from formal-semantics/spectec/tools/build.py. It shares the Newspeak
toolchain in formal-semantics/spectec/.toolchain (run that directory's
tools/bootstrap.py first) and builds its own regression driver in a separate
directory of the disposable upstream Dune workspace.
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
NEWSPEAK_SPECTEC = ROOT.parents[1] / "spectec"


def run(*args: str | Path, cwd: Path = ROOT, capture: bool = False) -> str:
    command = [str(arg) for arg in args]
    # See the Newspeak build: force native ARM for the opam/OCaml process.
    if sys.platform == "darwin" and command[0] == str(NEWSPEAK_SPECTEC / ".toolchain/opam"):
        binary = subprocess.run(["/usr/bin/file", "-b", command[0]],
                                capture_output=True, text=True, check=True).stdout
        if "arm64" in binary:
            command = ["/usr/bin/arch", "-arm64", *command]
    result = subprocess.run(command, cwd=cwd, check=True,
                            text=True, stdout=subprocess.PIPE if capture else None)
    return result.stdout if capture else ""


def main() -> None:
    pin = json.loads((NEWSPEAK_SPECTEC / "toolchain.json").read_text())
    toolchain = NEWSPEAK_SPECTEC / ".toolchain"
    upstream = toolchain / "upstream" / "spectec"
    opam = toolchain / "opam"
    if not opam.exists() or not upstream.exists():
        raise SystemExit("Run python3 tools/bootstrap.py in formal-semantics/spectec first.")
    revision = run("git", "rev-parse", "HEAD", cwd=upstream, capture=True).strip()
    if revision != pin["revision"]:
        raise SystemExit(f"wrong SpecTec revision: {revision}; expected {pin['revision']}")
    run(sys.executable, "tools/check_sources.py")
    driver_dir = upstream / "src/emmanuel-regress"
    driver_dir.mkdir(exist_ok=True)
    shutil.copyfile(ROOT / "tools/regress.ml", driver_dir / "regress.ml")
    shutil.copyfile(ROOT / "tools/regress.dune", driver_dir / "dune")
    run(opam, "exec", f"--root={toolchain / 'opam-root'}", "--switch=newspeak", "--",
        "dune", "build", "src/exe-spectec/main.exe", "src/emmanuel-regress/regress.exe", cwd=upstream)
    binary = upstream / "_build/default/src/exe-spectec/main.exe"
    regress = upstream / "_build/default/src/emmanuel-regress/regress.exe"
    core = sorted(ROOT.glob("[0-9][0-9]-*.spectec"))
    library = sorted(ROOT.glob("library/[0-9][0-9]-*.spectec"))
    # The library instantiates the parameters, so it is checked and rendered
    # with the core; its regressions run in a configuration of their own,
    # since the core's run its toy signature instead.
    sources = core + library
    run(binary, "--check", *sources)
    run(binary, "--let-intro-mech", "--check", *sources)
    run(binary, "--all-passes", "--check", *sources)
    fixtures = [ROOT / "tests/host-fixtures.spectec", ROOT / "tests/host-eval-fixtures.spectec",
                ROOT / "tests/signature-fixtures.spectec"]
    library_fixtures = [ROOT / "tests/host-eval-fixtures.spectec", ROOT / "library/tests/library-host.spectec",
                        ROOT / "library/tests/library-helpers.spectec"]
    run(regress, ROOT / "tests/cases.tsv", *core, *fixtures)
    run(regress, ROOT / "library/tests/library-cases.tsv", *core, *library, *library_fixtures)
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    latex = build / "emmanuel.generated.tex"
    ast = build / "emmanuel.ast"
    normalized = build / "emmanuel.mechanization.ast"
    run(binary, "--latex", *sources, "-o", latex)
    run(binary, "--ast", *sources, "-o", ast)
    run(binary, "--all-passes", "--ast", *sources, "-o", normalized)
    # Deterministic and path-independent generation, as for Newspeak.
    for mode, output in ((["--latex"], latex), (["--ast"], ast),
                         (["--all-passes", "--ast"], normalized)):
        original = output.read_bytes()
        run(binary, *mode, *sources, "-o", output)
        if output.read_bytes() != original:
            raise SystemExit(f"nondeterministic output: {output.name}")
        with tempfile.TemporaryDirectory(prefix="emmanuel-spectec-") as directory:
            temp = Path(directory)
            for source in sources:
                shutil.copyfile(source, temp / source.name)
            run(binary, *mode, *(temp / source.name for source in sources), "-o", temp / output.name)
            if (temp / output.name).read_bytes() != original:
                raise SystemExit(f"path-dependent output: {output.name}")
    report = {
        "upstream_revision": revision,
        "note": "Checked/ rendered only; no proofs generated.",
        "artifacts": {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                      for path in (latex, ast, normalized)},
        "source_manifest_sha256": hashlib.sha256((ROOT / "manifest.json").read_bytes()).hexdigest(),
        "regression_count": {str(cases.relative_to(ROOT)): sum(bool(line) and not line.startswith("#")
                                                           for line in cases.read_text().splitlines())
                             for cases in (ROOT / "tests/cases.tsv", ROOT / "library/tests/library-cases.tsv")},
        "test_inputs": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                        for path in [ROOT / "tests/cases.tsv", ROOT / "library/tests/library-cases.tsv",
                                     ROOT / "tools/regress.ml", *fixtures, *library_fixtures]},
        "test_harness_workaround": "Pinned IL suffix-list matcher corrected only in regress.ml",
    }
    (build / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("Emmanuel SpecTec checking, regressions, and repeatable generation passed.")


if __name__ == "__main__":
    main()
