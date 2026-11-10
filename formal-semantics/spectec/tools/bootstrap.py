#!/usr/bin/env python3
"""Download/build the pinned toolchain in .toolchain, never in ~/.opam.

On ARM macOS, use a checksummed opam and native static GMP. Elsewhere copy
an installed opam >= 2.0.5 and use existing system GMP/pkg-config. Package
downloads require network access. Nothing changes shell startup files.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parents[1]


def fetch(url: str, destination: Path, digest: str) -> None:
    if not destination.exists():
        print(f"Downloading {url}", flush=True)
        with urlopen(url, timeout=120) as response:
            destination.write_bytes(response.read())
    actual = hashlib.sha256(destination.read_bytes()).hexdigest()
    if actual != digest:
        raise SystemExit(f"checksum mismatch: {destination}; expected {digest}, got {actual}")


def main() -> None:
    pin = json.loads((ROOT / "toolchain.json").read_text())
    local = ROOT / ".toolchain"
    local.mkdir(exist_ok=True)
    env = os.environ.copy()
    arm_macos = platform.system() == "Darwin" and subprocess.run(
        ["/usr/sbin/sysctl", "-n", "hw.optional.arm64"], capture_output=True,
        text=True, check=True).stdout.strip() == "1"

    def run(*args: str | Path, cwd: Path = ROOT, capture: bool = False) -> str:
        command = [str(arg) for arg in args]
        if arm_macos and command[0] in {str(local / "opam"), "make", "/bin/sh"}:
            command = ["/usr/bin/arch", "-arm64", *command]
        result = subprocess.run(command, cwd=cwd, env=env, check=True,
                                text=True, stdout=subprocess.PIPE if capture else None)
        return result.stdout.strip() if capture else ""

    opam = local / "opam"
    if arm_macos:
        fetch(f"https://github.com/ocaml/opam/releases/download/{pin['opam']}/opam-{pin['opam']}-arm64-macos",
              opam, pin["opam_arm64_macos_sha256"])
        opam.chmod(0o755)
        native = local / "native"
        if not (native / "lib/libgmp.a").exists():
            archive = local / f"gmp-{pin['gmp']}.tar.xz"
            fetch(f"https://ftp.gnu.org/gnu/gmp/gmp-{pin['gmp']}.tar.xz", archive, pin["gmp_sha256"])
            run("tar", "-xf", archive, "-C", local)
            source = local / f"gmp-{pin['gmp']}"
            run("/bin/sh", "./configure", f"--prefix={native}", "--disable-shared", cwd=source)
            run("make", "-j6", cwd=source)
            run("make", "check", "-j6", cwd=source)
            run("make", "install", cwd=source)
        env["PKG_CONFIG_PATH"] = str(native / "lib/pkgconfig")
        env["CPPFLAGS"] = f"-I{native / 'include'}"
        env["LDFLAGS"] = f"-L{native / 'lib'}"
        pkg_config = shutil.which("pkg-config")
        if not pkg_config:
            raise SystemExit("pkg-config is required; bootstrap will not install global packages")
        bins = local / "bin"
        bins.mkdir(exist_ok=True)
        compatibility = bins / "pkgconf"
        if not compatibility.exists():
            compatibility.symlink_to(pkg_config)
        env["PATH"] = str(bins) + os.pathsep + env["PATH"]
    elif not opam.exists():
        existing = shutil.which("opam")
        if not existing:
            raise SystemExit("Install opam >= 2.0.5 before bootstrapping on this platform")
        version = tuple(map(int, run(existing, "--version", capture=True).split(".")))
        if version < (2, 0, 5):
            raise SystemExit("Installed opam is too old; need >= 2.0.5")
        shutil.copyfile(existing, opam)
        opam.chmod(0o755)
    opam_root = local / "opam-root"
    if not (opam_root / "config").exists():
        run(opam, "init", f"--root={opam_root}", "--bare", "--no-setup", "--disable-sandboxing", "-y")
    if not (opam_root / "newspeak/bin/ocaml").exists():
        run(opam, "switch", "create", f"--root={opam_root}", "newspeak", pin["ocaml"], "-y", "--jobs=6")
    run(opam, "install", f"--root={opam_root}", "--switch=newspeak", "-y",
        "--assume-depexts", "--jobs=6", *pin["packages"])
    upstream = local / "upstream"
    if not upstream.exists():
        run("git", "clone", "--filter=blob:none", "--no-checkout", pin["repository"], upstream)
        run("git", "sparse-checkout", "set", "spectec", "interpreter", cwd=upstream)
        run("git", "checkout", "--detach", pin["revision"], cwd=upstream)
    actual = run("git", "rev-parse", "HEAD", cwd=upstream, capture=True)
    if actual != pin["revision"]:
        raise SystemExit(f"Existing checkout is at {actual}; will not reset it")
    # Mirror the upstream Makefile's reference-interpreter preparation, but
    # avoid its global opam command and directory-deleting recipe.
    ref = upstream / "spectec/src/backend-interpreter/reference-interpreter"
    if not ref.exists():
        shutil.copytree(upstream / "interpreter", ref,
                        ignore=shutil.ignore_patterns("dune-project", "jslib"))
        shutil.copyfile(ref.parent / "dune-ref-interp", ref / "dune")
    run(opam, "exec", f"--root={opam_root}", "--switch=newspeak", "--",
        "dune", "build", "src/exe-spectec/main.exe", cwd=upstream / "spectec")
    print("Isolated SpecTec checker ready. Run python3 tools/build.py")


if __name__ == "__main__":
    main()
