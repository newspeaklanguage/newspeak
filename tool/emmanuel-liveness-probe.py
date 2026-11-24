#!/usr/bin/env python3
"""Time keystrokes in an Emmanuel document's editor, with and without viewers
of the document alive.

Run from tool/:
  python3 emmanuel-liveness-probe.py WORKDIR DOCZIP [NAME] [--variant LABEL=FILE[,FILE2] ...] [--runs N]

DOCZIP is an Emmanuel document zip; NAME defaults to its file name. Each
variant is a version of Ampleforth.ns, and optionally of Documents.ns
(FILE2; the source tree's by default; with no variant, both the tree's, labelled
"tree"); the IDE is built with EmmanuelDeckProbeApp and those versions
into out/EmmanuelLiveness-LABEL.vfuel (the static server must be serving out/
on localhost:8080) and run in headless Chrome by emmanuel-liveness-probe.mjs,
in three scenarios: the editor alone; after a viewer of the document was shown
(WORKDIR/Outer.zip, made here, transcludes it); and after five were. For each
it prints the median time of a keystroke, until it returns and until the page
has settled, and how many presentations were subscribed to the document's
changes.
"""
from pathlib import Path
import importlib.util
import re
import statistics
import subprocess
import sys
import zipfile

TOOL = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("corpus", TOOL / "emmanuel-corpus.py")
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)

OUTER_SOURCE = "[\\paragraph\\]Before[\\endParagraph\\][\\amplet: [shown: '%s']\\]"
OUTER_CLASS = """() (
	shown: name = (
		^transclude: name
	)
) : ()"""


def outer_zip(path, doc, name):
    """A document that transcludes the document, so shows its viewer."""
    with zipfile.ZipFile(path, "w") as z:
        for folder in ("", "contents/", "images/", "video/", "audio/", "documents/", "classes/"):
            z.writestr("Outer/" + folder, "")
        z.writestr("Outer/Outer.ems", OUTER_SOURCE % name)
        z.writestr("Outer/Outer.class", OUTER_CLASS)
        z.writestr("Outer/documents/%s.zip" % name, doc.read_bytes())


def build(snapshot, documents, docs=None):
    """The probe IDE, with documents as its Ampleforth.ns and docs (the
    tree's by default) as its Documents.ns."""
    tree = ("HopscotchForHTML5.ns", "Documents.ns")
    sources = [str(p) for p in sorted(corpus.OUT.glob("*.ns")) if not corpus.from_tree(p.name) and p.name not in tree]
    sources += [str(p) for p in sorted(corpus.NEWSPEAK.glob("*.ns")) if corpus.from_tree(p.name) and p.name != "Ampleforth.ns"]
    sources += [str(documents)]
    sources += [str(corpus.NEWSPEAK / "HopscotchForHTML5.ns"), str(docs or corpus.NEWSPEAK / "Documents.ns")]
    sources += [str(p) for p in sorted(corpus.OUT.glob("platform/*/*.ns"))]
    images = [str(p) for p in sorted(corpus.OUT.glob("*.png"))]
    subprocess.run([str(corpus.PRIMORDIALSOUP / "out/ReleaseX64/primordialsoup"),
                    str(corpus.PRIMORDIALSOUP / "out/snapshots/WebCompiler.vfuel"),
                    *sources, *images, "PrimordialSoup/WebRuntime", "EmmanuelDeckProbeApp",
                    str(corpus.OUT / snapshot)], check=True, cwd=corpus.OUT)


def run(work, snapshot, doc, name, outer, scenario):
    chrome = subprocess.Popen([corpus.CHROME, "--headless=new", "--disable-gpu", "--no-sandbox", "--no-first-run",
                               f"--remote-debugging-port={corpus.PORT}", f"--user-data-dir={work / 'chrome-profile'}",
                               "about:blank"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        corpus.wait_for_chrome()
        args = [corpus.NODE, str(TOOL / "emmanuel-liveness-probe.mjs"), str(corpus.PORT),
                f"http://localhost:8080/primordialsoup.html?snapshot={snapshot}", str(doc), name, str(outer), scenario]
        result = subprocess.run(args, capture_output=True, text=True)
    finally:
        chrome.terminate()
        chrome.wait()
    return result.stdout + result.stderr


def main():
    args = sys.argv[1:]
    variants, runs = [], 1
    while "--variant" in args:
        i = args.index("--variant")
        label, _, paths = args[i + 1].partition("=")
        files = [Path(f).resolve() for f in paths.split(",")]
        variants.append((label, files[0], files[1] if len(files) > 1 else None))
        del args[i:i + 2]
    if "--runs" in args:
        i = args.index("--runs")
        runs = int(args[i + 1])
        del args[i:i + 2]
    if not variants:
        variants = [("tree", corpus.NEWSPEAK / "Ampleforth.ns", None)]
    work = Path(args[0]).resolve()
    work.mkdir(parents=True, exist_ok=True)
    doc = Path(args[1]).resolve()
    name = args[2] if len(args) > 2 else doc.stem
    outer = work / "Outer.zip"
    outer_zip(outer, doc, name)
    for label, documents, docs in variants:
        snapshot = f"EmmanuelLiveness-{label}.vfuel"
        build(snapshot, documents, docs)
        for scenario in ("editor", "viewer", "viewers"):
            for k in range(runs):
                out = run(work, snapshot, doc, name, outer, scenario)
                keys = re.search(r"^KEYS sync (.*) \| settled (.*)$", out, re.M)
                outlets = re.search(r"^OUTLETS (.*)$", out, re.M)
                typed = re.search(r"^TYPED (.*)$", out, re.M)
                errors = [l for l in out.splitlines() if l.startswith("EXCEPTION")]
                if not keys:
                    print(f"{label:10} {scenario:8} FAILED\n{out}")
                    continue
                sync = [int(x) for x in keys.group(1).split()]
                settled = [int(x) for x in keys.group(2).split()]
                print(f"{label:10} {scenario:8} outlets {outlets.group(1) if outlets else '?':>3}  "
                      f"keystroke median {statistics.median(sync):6.0f} ms (settled {statistics.median(settled):6.0f})  "
                      f"all {' '.join(map(str, sync))}  typed {typed.group(1) if typed else '?'}"
                      + (f"  {len(errors)} exceptions" if errors else ""), flush=True)


if __name__ == "__main__":
    main()
