#!/usr/bin/env python3
"""Check that a presentation in an Emmanuel document moves between slides.

Run from tool/:
  python3 emmanuel-deck-probe.py WORKDIR DECKZIP [NAME]

DECKZIP is a Telescreen presentation as an Emmanuel document zip, as
emmanuel-corpus-zips.py writes them (say docs-emmanuel/presentations/
wgld-2025/WGLD_April_2025.zip); NAME defaults to its file name. The IDE is
built with EmmanuelDeckProbeApp into out/EmmanuelDeckProbe.vfuel (the static
server must be serving out/ on localhost:8080) and run in a headless Chrome
by emmanuel-deck-probe.mjs, twice: with the presentation opened itself, and
with it in the section toggle of another Emmanuel document (WORKDIR/Outer.zip,
made here), whose viewer renders it. Each time Next is clicked three times,
and the slide shown must advance by one each time. A presenter in an amplet
used to keep its first rendering: the slide never changed.
"""
from pathlib import Path
import importlib.util
import re
import subprocess
import sys
import zipfile

TOOL = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("corpus", TOOL / "emmanuel-corpus.py")
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)

OUTER_SOURCE = "[\\paragraph\\]Before[\\endParagraph\\][\\amplet: [section: '%s' titled: 'Deck']\\]"
OUTER_CLASS = """() (
	section: name titled: t = (
		^webTransclusion: name title: t lazily: false content: (collapsed: [ (label: t) bold ] expanded: [ transclude: name ])
	)
) : ()"""


def outer_zip(path, deck, name):
    """A document whose section toggle transcludes the presentation."""
    with zipfile.ZipFile(path, "w") as z:
        for folder in ("", "contents/", "images/", "video/", "audio/", "documents/", "classes/"):
            z.writestr("Outer/" + folder, "")
        z.writestr("Outer/Outer.ems", OUTER_SOURCE % name)
        z.writestr("Outer/Outer.class", OUTER_CLASS)
        z.writestr("Outer/documents/%s.zip" % name, deck.read_bytes())


def run(work, zip_path, name, toggle=None):
    """The slides shown, at the start and after each Next."""
    chrome = subprocess.Popen([corpus.CHROME, "--headless=new", "--disable-gpu", "--no-sandbox", "--no-first-run",
                               f"--remote-debugging-port={corpus.PORT}", f"--user-data-dir={work / 'chrome-profile'}",
                               "about:blank"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        corpus.wait_for_chrome()
        args = [corpus.NODE, str(TOOL / "emmanuel-deck-probe.mjs"), str(corpus.PORT),
                "http://localhost:8080/primordialsoup.html?snapshot=EmmanuelDeckProbe.vfuel", str(zip_path), name]
        out = subprocess.run(args + ([toggle] if toggle else []), capture_output=True, text=True).stdout
    finally:
        chrome.terminate()
    print(out.rstrip())
    return [int(s) if s != "null" else None for s in re.findall(r"^SLIDE (\S+)", out, re.M)]


def main():
    work = Path(sys.argv[1]).resolve()
    work.mkdir(parents=True, exist_ok=True)
    deck = Path(sys.argv[2]).resolve()
    name = sys.argv[3] if len(sys.argv) > 3 else deck.stem
    outer = work / "Outer.zip"
    outer_zip(outer, deck, name)
    corpus.build("EmmanuelDeckProbeApp", "EmmanuelDeckProbe.vfuel", tree=("HopscotchForHTML5.ns", "Documents.ns"))
    failed = False
    for label, zip_path, doc, toggle in (("the presentation", deck, name, None),
                                         ("the presentation in a toggle", outer, "Outer", "Deck")):
        slides = run(work, zip_path, doc, toggle)
        ok = slides == [1, 2, 3, 4]
        failed = failed or not ok
        print(("PASS " if ok else "FAIL ") + label + ": slides " + " ".join(str(s) for s in slides))
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
