#!/usr/bin/env python3
"""List the slides whose content does not fit on the slide's canvas.

Run from tool/:
  python3 emmanuel-slide-survey.py WORKDIR [DECKDIR] [--no-build]

Opens each Telescreen presentation under DECKDIR (default
~/newspeak/dev/web/docs-emmanuel/presentations), as emmanuel-corpus-zips.py
writes them, in the IDE built with EmmanuelDeckProbeApp (out/
EmmanuelDeckProbe.vfuel; the static server must be serving out/ on
localhost:8080), in a headless Chrome with a 1440x900 window, and steps
through its slides (emmanuel-deck-probe.mjs with SURVEY set). A slide is
laid out on a canvas 1080 wide and at least 675 high; one whose content is
taller grows longer than the canvas, and one whose content is wider is cut
off. Each is listed with how much it needs.
"""
from pathlib import Path
import importlib.util
import os
import re
import subprocess
import sys
import zipfile

TOOL = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("corpus", TOOL / "emmanuel-corpus.py")
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)


def is_deck(path):
    try:
        names = zipfile.ZipFile(path).namelist()
    except zipfile.BadZipFile:
        return False
    return any(re.match(r"[^/]+/contents/[^/]+_slide_\d+\.zip$", n) for n in names)


def survey(work, deck):
    chrome = subprocess.Popen([corpus.CHROME, "--headless=new", "--disable-gpu", "--no-sandbox", "--no-first-run",
                               "--window-size=1440,900", f"--remote-debugging-port={corpus.PORT}",
                               f"--user-data-dir={work / 'chrome-profile'}", "about:blank"],
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        corpus.wait_for_chrome()
        args = [corpus.NODE, str(TOOL / "emmanuel-deck-probe.mjs"), str(corpus.PORT),
                "http://localhost:8080/primordialsoup.html?snapshot=EmmanuelDeckProbe.vfuel", str(deck), deck.stem]
        out = subprocess.run(args, capture_output=True, text=True, timeout=1200,
                             env=dict(os.environ, SURVEY="1")).stdout
    finally:
        chrome.terminate()
        chrome.wait()
    return re.findall(r"^FIT (\S+) (\d+)x(\d+) of (\d+)x(\d+)", out, re.M), out


def main():
    args = [a for a in sys.argv[1:] if a != "--no-build"]
    work = Path(args[0]).resolve()
    work.mkdir(parents=True, exist_ok=True)
    decks = Path(args[1] if len(args) > 1 else Path.home() / "newspeak/dev/web/docs-emmanuel/presentations").resolve()
    if "--no-build" not in sys.argv:
        corpus.build("EmmanuelDeckProbeApp", "EmmanuelDeckProbe.vfuel", tree=("HopscotchForHTML5.ns", "Documents.ns"))
    total = over = 0
    for deck in sorted(p for p in decks.glob("**/*.zip") if is_deck(p)):
        fits, out = survey(work, deck)
        if not fits:
            print(f"{deck.relative_to(decks)}: no slides measured")
            print("  " + out.strip().replace("\n", "\n  ")[-600:])
            continue
        bad = [(n, int(h), int(w), int(ch), int(cw)) for n, h, w, ch, cw in fits
               if int(h) > int(ch) or int(w) > int(cw)]
        total += len(fits)
        over += len(bad)
        print(f"{deck.relative_to(decks)}: {len(fits)} slides, {len(bad)} too big")
        for n, h, w, ch, cw in bad:
            print(f"  slide {n}: content {w}x{h}, slide {cw}x{ch} ({h * 100 // ch}% of its height)")
    print(f"{over} of {total} slides too big for the canvas")


if __name__ == "__main__":
    main()
