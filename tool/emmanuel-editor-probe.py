#!/usr/bin/env python3
"""Type into the Emmanuel live editor in headless Chrome and check the sources
it edits. Run from tool/:
  python3 emmanuel-editor-probe.py WORKDIR [SOURCE...]

Each SOURCE (an Emmanuel source file) is also loaded and timed: the time of
a keystroke in it.

Builds EmmanuelEditorProbeApp into out/EmmanuelEditorProbe.vfuel (with the
Emmanuel modules from the source tree, as emmanuel-corpus.py does) and runs
emmanuel-editor-probe.mjs against it; the static server must be serving out/
on localhost:8080.
"""
import importlib.util
from pathlib import Path
import subprocess
import sys

TOOL = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("corpus", TOOL / "emmanuel-corpus.py")
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)


def main():
    work = Path(sys.argv[1]).resolve()
    work.mkdir(parents=True, exist_ok=True)
    corpus.build("EmmanuelEditorProbeApp", "EmmanuelEditorProbe.vfuel", tree=("HopscotchForHTML5.ns",))
    chrome = subprocess.Popen([corpus.CHROME, "--headless=new", "--disable-gpu", "--no-sandbox", "--no-first-run",
                               f"--remote-debugging-port={corpus.PORT}", f"--user-data-dir={work / 'chrome-profile'}",
                               "about:blank"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        corpus.wait_for_chrome()
        result = subprocess.run([corpus.NODE, str(TOOL / "emmanuel-editor-probe.mjs"), str(corpus.PORT),
                                 "http://localhost:8080/primordialsoup.html?snapshot=EmmanuelEditorProbe.vfuel", *sys.argv[2:]])
    finally:
        chrome.terminate()
    sys.exit(result.returncode)


if __name__ == "__main__":
    main()
