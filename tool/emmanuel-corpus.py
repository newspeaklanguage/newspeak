#!/usr/bin/env python3
"""Convert the Ampleforth document corpus to Emmanuel and report.

Run from tool/:
  python3 emmanuel-corpus.py WORKDIR [DOCS]

DOCS defaults to ~/newspeak/dev/web/docs. Every document there (each *.zip,
and the documents nested in its documents/ folder) is converted in a
headless Chrome by EmmanuelCorpusApp (see EmmanuelCorpusApp.ns), which is
built into out/EmmanuelCorpus.vfuel; the static server must be serving out/
on localhost:8080. WORKDIR gets the converted sources (sources/NAME.ems),
the raw results (results.json), and the report (report.md): which
constructs the library could not convert, how often and in how many
documents, which documents did not interpret cleanly, and the time of each
stage. The documents are only read.
"""
from pathlib import Path
import collections
import io
import json
import os
import shutil
import subprocess
import sys
import time
import zipfile

TOOL = Path(__file__).resolve().parent
NEWSPEAK = TOOL.parent
OUT = NEWSPEAK / "out"
PRIMORDIALSOUP = Path(os.environ.get("PRIMORDIALSOUP", NEWSPEAK.parent / "primordialsoup"))
CHROME = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
NODE = os.environ.get("NODE", "node")
PORT = 9333


def documents_in(name, data, out):
    """The documents of a zip: its top-level HTML file, and those of the
    zips in its documents/ folder."""
    try:
        archive = zipfile.ZipFile(io.BytesIO(data))
    except zipfile.BadZipFile:
        return
    for entry in archive.namelist():
        parts = entry.split("/")
        if len(parts) == 2 and parts[1].endswith(".html"):
            out.append({"name": name, "html": archive.read(entry).decode("utf-8", "replace")})
        elif len(parts) == 3 and parts[1] == "documents" and parts[2].endswith(".zip"):
            documents_in(name + "/" + parts[2][:-4], archive.read(entry), out)


def build(app="EmmanuelCorpusApp", snapshot="EmmanuelCorpus.vfuel"):
    # The Emmanuel modules come from the source tree, not from out/, which
    # may hold older copies (an IDE build copies the tree there).
    sources = [str(p) for p in sorted(OUT.glob("*.ns")) if not p.name.startswith("Emmanuel")]
    sources += [str(p) for p in sorted(NEWSPEAK.glob("Emmanuel*.ns"))]
    images = [str(p) for p in sorted(OUT.glob("*.png"))]
    target = OUT / snapshot
    subprocess.run([str(PRIMORDIALSOUP / "out/ReleaseX64/primordialsoup"),
                    str(PRIMORDIALSOUP / "out/snapshots/WebCompiler.vfuel"),
                    *sources, *images, "RuntimeForHopscotchForHTML", app, str(target)],
                   check=True, cwd=OUT)


def wait_for_chrome():
    import urllib.request
    for _ in range(300):
        try:
            urllib.request.urlopen(f"http://localhost:{PORT}/json/version", timeout=1)
            return
        except OSError:
            time.sleep(0.2)
    raise SystemExit("Chrome did not start")


def report(results, work):
    kinds = collections.Counter()
    kind_docs = collections.Counter()
    examples = {}
    unclean, failures = [], []
    stages = collections.defaultdict(list)
    for r in results:
        name, res = r["name"], r["result"]
        if "failure" in res:
            failures.append((name, res["failure"]))
            continue
        seen = set()
        for kind, detail in res["losses"]:
            kinds[kind] += 1
            seen.add(kind)
            examples.setdefault(kind, detail)
        for kind in seen:
            kind_docs[kind] += 1
        if not res["done"] or res["errors"] != 0:
            unclean.append((name, res["done"], res["errors"]))
        for stage in ("parse", "convert", "interpret"):
            stages[stage].append((res[stage], len(res["source"]), name))
        path = work / "sources" / (name.replace("/", "__") + ".ems")
        path.write_text(res["source"])
    lines = ["# Emmanuel corpus conversion", "",
             f"{len(results)} documents; {len(results) - len(failures)} converted; "
             f"{len(results) - len(failures) - len(unclean)} interpret without errors; "
             f"{len(failures)} failed.", "",
             "## What the library could not convert", "",
             "| kind | occurrences | documents | example |", "|---|---|---|---|"]
    for kind, count in kinds.most_common():
        example = str(examples[kind]).replace("|", "\\|").replace("\n", " ")[:90]
        lines.append(f"| {kind} | {count} | {kind_docs[kind]} | `{example}` |")
    lines += ["", "## Time per stage (ms)", "", "| stage | total | median | max (document, source size) |",
              "|---|---|---|---|"]
    for stage, values in stages.items():
        ms = sorted(v[0] for v in values)
        worst = max(values)
        lines.append(f"| {stage} | {sum(ms):.0f} | {ms[len(ms) // 2]:.1f} | {worst[0]:.0f} ({worst[2]}, {worst[1]} chars) |")
    if unclean:
        lines += ["", "## Documents that did not interpret cleanly", ""]
        lines += [f"- {n}: " + ("did not interpret" if not d else f"{e} errors") for n, d, e in unclean]
    if failures:
        lines += ["", "## Failures", ""]
        lines += [f"- {n}: {f[:300]}" for n, f in failures]
    (work / "report.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines[:4]))


def main():
    work = Path(sys.argv[1]).resolve()
    docs_dir = Path(sys.argv[2] if len(sys.argv) > 2 else Path.home() / "newspeak/dev/web/docs")
    (work / "sources").mkdir(parents=True, exist_ok=True)
    docs = []
    for z in sorted(docs_dir.glob("*.zip")):
        documents_in(z.stem, z.read_bytes(), docs)
    (work / "documents.json").write_text(json.dumps(docs))
    print(f"{len(docs)} documents")
    build()
    profile = work / "chrome-profile"
    chrome = subprocess.Popen([CHROME, "--headless=new", "--disable-gpu", "--no-sandbox", "--no-first-run",
                               f"--remote-debugging-port={PORT}", f"--user-data-dir={profile}", "about:blank"],
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        wait_for_chrome()
        subprocess.run([NODE, str(TOOL / "emmanuel-corpus.mjs"), str(PORT),
                        "http://localhost:8080/primordialsoup.html?snapshot=EmmanuelCorpus.vfuel",
                        str(work / "documents.json"), str(work / "results.json")], check=True)
    finally:
        chrome.terminate()
    report(json.loads((work / "results.json").read_text())["results"], work)


if __name__ == "__main__":
    main()
