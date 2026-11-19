#!/usr/bin/env python3
"""Build Emmanuel documents from the Ampleforth document corpus.

Run from tool/:
  python3 emmanuel-corpus-zips.py WORKDIR OUTDIR [DOCS]

Converts every document under DOCS (default ~/newspeak/dev/web/docs) with
emmanuel-corpus.py (headless Chrome; the static server must be serving out/
on localhost:8080), then writes, for each zip under DOCS, a zip at the same
relative path under OUTDIR that holds the document as an Emmanuel document
(EmmanuelDocuments.ns):

  NAME/NAME.ems    the converted source
  NAME/NAME.class  the class body, from the HTML's classBody attribute
  NAME/images/, video/, audio/, classes/   copied as they are
  NAME/documents/*.zip   transcluded documents, converted the same way
  NAME/contents/   copied; the zips in it that are documents (a
                   presentation's slides) are converted the same way

A document the converter could not convert is copied unconverted, and
listed. DOCS is only read; OUTDIR must not be DOCS.
"""
from pathlib import Path
import html
import importlib.util
import io
import re
import sys
import zipfile

TOOL = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("corpus", TOOL / "emmanuel-corpus.py")
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)

CLASS_BODY = re.compile(r'classBody\s*=\s*"([^"]*)"', re.S)


def main_html(archive):
    """The name of a document zip's document, and its HTML, or None."""
    for entry in archive.namelist():
        parts = entry.split("/")
        if len(parts) == 2 and parts[1] == parts[0] + ".html":
            return parts[0], archive.read(entry).decode("utf-8", "replace")
    return None


def convert(key, data, sources, unconverted):
    """The Emmanuel zip of the document zip data, whose corpus name is key;
    data itself when it is not a document, or could not be converted."""
    try:
        archive = zipfile.ZipFile(io.BytesIO(data))
    except zipfile.BadZipFile:
        return data
    found = main_html(archive)
    if found is None:
        return data
    name, page = found
    if key not in sources:
        unconverted.append(key)
        return data
    m = CLASS_BODY.search(page)
    class_body = html.unescape(m.group(1)).strip() if m else "()()"
    out = io.BytesIO()
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
        for folder in ("", "contents/", "images/", "video/", "audio/", "documents/", "classes/"):
            z.writestr(name + "/" + folder, "")
        z.writestr("%s/%s.ems" % (name, name), sources[key])
        z.writestr("%s/%s.class" % (name, name), class_body)
        for entry in archive.namelist():
            parts = entry.split("/")
            if len(parts) < 3 or entry.endswith("/"):
                continue
            folder, data2 = parts[1], archive.read(entry)
            if folder in ("documents", "contents") and len(parts) == 3 and parts[2].endswith(".zip"):
                data2 = convert(key + "/" + parts[2][:-4], data2, sources, unconverted)
            if folder in ("images", "video", "audio", "classes", "documents", "contents"):
                z.writestr(entry, data2)
    return out.getvalue()


def main():
    work = Path(sys.argv[1]).resolve()
    out_dir = Path(sys.argv[2]).resolve()
    docs_dir = Path(sys.argv[3] if len(sys.argv) > 3 else Path.home() / "newspeak/dev/web/docs").resolve()
    if out_dir == docs_dir or docs_dir in out_dir.parents:
        raise SystemExit("OUTDIR must not be DOCS, or inside it")
    results = corpus.run(work, docs_dir)
    sources = {r["name"]: r["result"]["source"] for r in results
               if "source" in r["result"] and r["result"].get("done")}
    unconverted = []
    count = 0
    for z in sorted(docs_dir.glob("**/*.zip")):
        rel = z.relative_to(docs_dir)
        converted = convert(str(rel.with_suffix("")), z.read_bytes(), sources, unconverted)
        target = out_dir / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(converted)
        count += 1
    print(f"{count} zips written to {out_dir}; {len(unconverted)} documents left unconverted")
    for key in unconverted:
        print("  unconverted:", key)


if __name__ == "__main__":
    main()
