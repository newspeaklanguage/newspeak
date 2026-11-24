#!/usr/bin/env python3
"""Build Emmanuel documents from the Ampleforth document corpus.

Run from tool/:
  python3 emmanuel-corpus-zips.py WORKDIR OUTDIR [DOCS]

Converts every document under DOCS (default ~/newspeak/dev/web/docs) with
emmanuel-corpus.py (headless Chrome; the static server must be serving out/
on localhost:8080), then writes, for each zip under DOCS, a zip at the same
relative path under OUTDIR that holds the document as an Emmanuel document
(Ampleforth.ns):

  NAME/NAME.ems    the converted source
  NAME/NAME.class  the class body, from the HTML's classBody attribute
  NAME/images/, video/, audio/, classes/   copied as they are
  NAME/documents/*.zip   transcluded documents, converted the same way
  NAME/contents/   copied; the zips in it that are documents (a
                   presentation's slides) are converted the same way

A slide (a converted document laid out for page: 'slide') whose class body
is empty gets the slide template's, which interprets it with the slide
stylesheet; one with code of its own keeps it, with the template's
stylesheet method added, and is listed. A document whose conversion gives
looks (a centered title) gets a stylesheet method that adds them to its
stylesheet. The Telescreen
template is written twice: TelescreenTemplate, whose master slide
(MasterSlide) has no background, and NewspeakTelescreenTemplate, whose
NewspeakMasterSlide is on the Newspeak background.

A document the converter could not convert is copied unconverted, and
listed. DOCS is only read; OUTDIR must not be DOCS.

OUTDIR may hold documents edited since they were written. Before writing,
OUTDIR is copied whole to OUTDIR-backups/<time>/, and a zip that differs
from the one this script last wrote there (OUTDIR/.generated.json records
each one's digest) is left as it is, and listed.
"""
from pathlib import Path
import hashlib
import html
import json
import shutil
import time
import importlib.util
import io
import re
import sys
import zipfile

TOOL = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("corpus", TOOL / "emmanuel-corpus.py")
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)

LOOKS = {}  # a document's looks, as the converter gives their source
CLASS_BODY = re.compile(r'classBody\s*=\s*"([^"]*)"', re.S)
EMPTY_BODY = re.compile(r'^\(\s*\)\s*\(\s*\)(\s*:\s*\(\s*\))?$')
SLIDE_BODY = "()(public stylesheet = ( ^slideStylesheet ))"
SLIDE_PAGE = "[\\page: 'slide'\\]"
BACKGROUND = re.compile(r"\[\\background: '[^']*'\\\]")


def main_html(archive):
    """The name of a document zip's document, and its HTML, or None."""
    for entry in archive.namelist():
        parts = entry.split("/")
        if len(parts) == 2 and parts[1] == parts[0] + ".html":
            return parts[0], archive.read(entry).decode("utf-8", "replace")
    return None


def convert(key, data, sources, unconverted, custom=None):
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
    looks = LOOKS.get(key, "")
    slide = SLIDE_PAGE in sources[key]
    if slide and not looks and EMPTY_BODY.match(class_body):
        class_body = SLIDE_BODY
    elif slide or looks:
        own_code = not EMPTY_BODY.match(class_body)
        base = "slideStylesheet" if slide else "super stylesheet"
        class_body = with_stylesheet(class_body, base + (" withLooks: " + looks if looks else ""))
        if custom is not None and own_code:
            custom.append(key)
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
                data2 = convert(key + "/" + parts[2][:-4], data2, sources, unconverted, custom)
            if folder in ("images", "video", "audio", "classes", "documents", "contents"):
                z.writestr(entry, data2)
    return out.getvalue()


def instance_side(body):
    """The index just after the parenthesis that opens the instance side of
    the class body: past the header's balanced parentheses, skipping string
    literals and comments, then the next opening parenthesis."""
    i, depth, n = body.index("("), 0, len(body)
    while i < n:
        if body.startswith("(*", i):
            i = body.index("*)", i + 2) + 2
            continue
        c = body[i]
        if c == "'":
            i = body.index("'", i + 1) + 1
            continue
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                j = body.index("(", i + 1)
                if body[i + 1:j].strip():
                    raise SystemExit("unexpected text between header and instance side:\n" + body)
                return j + 1
        i += 1
    raise SystemExit("no instance side in the class body:\n" + body)


def with_stylesheet(body, expression):
    """The class body with a stylesheet method answering expression first
    on its instance side, unless it defines a stylesheet already."""
    if re.search(r"\bstylesheet\s*=", body):
        return body
    i = instance_side(body)
    return body[:i] + "\n\tpublic stylesheet = (\n\t\t^" + expression + "\n\t)" + body[i:]


def renamed(data, renames, edit=lambda path, text: text):
    """The zip data with the names renames maps (old to new) replaced in
    every entry's path, its nested zips' too, and edit applied to each text
    entry (.ems, .class) given its new path."""
    old = zipfile.ZipFile(io.BytesIO(data))
    out = io.BytesIO()
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
        for entry in old.namelist():
            path = entry
            for a, b in renames.items():
                path = path.replace(a, b)
            body = old.read(entry)
            if path.endswith(".zip"):
                body = renamed(body, renames, edit)
            elif path.endswith((".ems", ".class")):
                body = edit(path, body.decode("utf-8")).encode("utf-8")
            z.writestr(path, body)
    return out.getvalue()


def telescreen_templates(data):
    """The converted Telescreen template, as the two templates: one whose
    master slide, MasterSlide, has no background, and the Newspeak one."""
    def plain(path, text):
        if path.endswith(".ems"):
            return BACKGROUND.sub("", text)
        text = text.replace("NewspeakMasterSlide = (\n\t\t^Root at: #NewspeakMasterSlide\n\t)",
                            "MasterSlide = (\n\t\t^Root at: #MasterSlide\n\t)")
        text = text.replace("(* for now, hardwired to use the Newspeak master slide *)",
                            "(* for now, hardwired to use the master slide *)")
        return text.replace("^NewspeakMasterSlide", "^MasterSlide")
    template = renamed(data, {"NewspeakMasterSlide": "MasterSlide"}, plain)
    if b"NewspeakMasterSlide" in b"".join(zipfile.ZipFile(io.BytesIO(template)).read(n)
                                          for n in zipfile.ZipFile(io.BytesIO(template)).namelist()
                                          if n.endswith(".class")):
        raise SystemExit("the Telescreen template still names NewspeakMasterSlide")
    return {"TelescreenTemplate.zip": template,
            "NewspeakTelescreenTemplate.zip": renamed(data, {"TelescreenTemplate": "NewspeakTelescreenTemplate"})}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    work = Path(sys.argv[1]).resolve()
    out_dir = Path(sys.argv[2]).resolve()
    docs_dir = Path(sys.argv[3] if len(sys.argv) > 3 else Path.home() / "newspeak/dev/web/docs").resolve()
    if out_dir == docs_dir or docs_dir in out_dir.parents:
        raise SystemExit("OUTDIR must not be DOCS, or inside it")
    results = corpus.run(work, docs_dir)
    LOOKS.update({r["name"]: r["result"].get("looks", "") for r in results if "source" in r["result"]})
    sources = {r["name"]: r["result"]["source"] for r in results
               if "source" in r["result"] and r["result"].get("done")}
    unconverted, custom, kept = [], [], []
    manifest_path = out_dir / ".generated.json"
    manifest = json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
    if out_dir.exists():
        backup = out_dir.parent / (out_dir.name + "-backups") / time.strftime("%Y-%m-%d_%H%M%S")
        shutil.copytree(out_dir, backup)
        print("backed up", out_dir, "to", backup)
    written = {}
    for z in sorted(docs_dir.glob("**/*.zip")):
        rel = z.relative_to(docs_dir)
        converted = convert(str(rel.with_suffix("")), z.read_bytes(), sources, unconverted, custom)
        outputs = {str(rel): converted}
        if str(rel) == "TelescreenTemplate.zip":
            outputs = telescreen_templates(converted)
        for name, data in outputs.items():
            target = out_dir / name
            if target.exists() and name in manifest and digest(target.read_bytes()) != manifest[name]:
                kept.append(name)
                written[name] = manifest[name]
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            written[name] = digest(data)
    manifest_path.write_text(json.dumps(written, indent=1, sort_keys=True))
    print(f"{len(written) - len(kept)} zips written to {out_dir}; {len(unconverted)} documents left unconverted")
    for key in unconverted:
        print("  unconverted:", key)
    for key in custom:
        print("  class body of its own, given a stylesheet method:", key)
    for name in kept:
        print("  edited since it was written, so left as it is:", name)


if __name__ == "__main__":
    main()
