#!/usr/bin/env python3
"""Repair Ampleforth document class bodies that the psoup parser accepted but the
declarative grammar rejects, by round-tripping each one through the pretty printer.

Background. A document's Newspeak source lives in the `classBody` attribute of its
HTML. The IDE's pretty printer normalises code it prints, but nothing prints what
goes into that attribute, so a syntax error typed once is copied forward by every
clone of the document. primordialsoup's predictive parser accepts some malformed
source (notably a tuple whose elements are not separated by periods); the
combinatorial parser built from the declarative grammar - which is what the
NS->JS platform uses - correctly rejects it. Such a document loads on psoup and
fails to load on the JS platform.

What this does, per document: extract the classBody, wrap it as a compilation unit
exactly the way Documents>>createDocumentSubclassNamed:body: does, pretty print it,
verify the result parses under BOTH parsers, strip the wrapper back off and write
the body back. Documents that already parse are left untouched, so working
artefacts are not churned.

Usage:
    tool/fix-classbody-syntax.py [--apply] [--backup-dir DIR] [PATH ...]

Default is a dry run: it reports what it would change and changes nothing.
"""
import argparse, hashlib, html, io, os, re, shutil, subprocess, sys, tempfile, zipfile
from html.parser import HTMLParser

NEWSPEAK = '/Users/gbracha/newspeak/dev/web/newspeak'
PSOUP    = '/Users/gbracha/newspeak/dev/web/primordialsoup'
TOOL     = os.path.join(NEWSPEAK, 'tool')
COMB     = os.path.join(PSOUP, 'out/snapshots/CombParseCheck.vfuel')
VM       = os.path.join(PSOUP, 'out/ReleaseX64/primordialsoup')

ATTR = re.compile(r'(classBody\s*=\s*")([^"]*)(")', re.S)
NAME = re.compile(r'name\s*=\s*"([^"]*)"')

def wrap(name, body):
    """Exactly the source Documents>>createDocumentSubclassNamed:body: compiles,
    as a three-line unit: the printer treats line 1 as the unit header."""
    return ("Newspeak3\n'Uncategorized'\npublic class %s contents: c <String> = "
            "Document named: #%s contents: c %s" % (name, name, body))

def unwrap(printed):
    """Take everything from the first top-level '(' - the instance initializer -
    which is precisely what the classBody attribute holds."""
    i, n, depth = 0, len(printed), 0
    while i < n:
        c = printed[i]
        if c == "'":
            i += 1
            while i < n:
                if printed[i] == "'":
                    if i + 1 < n and printed[i+1] == "'": i += 2; continue
                    break
                i += 1
        elif c == '"':
            i += 1
            while i < n and printed[i] != '"': i += 1
        elif c == '(' and i + 1 < n and printed[i+1] == '*':
            d = 1; i += 2
            while i < n and d > 0:
                if printed[i] == '(' and i+1 < n and printed[i+1] == '*': d += 1; i += 2; continue
                if printed[i] == '*' and i+1 < n and printed[i+1] == ')': d -= 1; i += 2; continue
                i += 1
            continue
        elif c == '(':
            return printed[i:].rstrip() + '\n'
        i += 1
    return None

def comb_ok(path):
    r = subprocess.run([VM, COMB, path], capture_output=True, text=True, timeout=180)
    return 'COMB PARSE OK' in r.stdout, r.stdout.strip().split('\n')[0]

def pretty(path):
    r = subprocess.run(['./pretty-print.sh', path, path], cwd=TOOL,
                       capture_output=True, text=True, timeout=300)
    return r.returncode == 0

def roundtrip_ok(path):
    r = subprocess.run(['./round-trip-check.sh', path], cwd=TOOL,
                       capture_output=True, text=True, timeout=300)
    return r.stdout.strip().startswith('OK:') or '\nOK:' in r.stdout


FOREACH = re.compile(r'forEach:\s*\[\s*:(\w+)\s*(?:<[^>]*>)?\s*:(\w+)\s*(?:<[^>]*>)?\s*\|')

def block_end(text, open_idx):
    """Index just past the ']' closing the block that starts at open_idx ('['),
    honouring strings, character literals and nested comments."""
    i, n, depth = open_idx, len(text), 0
    while i < n:
        c = text[i]
        if c == "'":
            i += 1
            while i < n:
                if text[i] == "'":
                    if i + 1 < n and text[i+1] == "'": i += 2; continue
                    break
                i += 1
        elif c == '"':
            i += 1
            while i < n and text[i] != '"': i += 1
        elif c == '(' and i + 1 < n and text[i+1] == '*':
            d = 1; i += 2
            while i < n and d > 0:
                if text[i] == '(' and i+1 < n and text[i+1] == '*': d += 1; i += 2; continue
                if text[i] == '*' and i+1 < n and text[i+1] == ')': d -= 1; i += 2; continue
                i += 1
            continue
        elif c == '[': depth += 1
        elif c == ']':
            depth -= 1
            if depth == 0: return i + 1
        i += 1
    return n

def retarget_foreach(body, report):
    """JSZip forEach hands the block (relativePath, entry). psoup's expat bridge
    delivers the LAST argument to every parameter, so code that reads a property
    off the FIRST parameter works there and only there; NS2JS passes true order.
    Reading from the second parameter is correct on both. See Documents.ns's own
    loader, which reads zo and says the path argument 'is not working as specified'."""
    out = body; n = 0
    while True:
        m = FOREACH.search(out)
        found = False
        for m in FOREACH.finditer(out):
            first, second = m.group(1), m.group(2)
            br = out.rindex('[', m.start(), m.end())
            end = block_end(out, br)
            block = out[br:end]
            pat = re.compile(r'\b' + re.escape(first) + r'(\s+at:)')
            new_block, k = pat.subn(second + r'\1', block)
            if k:
                report(f"    forEach: reads '{first}' -> '{second}' ({k} site{'s' if k>1 else ''})")
                out = out[:br] + new_block + out[end:]
                n += k; found = True
                break
        if not found: return out, n

class Finder(HTMLParser):
    def __init__(self): super().__init__(convert_charrefs=True); self.found = False
    def handle_starttag(self, tag, attrs):
        if 'classbody' in dict(attrs): self.found = True

def repair_html(text, label, report, foreach=False):
    """Returns (new_text, status). status in {'clean','fixed','failed','skip'}"""
    m = ATTR.search(text)
    if not m: return text, 'skip'
    raw_body = m.group(2)
    body = html.unescape(raw_body)
    forced = False
    if foreach:
        body2, k = retarget_foreach(body, report)
        if k: body, forced = body2, True
    nm = NAME.search(text)
    name = (nm.group(1) if nm else 'Doc').strip() or 'Doc'
    if not re.match(r'^[A-Za-z_][A-Za-z0-9_]*$', name): name = 'Doc'
    with tempfile.TemporaryDirectory() as td:
        src = os.path.join(td, 'Unit.ns')
        open(src, 'w').write(wrap(name, body))
        ok, msg = comb_ok(src)
        if ok and not forced:
            return text, 'clean'
        if ok and forced:
            if not pretty(src): report("    pretty-print FAILED"); return text, 'failed'
            ok2, msg2 = comb_ok(src)
            if not ok2: report(f"    broken by the rewrite: {msg2}"); return text, 'failed'
            nb = unwrap(open(src).read())
            if nb is None: report("    could not locate class body"); return text, 'failed'
            return text[:m.start(2)] + nb.replace('"','&quot;') + text[m.end(2):], 'fixed'
        report(f"    parses only on psoup: {msg}")
        if not pretty(src):
            report("    pretty-print FAILED"); return text, 'failed'
        ok2, msg2 = comb_ok(src)
        if not ok2:
            report(f"    still bad after printing: {msg2}"); return text, 'failed'
        if not roundtrip_ok(src):
            report("    round-trip check failed after printing"); return text, 'failed'
        new_body = unwrap(open(src).read())
        if new_body is None:
            report("    could not locate the class body in printed output"); return text, 'failed'
    escaped = new_body.replace('"', '&quot;')
    return text[:m.start(2)] + escaped + text[m.end(2):], 'fixed'

def process_zip(path, apply, backup_dir, report, foreach=False):
    z = zipfile.ZipFile(path)
    entries = []; changed = False; stats = {'clean':0,'fixed':0,'failed':0,'skip':0}
    for info in z.infolist():
        data = z.read(info.filename)
        if info.filename.endswith('.html'):
            text = data.decode('utf-8', 'replace')
            new, st = repair_html(text, f"{path}!{info.filename}", report, foreach)
            stats[st] += 1
            if st == 'fixed':
                report(f"    FIXED {info.filename}"); data = new.encode('utf-8'); changed = True
        elif info.filename.endswith('.zip'):
            inner = zipfile.ZipFile(io.BytesIO(data))
            ients = []; ichanged = False
            for ii in inner.infolist():
                idata = inner.read(ii.filename)
                if ii.filename.endswith('.html'):
                    text = idata.decode('utf-8', 'replace')
                    new, st = repair_html(text, f"{path}!{info.filename}!{ii.filename}", report, foreach)
                    stats[st] += 1
                    if st == 'fixed':
                        report(f"    FIXED {info.filename}!{ii.filename}")
                        idata = new.encode('utf-8'); ichanged = True
                ients.append((ii, idata))
            if ichanged:
                buf = io.BytesIO()
                with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as out:
                    for ii, idata in ients: out.writestr(ii, idata)
                data = buf.getvalue(); changed = True
        entries.append((info, data))
    if changed and apply:
        if backup_dir:
            os.makedirs(backup_dir, exist_ok=True)
            shutil.copy2(path, os.path.join(backup_dir, os.path.basename(path) + '.bak'))
        tmp = path + '.tmp'
        with zipfile.ZipFile(tmp, 'w', zipfile.ZIP_DEFLATED) as out:
            for info, data in entries: out.writestr(info, data)
        os.replace(tmp, path)
    return changed, stats

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('paths', nargs='*')
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('--backup-dir')
    ap.add_argument('--foreach', action='store_true',
                    help="also retarget forEach: blocks that read the zip entry off the first parameter")
    a = ap.parse_args()
    targets = []
    for p in a.paths:
        if os.path.isdir(p):
            for dp, _, fs in os.walk(p):
                for f in fs:
                    if f.endswith('.zip'): targets.append(os.path.join(dp, f))
        elif p.endswith('.zip'): targets.append(p)
    tot = {'clean':0,'fixed':0,'failed':0,'skip':0}; touched = []
    for t in sorted(targets):
        lines = []
        rep = lambda s: lines.append(s)
        try:
            changed, stats = process_zip(t, a.apply, a.backup_dir, rep, a.foreach)
        except Exception as e:
            print(f"  {t}\n    ERROR {e}"); continue
        for k in tot: tot[k] += stats[k]
        if lines:
            print(f"  {t}"); [print(l) for l in lines]
        if changed: touched.append(t)
    print(f"\ndocuments: {tot['clean']} already valid, {tot['fixed']} repaired, "
          f"{tot['failed']} still broken, {tot['skip']} no classBody")
    print(f"archives {'rewritten' if a.apply else 'that WOULD be rewritten'}: {len(touched)}")
    for t in touched: print("   ", t)
    if not a.apply: print("\n(dry run - pass --apply to write, ideally with --backup-dir)")

if __name__ == '__main__':
    main()
