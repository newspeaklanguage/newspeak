#!/usr/bin/env python3
"""Pretty-print a class body that lives inside a Newspeak string literal.

    tool/print-ns-classbody.py [--apply]

Companion to fix-classbody-syntax.py, which does the same for the classBody
attribute of stored documents. This one is for a body held as source in a .ns
file, where the pretty printer cannot reach it either.

AI_IDE_Support>>chatTemplateClassBody returns the class body every chat document
carries, as a single-quoted Newspeak string. Nothing validates it: it is not
source the compiler sees, and the pretty printer never reached it, so a mistake
typed once rides into every chat created afterwards.

Same pipeline the document tool uses -- wrap as a compilation unit exactly the
way Documents>>createDocumentSubclassNamed:body: does, print, check under both
parsers, round-trip, unwrap -- plus the two constraints this literal has that a
document attribute does not:

  * it is a single-quoted Newspeak string, so ' is doubled going back in;
  * it is emitted into classBody="..." later, so it must contain no " at all.

Dry run unless --apply is passed.
"""
import argparse, importlib.util, os, re, subprocess, sys, tempfile

NEWSPEAK = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
fxpath = os.path.join(NEWSPEAK, 'tool/fix-classbody-syntax.py')
spec = importlib.util.spec_from_file_location('fx', fxpath)
fx = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fx)

TARGET = os.path.join(NEWSPEAK, 'AI_IDE_Support.ns')
# The literal: everything between ^' and the closing ' of chatTemplateClassBody.
LITERAL = re.compile(r"(chatTemplateClassBody \^<String> = \(.*?\^')(.*?)('\n\t\))", re.S)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--apply', action='store_true')
    a = ap.parse_args()

    src = open(TARGET).read()
    m = LITERAL.search(src)
    if not m:
        sys.exit('could not locate the chatTemplateClassBody literal')
    literal = m.group(2)
    body = literal.replace("''", "'")          # undouble: Newspeak string escaping
    print('literal %d chars, body %d chars' % (len(literal), len(body)))

    with tempfile.TemporaryDirectory() as td:
        unit = os.path.join(td, 'Unit.ns')
        open(unit, 'w').write(fx.wrap('ChatTemplate', body))
        ok, msg = fx.comb_ok(unit)
        print('parses under the declarative grammar before printing:', ok, '' if ok else msg)
        if not fx.pretty(unit):
            sys.exit('pretty-print failed')
        ok2, msg2 = fx.comb_ok(unit)
        if not ok2:
            sys.exit('BROKEN BY PRINTING: ' + msg2)
        if not fx.roundtrip_ok(unit):
            sys.exit('round-trip check failed after printing')
        printed = fx.unwrap(open(unit).read())
    if printed is None:
        sys.exit('could not locate the class body in the printed output')

    if '"' in printed:
        sys.exit('printed body contains a double quote; it would truncate classBody="..."')
    new_literal = printed.replace("'", "''")   # redouble for the Newspeak string

    if new_literal == literal:
        print('already canonical; nothing to do')
        return
    print('new literal %d chars' % len(new_literal))
    out = src[:m.start(2)] + new_literal + src[m.end(2):]
    if not a.apply:
        with tempfile.TemporaryDirectory() as dd:
            a, b = os.path.join(dd, 'old'), os.path.join(dd, 'new')
            open(a, 'w').write(body)
            open(b, 'w').write(printed)
            subprocess.run(['diff', a, b])
        print('\n(dry run - pass --apply to write)')
        return
    open(TARGET, 'w').write(out)
    print('written to', TARGET)


if __name__ == '__main__':
    main()
