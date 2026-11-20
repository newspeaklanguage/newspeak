"""Generate library/tests/library-cases.tsv and library/tests/library-host.spectec.

Run from emmanuel/spectec:
  python3 library/tests/gen_library.py library/tests/library-cases.tsv library/tests/library-host.spectec

The fixture host parser is a table; its entries are derived here by a small
parser for the restricted code the tests use (unary and keyword sends whose
arguments are the constants of CONST or markup literals, separated by ". ",
no comments, no escapes). Expected trees, errors, and printed sources are
hand-written, never computed.
"""
import re
import sys

ESC = {'\\': '\\\\', '\n': '\\n', '\t': '\\t', '\r': '\\r'}
def q(ch): return '"%s"' % ESC.get(ch, ch)
def chars(s): return ' '.join(q(c) for c in s) if s else 'eps'
def sp(i, j): return '(SPAN %d %d)' % (i, j)
def seq(*xs): return '(%s)' % ' '.join(xs) if xs else '(eps)'

# Host constants: code text -> id of $const in tests/host-eval-fixtures.spectec.
CONST = {"#intro": 1001, "'x := 1'": 1002, "#smalltalk": 1003, "'<hr>'": 1004,
         "nil": 1005, "#fig": 1006, "'Hamlet'": 1007, "#plot": 1008,
         "aClosure": 5}
OPEN, CLOSE = '[\\', '\\]'
SRCNAME = ['doc']   # the source being parsed, recorded in every literal

# ---- Deriving the fixture host parser from sources.
host = []
def H(pieces, result):
    if (pieces, result) not in host: host.append((pieces, result))

def parse_bracket(src, i):
    """src[i:] starts just after an opening [\\ of a message bracket. Registers
    the bracket with the host table; returns (stmts, index after \\])."""
    pieces, stmts, cur = [], [], None   # cur: [start, end, keywords, args]
    seg_start, j = i, i
    def flush_src(end):
        if end > seg_start:
            pieces.append('(HSRC (%s) %s)' % (chars(src[seg_start:end]), sp(seg_start, end)))
    def finish():
        nonlocal cur
        if cur:
            start, end, kws, args = cur
            stmts.append('(SEND (eps) "%s" %s %s)' % (''.join(kws), seq(*args), sp(start, end)))
            cur = None
    while True:
        if src.startswith(CLOSE, j):
            flush_src(j); finish(); break
        c = src[j]
        if c == ' ':
            j += 1; continue
        if src.startswith('. ', j) or (c == '.' and src.startswith(CLOSE, j + 1)):
            finish(); j += 1; continue
        if src.startswith(OPEN, j):                      # a markup literal argument
            flush_src(j)
            lit, k = parse_literal(src, j)
            pieces.append('(HHOLE %s)' % lit)
            cur[3].append('(HOSTEXPR 1 (%s))' % lit); cur[1] = k
            seg_start = j = k; continue
        m = re.compile(r"'[^']*'|#\w+|nil|\w+:|\w+").match(src, j)
        assert m, (src, j)
        tokn = m.group(0)
        if tokn.endswith(':'):
            if cur is None: cur = [j, m.end(), [], []]
            cur[2].append(tokn); cur[1] = m.end()
        elif tokn in CONST:
            cur[3].append('(HOSTEXPR %d eps)' % CONST[tokn]); cur[1] = m.end()
        else:
            assert cur is None, (src, j)
            cur = [j, m.end(), [tokn], []]
        j = m.end()
    H(' '.join(pieces), 'STMTS %s' % seq(*stmts))
    return stmts, j + 2

def parse_literal(src, i):
    """src[i:] starts with the [\\ of a markup literal; returns its AST and the
    index after its \\]."""
    j, nodes, text_start = i + 2, [], i + 2
    while True:
        if src.startswith(CLOSE, j):
            if j > text_start:
                nodes.append('(FINAL (%s) %s)' % (chars(src[text_start:j]), sp(text_start, j)))
            return '(MARKUP "%s" %s %s)' % (SRCNAME[0], seq(*nodes), sp(i, j + 2)), j + 2
        if src.startswith(OPEN, j):
            text = src[text_start:j]
            stmts, k = parse_bracket(src, j + 2)
            nodes.append('(BLOCK %s %s %s %s)' % ('(%s)' % chars(text) if text else '(eps)',
                                                   sp(text_start, j), seq(*stmts), sp(text_start, k)))
            j = text_start = k; continue
        assert src[j] != '\\', 'no escapes in library tests'
        j += 1

def register(src):
    j = 0
    while True:
        k = src.find(OPEN, j)
        if k < 0: return
        _, j = parse_bracket(src, k + 2)

# ---- Expected values, hand-written, with every span erased.
Z = '(SPAN 0 0)'
def S(sel, *args): return '(SEND (eps) "%s" %s %s)' % (sel, seq(*args), Z)
def C(code): return '(HOSTEXPR %d eps)' % CONST[code]
def MK(*nodes): return '(MARKUP "doc" %s %s)' % (seq(*nodes), Z)
def LIT(*nodes): return '(HOSTEXPR 1 (%s))' % MK(*nodes)
def FIN(u): return '(FINAL (%s) %s)' % (chars(u), Z)
def BLK(u, *stmts): return '(BLOCK %s %s %s %s)' % ('(%s)' % chars(u) if u else '(eps)', Z, seq(*stmts), Z)
def st(name, *vals): return '(STATE "%s" %s)' % (name, seq(*vals) if vals else 'eps')
def T(state, items, msgs, flag='CLOSED'): return '(TREE %s %s %s %s)' % (state, seq(*items), seq(*msgs), flag)
def run(u): return '(RUN (%s) %s)' % (chars(u), Z)
def stray(u): return '(STRAY (%s) %s)' % (chars(u), Z)
def sub(t): return '(SUB %s)' % t
def mut(s): return '(MUT %s)' % s
def dnu(s): return '(DNU %s)' % s
def refused(s): return '(REFUSED %s)' % s
def strv(u): return '(STRV %s)' % seq(chars(u))
def sym(x): return strv(x)   # a symbol #x is the string literal 'x'
NIL = 'NILV'
def inline(u):
    """The tree value of the literal [\\u\\]: a single run."""
    return '(TREEV %s %s)' % (MK(FIN(u)), T(st('inline'), [run(u)], []))
def para(*items, closer=True):
    return sub(T(st('para'), list(items), [S('paragraph')] + ([S('endParagraph')] if closer else [])))
def simple(name, opener, closer, *items, flag='CLOSED'):
    return sub(T(st(name), list(items), [S(opener)] + ([S(closer)] if closer else []), flag))
def doc(fields, items, msgs=()): return T(st('doc', *fields), items, list(msgs))
DOCF = (NIL, NIL, NIL)   # title, subtitle, background; no authors

rows = []
def rel(name, relation, query, expected, truth='true'):
    rows.append((name, 'relation', relation, query + ' => (' + expected + ')', truth))
def tree(name, src, expected):
    register(src); rel(name, 'LibTree', '(HOSTSTATE 0, %s)' % chars(src), expected)
def errors(name, src, lib, core):
    register(src); rel(name, 'LibErrors', '(HOSTSTATE 0, %s)' % chars(src), '%s, %s' % (seq(*lib), seq(*core)))
def roundtrip(name, src, printed):
    register(src); register(printed)
    rel(name, 'LibRoundTrip', '(HOSTSTATE 0, %s)' % chars(src), '%s, true, true' % chars(printed))

rows.append('# The standard library (Section 6). Trees are compared in canonical form.')

# Title, author, and nested sections.
W1 = ("[\\title: [\\Hamlet\\]. author: 'Hamlet'\\][\\section: #intro\\][\\paragraph\\]To be."
      "[\\endParagraph. section: #plot\\][\\paragraph\\]Or not.[\\endParagraph. endSection. endSection\\]")
s_title = S('title:', LIT(FIN('Hamlet'))); s_author = S('author:', C("'Hamlet'"))
sec2 = sub(T(st('section', '(INTV 2)', sym('plot'), NIL), [para(run('Or not.'))],
             [S('section:', C('#plot')), S('endSection')]))
sec1 = sub(T(st('section', '(INTV 1)', sym('intro'), NIL), [para(run('To be.')), sec2],
             [S('section:', C('#intro')), S('endSection')]))
tree('lib-sections', W1, doc((inline('Hamlet'), NIL, NIL, strv('Hamlet')), [mut(s_title), mut(s_author), sec1],
                             [s_title, s_author]))
roundtrip('lib-sections-roundtrip', W1,
          "[\\title: [\\Hamlet\\]\\][\\author: 'Hamlet'\\][\\section: #intro\\][\\paragraph\\]To be.[\\endParagraph\\]"
          "[\\section: #plot\\][\\paragraph\\]Or not.[\\endParagraph\\][\\endSection\\][\\endSection\\]")

# The table of the design notes.
W2 = ("[\\table. headerRow. cell\\]Act[\\endCell. cell\\]Scenes[\\endCell. endRow\\]\n"
      "[\\row. cell\\]I[\\endCell. cell\\]5[\\endCell. endRow\\]\n[\\endTable\\]")
def cell(*items, flag='CLOSED'): return simple('cell', 'cell', 'endCell', *items, flag=flag)
tbl = sub(T(st('table', NIL), [
    simple('headerRow', 'headerRow', 'endRow', cell(run('Act')), cell(run('Scenes'))),
    simple('row', 'row', 'endRow', cell(run('I')), cell(run('5')))], [S('table'), S('endTable')]))
tree('lib-table', W2, doc(DOCF, [tbl]))
roundtrip('lib-table-roundtrip', W2,
          "[\\table\\][\\headerRow\\][\\cell\\]Act[\\endCell\\][\\cell\\]Scenes[\\endCell\\][\\endRow\\]"
          "[\\row\\][\\cell\\]I[\\endCell\\][\\cell\\]5[\\endCell\\][\\endRow\\][\\endTable\\]")

# Cells: the shorthand is trimmed; flow content drops layout; mixing is rejected.
W3 = ("[\\table. row. cell\\] x [\\endCell. cell\\] [\\paragraph\\]y[\\endParagraph\\] "
      "[\\endCell. cell\\]x[\\paragraph\\]y[\\endParagraph. endCell. endRow. endTable\\]")
mixed = T(st('cell'), [run('x'), para(run('y'))], [S('cell'), S('endCell')], 'REJECTED')
tree('lib-cells', W3, doc(DOCF, [sub(T(st('table', NIL), [simple('row', 'row', 'endRow',
    cell(run('x')), cell(para(run('y'))), sub(mixed))], [S('table'), S('endTable')]))]))
errors('lib-cells-errors', W3, ['(REJECTEDBLOCK %s)' % seq(S('cell'), S('endCell'))],
       ['(REJECTEDBLOCK %s)' % seq(S('cell'), S('endCell'))])
roundtrip('lib-cells-roundtrip', W3,
          "[\\table\\][\\row\\][\\cell\\]x[\\endCell\\][\\cell\\][\\paragraph\\]y[\\endParagraph\\][\\endCell\\]"
          "[\\cell\\]x[\\paragraph\\]y[\\endParagraph\\][\\endCell\\][\\endRow\\][\\endTable\\]")

# Lists: items hold flow content; each list has its own closer.
W4 = ("[\\list. item. paragraph\\]a[\\endParagraph. endItem. endList. numberedList. item\\]b"
      "[\\endItem. endList. endNumberedList\\]")
tree('lib-lists', W4, doc(DOCF, [
    simple('list', 'list', 'endList', simple('item', 'item', 'endItem', para(run('a')))),
    simple('numbered', 'numberedList', 'endNumberedList',
           simple('item', 'item', 'endItem', stray('b')), dnu(S('endList')))]))

# Refusals: a second title, a bad argument, a relabelled section.
W5 = ("[\\title: [\\A\\]. title: [\\B\\]. subtitle: nil. section: #intro. label: #fig. "
      "label: 'x := 1'. label: #plot\\][\\endSection\\]")
s_ta, s_tb, s_sub = S('title:', LIT(FIN('A'))), S('title:', LIT(FIN('B'))), S('subtitle:', C('nil'))
s_l1, s_l2, s_l3 = S('label:', C('#fig')), S('label:', C("'x := 1'")), S('label:', C('#plot'))
sec5 = sub(T(st('section', '(INTV 1)', sym('intro'), sym('fig')), [mut(s_l1), refused(s_l2), refused(s_l3)],
             [S('section:', C('#intro')), s_l1, S('endSection')]))
tree('lib-refusals', W5, doc((inline('A'), NIL, NIL), [mut(s_ta), refused(s_tb), refused(s_sub), sec5], [s_ta]))
leaf = lambda s: '(ERRORLEAF (REFUSED %s))' % s
errors('lib-refusals-errors', W5, [leaf(s_tb), leaf(s_sub), leaf(s_l2), leaf(s_l3)],
       [leaf(s_tb), leaf(s_sub), leaf(s_l2), leaf(s_l3)])
roundtrip('lib-refusals-roundtrip', W5,
          "[\\title: [\\A\\]\\][\\title: [\\B\\]\\][\\subtitle: nil\\][\\section: #intro\\][\\label: #fig\\]"
          "[\\label: 'x := 1'\\][\\label: #plot\\][\\endSection\\]")

# A taken title is refused without interpreting its argument; a label must be a string.
W5b = "[\\title: [\\A\\]. title: nil. section: #intro. label: nil\\][\\endSection\\]"
s_tf, s_lx = S('title:', C('nil')), S('label:', C('nil'))
sec5b = sub(T(st('section', '(INTV 1)', sym('intro'), NIL), [refused(s_lx)],
              [S('section:', C('#intro')), S('endSection')]))
tree('lib-refusal-args', W5b, doc((inline('A'), NIL, NIL), [mut(s_ta), refused(s_tf), sec5b], [s_ta]))

# Displays, a figure, and a quote.
W6 = ("[\\verbatim: 'x := 1'. codeBlock: 'x := 1'. codeBlock: 'x := 1' language: #smalltalk. html: nil. "
      "figure. html: '<hr>'. caption: [\\A plot\\]. label: #plot. endFigure. quote. attribution: [\\Hamlet\\]. "
      "paragraph\\]To be.[\\endParagraph. endQuote\\]")
def leafb(s, state): return sub(T(state, [], [s]))
s_v, s_c1 = S('verbatim:', C("'x := 1'")), S('codeBlock:', C("'x := 1'"))
s_c2, s_h1 = S('codeBlock:language:', C("'x := 1'"), C('#smalltalk')), S('html:', C('nil'))
s_h2, s_cap, s_lab = S('html:', C("'<hr>'")), S('caption:', LIT(FIN('A plot'))), S('label:', C('#plot'))
s_att = S('attribution:', LIT(FIN('Hamlet')))
fig = sub(T(st('figure', inline('A plot'), sym('plot')),
            [leafb(s_h2, st('html', strv('<hr>'))), mut(s_cap), mut(s_lab)],
            [S('figure'), s_cap, s_lab, S('endFigure')]))
quote = sub(T(st('quote', inline('Hamlet')), [mut(s_att), para(run('To be.'))],
              [S('quote'), s_att, S('endQuote')]))
tree('lib-displays', W6, doc(DOCF, [
    leafb(s_v, st('verbatim', strv('x := 1'))),
    leafb(s_c1, st('codeBlock', strv('x := 1'), sym('newspeak'))),
    leafb(s_c2, st('codeBlock', strv('x := 1'), sym('smalltalk'))),
    refused(s_h1), fig, quote]))
roundtrip('lib-displays-roundtrip', W6,
          "[\\verbatim: 'x := 1'\\][\\codeBlock: 'x := 1'\\][\\codeBlock: 'x := 1' language: #smalltalk\\]"
          "[\\html: nil\\][\\figure\\][\\html: '<hr>'\\][\\caption: [\\A plot\\]\\][\\label: #plot\\][\\endFigure\\]"
          "[\\quote\\][\\attribution: [\\Hamlet\\]\\][\\paragraph\\]To be.[\\endParagraph\\][\\endQuote\\]")

# Amplets: a host value (the closure of the amplet's code) is a display in
# flow content and an inline leaf in a paragraph; anything else is refused.
W6b = "[\\amplet: aClosure. paragraph\\]See [\\amplet: aClosure\\] here.[\\endParagraph. amplet: 'x := 1'\\]"
s_am, s_amx = S('amplet:', C('aClosure')), S('amplet:', C("'x := 1'"))
tree('lib-amplets', W6b, doc(DOCF, [
    leafb(s_am, st('amplet', '(HOSTV 5)')),
    para(run('See '), leafb(s_am, st('inlineAmplet', '(HOSTV 5)')), run(' here.')),
    refused(s_amx)]))
errors('lib-amplets-errors', W6b, [leaf(s_amx)], [leaf(s_amx)])
roundtrip('lib-amplets-roundtrip', W6b,
          "[\\amplet: aClosure\\][\\paragraph\\]See [\\amplet: aClosure\\] here.[\\endParagraph\\][\\amplet: 'x := 1'\\]")

# Errors inside a title are the library's to report; the core does not see them.
W7 = "[\\title: [\\x[\\endParagraph\\]\\]\\]"
errors('lib-title-errors', W7, ['(ERRORLEAF (DNU %s))' % S('endParagraph')], [])

# A closer sent to the wrong block is not understood.
W8 = "[\\paragraph\\]a [\\emphasis\\]b[\\endStrong. endEmphasis. endParagraph\\]"
tree('lib-wrong-closer', W8, doc(DOCF, [para(run('a '), simple('emph', 'emphasis', 'endEmphasis', run('b'), dnu(S('endStrong'))))]))

# Text directly in a table is stray; a section opens only in a document or section.
W9 = "[\\table\\]oops[\\endTable. quote. section: #intro\\]"
tree('lib-misplaced', W9, doc(DOCF, [simple('table', 'table', 'endTable', stray('oops')).replace('(STATE "table" eps)', '(STATE "table" (NILV))'),
                                     simple('quote', 'quote', None, dnu(S('section:', C('#intro'))), flag='UNCLOSED').replace('(STATE "quote" eps)', '(STATE "quote" (NILV))')]))
errors('lib-misplaced-errors', W9,
       ['(ERRORLEAF %s)' % stray('oops'), '(UNCLOSEDBLOCK %s)' % seq(S('quote')), '(ERRORLEAF (DNU %s))' % S('section:', C('#intro'))],
       ['(ERRORLEAF %s)' % stray('oops'), '(UNCLOSEDBLOCK %s)' % seq(S('quote')), '(ERRORLEAF (DNU %s))' % S('section:', C('#intro'))])


# ---- Editing (Section 7). Expected sources are hand-written.
CONST.update({"actTitle": 1009, "standardTitle": 1010, "'Act I'": 1011, "'y := 2'": 1012,
              "scratchTitle": 1013, "'http://x'": 1015, "'http://y'": 1016})
TEMPLATES = "standardTitle = ( ^[\\The Play\\] )"
SRCNAME[0] = 'Templates'
template_lit, _ = parse_literal(TEMPLATES, TEMPLATES.index(OPEN))
SRCNAME[0] = 'doc'
extra_defs = ['def $const(1010) = LITV %s' % template_lit]

def image(doc, templates):
    es = ['(ENTRY "doc" (%s))' % chars(doc)]
    if templates: es.append('(ENTRY "Templates" (%s))' % chars(TEMPLATES))
    return ' '.join(es)
def path(*xs): return '(%s)' % ' '.join(xs) if xs else '(eps)'
def INTO(i): return '(INTO %d)' % i
def FLD(j): return '(FIELDOF %d)' % j
def GAPP(st, i): return '(GAP %s %d)' % (st, i)
def INP(st, i, k): return '(IN %s %d %d)' % (st, i, k)
def TXTI(u): return '(ITEXT (%s) %s)' % (chars(u), Z)
def NEWS(sel): return '(ISTMT (SEND (eps) "%s" (eps) %s))' % (sel, Z)
CARET = '\u2038'   # marks the caret in a hand-written expected source
def ex(p): return p if p.startswith('(AT ') or p.startswith('(EXACT ') else '(EXACT %s)' % p
def AT(p, a): return '(AT %s (%s))' % (p, a)
def REPLACE(p, q, *items, after=()): return '(REPLACE %s %s %s (AFTERCARET %s))' % (ex(p), ex(q), seq(*items), seq(*after))
def SPLIT(p, lv): return '(SPLIT %s %d)' % (ex(p), lv)
def STYLE(p, q, x): return '(STYLE %s %s "%s")' % (ex(p), ex(q), x)
def plain(src): return src.replace(CARET, '')
def mark(src, before=None):
    """src with the caret just before the one occurrence of `before`, or at
    the end."""
    if before is None: return src + CARET
    assert src.count(before) == 1, (src, before)
    i = src.index(before)
    return src[:i] + CARET + src[i:]
def edited(src, name='doc'):
    """The expected result: the source, and the caret where it is marked;
    an unmarked source means the caret stays where it was."""
    assert src.count(CARET) <= 1
    pos = 'SAMECARET' if CARET not in src else '(CARETAT %d)' % src.index(CARET)
    return 'EDITED "%s" (%s) %s' % (name, chars(plain(src)), pos)
def refusedE(*offers): return 'REFUSEDEDIT %s' % seq(*offers)
def edit(name, doc, op, result, templates=False, out=None):
    register(doc)
    if out is not None: register(plain(out))
    rel(name, 'Edit', '(%s, "doc", HOSTSTATE 0, STATE "doc" (NILV NILV NILV), %s)'
        % (image(doc, templates), op), result)

# Links: an inline block whose target is a string; its text is inline
# content, without links. A target that is not a string is refused.
W10 = "[\\paragraph\\]See [\\link: 'http://x'\\]the [\\emphasis\\]site[\\endEmphasis. endLink\\] now.[\\endParagraph\\]"
s_lk = S('link:', C("'http://x'"))
tree('lib-links', W10, doc(DOCF, [para(run('See '),
    sub(T(st('link', strv('http://x')), [run('the '), simple('emph', 'emphasis', 'endEmphasis', run('site'))],
          [s_lk, S('endLink')])),
    run(' now.'))]))
roundtrip('lib-links-roundtrip', W10,
          "[\\paragraph\\]See [\\link: 'http://x'\\]the [\\emphasis\\]site[\\endEmphasis\\][\\endLink\\] now.[\\endParagraph\\]")
W10b = "[\\paragraph\\]a[\\link: nil\\]b[\\link: 'http://x'. link: 'http://x'\\]c[\\endLink. endParagraph\\]"
s_ln = S('link:', C('nil'))
tree('lib-link-refusals', W10b, doc(DOCF, [para(run('a'), refused(s_ln), run('b'),
    sub(T(st('link', strv('http://x')), [dnu(s_lk), run('c')], [s_lk, S('endLink')])))]))

# Underline, strikethrough, subscript, and superscript: inline styles, as
# emphasis is; each has its own closer, and they nest in links.
W11 = ("[\\paragraph\\]a[\\underline\\]b[\\endUnderline. strikethrough\\]c[\\endStrong. endStrikethrough\\]"
       "H[\\subscript\\]2[\\endSubscript\\]O[\\link: 'http://x'. superscript\\]n[\\endSuperscript. endLink. endParagraph\\]")
tree('lib-styles', W11, doc(DOCF, [para(run('a'),
    simple('underline', 'underline', 'endUnderline', run('b')),
    simple('strikethrough', 'strikethrough', 'endStrikethrough', run('c'), dnu(S('endStrong'))),
    run('H'), simple('subscript', 'subscript', 'endSubscript', run('2')), run('O'),
    sub(T(st('link', strv('http://x')), [simple('superscript', 'superscript', 'endSuperscript', run('n'))],
          [s_lk, S('endLink')])))]))
roundtrip('lib-styles-roundtrip', W11,
          "[\\paragraph\\]a[\\underline\\]b[\\endUnderline\\][\\strikethrough\\]c[\\endStrong\\][\\endStrikethrough\\]"
          "H[\\subscript\\]2[\\endSubscript\\]O[\\link: 'http://x'\\][\\superscript\\]n[\\endSuperscript\\][\\endLink\\][\\endParagraph\\]")

# A background: a string naming an image, set once, and only on the document.
W12 = ("[\\background: nil. background: 'Hamlet'. background: 'x := 1'. title: [\\A\\]\\]"
       "[\\paragraph\\]a[\\background: 'Hamlet'\\][\\endParagraph\\]")
s_bn, s_bh, s_bx = S('background:', C('nil')), S('background:', C("'Hamlet'")), S('background:', C("'x := 1'"))
tree('lib-background', W12, doc((inline('A'), NIL, strv('Hamlet')),
    [refused(s_bn), mut(s_bh), refused(s_bx), mut(s_ta), para(run('a'), dnu(s_bh))], [s_bh, s_ta]))
errors('lib-background-errors', W12, [leaf(s_bn), leaf(s_bx), '(ERRORLEAF (DNU %s))' % s_bh],
       [leaf(s_bn), leaf(s_bx), '(ERRORLEAF (DNU %s))' % s_bh])
roundtrip('lib-background-roundtrip', W12,
          "[\\background: nil\\][\\background: 'Hamlet'\\][\\background: 'x := 1'\\][\\title: [\\A\\]\\]"
          "[\\paragraph\\]a[\\background: 'Hamlet'\\][\\endParagraph\\]")

rows.append('# Editing (Section 7).')
emph_all = simple('emph', 'emphasis', 'endEmphasis', run('all'))
E1 = "[\\paragraph\\]Hi [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
P_EMPH_END = GAPP(path(INTO(0), INTO(1)), 1)
O1 = "[\\paragraph\\]Hi [\\emphasis\\]all![\\endEmphasis. endParagraph\\]"
edit('edit-type', E1, REPLACE(P_EMPH_END, P_EMPH_END, TXTI('!')), edited(mark(O1, '[\\endEmphasis')), out=O1)
edit('edit-identity', E1, REPLACE(P_EMPH_END, P_EMPH_END), edited(E1))

# Enter between "Hi" and the space splits the paragraph; Backspace joins it.
O2 = "[\\paragraph\\]Hi[\\endParagraph. paragraph\\] [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
edit('edit-split', E1, SPLIT(INP(path(INTO(0)), 0, 2), 1), edited(mark(O2, ' [\\emphasis')), out=O2)
tree('edit-split-tree', O2, doc(DOCF, [para(run('Hi')), para(emph_all)]))
edit('edit-join', O2, REPLACE(GAPP(path(INTO(0)), 1), GAPP(path(INTO(1)), 0)), edited(mark(E1, ' [\\emphasis')))

# Toggling emphasis on, and off a range that is all of an emphasis.
O4 = "[\\paragraph\\][\\emphasis\\]Hi[\\endEmphasis\\] [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
edit('edit-style-apply', E1, STYLE(GAPP(path(INTO(0)), 0), INP(path(INTO(0)), 0, 2), 'emphasis'),
     edited(mark(O4, '[\\endEmphasis\\] ')), out=O4)
tree('edit-style-apply-tree', O4, doc(DOCF, [para(simple('emph', 'emphasis', 'endEmphasis', run('Hi')), run(' '), emph_all)]))
O5 = "[\\paragraph\\]Hi all[\\endParagraph\\]"
edit('edit-style-remove', E1, STYLE(GAPP(path(INTO(0), INTO(1)), 0), P_EMPH_END, 'emphasis'),
     edited(mark(O5, '[\\endParagraph')), out=O5)
tree('edit-style-remove-tree', O5, doc(DOCF, [para(run('Hi all'))]))

O4u = "[\\paragraph\\][\\underline\\]Hi[\\endUnderline\\] [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
edit('edit-style-underline', E1, STYLE(GAPP(path(INTO(0)), 0), INP(path(INTO(0)), 0, 2), 'underline'),
     edited(mark(O4u, '[\\endUnderline\\] ')), out=O4u)
tree('edit-style-underline-tree', O4u, doc(DOCF, [para(simple('underline', 'underline', 'endUnderline', run('Hi')), run(' '), emph_all)]))

# Deleting all of an emphasis removes it rather than leaving it empty.
O6 = "[\\paragraph\\]Hi [\\endParagraph\\]"
edit('edit-delete-tidy', E1, REPLACE(GAPP(path(INTO(0), INTO(1)), 0), P_EMPH_END), edited(mark(O6, '[\\endParagraph')), out=O6)
tree('edit-delete-tidy-tree', O6, doc(DOCF, [para(run('Hi'))]))

# Deleting across two paragraphs joins them.
E7 = "[\\paragraph\\]ab[\\endParagraph\\]\n[\\paragraph\\]cd[\\endParagraph\\]"
O7 = "[\\paragraph\\]ad[\\endParagraph\\]"
edit('edit-delete-join', E7, REPLACE(INP(path(INTO(0)), 0, 1), INP(path(INTO(1)), 0, 1)), edited(mark(O7, 'd[')), out=O7)

# Typing over a selection that leaves an emphasis keeps its first half.
E8 = "[\\paragraph\\]a [\\emphasis\\]bc[\\endEmphasis\\] d[\\endParagraph\\]"
O8 = "[\\paragraph\\]a [\\emphasis\\]bX[\\endEmphasis\\]d[\\endParagraph\\]"
edit('edit-replace-across', E8, REPLACE(INP(path(INTO(0), INTO(1)), 0, 1), INP(path(INTO(0)), 2, 1), TXTI('X')),
     edited(mark(O8, '[\\endEmphasis')), out=O8)

# Inserting a paragraph's template after the last block.
E9 = "[\\paragraph\\]ab[\\endParagraph\\]"
O9 = E9 + "[\\paragraph. endParagraph\\]"
edit('edit-insert-block', E9, REPLACE(GAPP(path(), 1), GAPP(path(), 1), NEWS('paragraph'), NEWS('endParagraph')),
     edited(mark(O9)), out=O9)
tree('edit-insert-block-tree', O9, doc(DOCF, [para(run('ab')), para()]))

# Enter at the start of an emphasis: an empty paragraph, no empty emphasis.
E20 = "[\\paragraph. emphasis\\]abc[\\endEmphasis. endParagraph\\]"
O20 = "[\\paragraph\\][\\endParagraph. paragraph. emphasis\\]abc[\\endEmphasis. endParagraph\\]"
edit('edit-split-tidy', E20, SPLIT(GAPP(path(INTO(0), INTO(0)), 0), 1), edited(mark(O20, 'abc')), out=O20)
tree('edit-split-tidy-tree', O20, doc(DOCF, [para(), para(simple('emph', 'emphasis', 'endEmphasis', run('abc')))]))

# A title edited in place; a template's title edited in its method's source.
E10 = "[\\title: [\\Hamlet\\]\\][\\paragraph\\]x[\\endParagraph\\]"
O10 = "[\\title: [\\Ham-let\\]\\][\\paragraph\\]x[\\endParagraph\\]"
edit('edit-title', E10, REPLACE(INP(path(FLD(0)), 0, 3), INP(path(FLD(0)), 0, 3), TXTI('-')), edited(mark(O10, 'let')), out=O10)
E11 = "[\\title: standardTitle\\]"
edit('edit-template', E11, REPLACE(INP(path(FLD(0)), 0, 4), INP(path(FLD(0)), 0, 4), TXTI('Great ')),
     edited(mark("standardTitle = ( ^[\\The Great Play\\] )", 'Play'), 'Templates'), templates=True)
edit('edit-detach-template', E11, '(DETACH (eps) 0)', edited("[\\title: [\\The Play\\]\\]"), templates=True,
     out="[\\title: [\\The Play\\]\\]")

# Computed text: a computed string is offered detach; detaching writes it.
E12 = "[\\title: actTitle\\]"
edit('edit-string-computed', E12, '(SETSTRING (eps) 0 (%s))' % chars('Act II'),
     refusedE('(OFFERDETACH (eps) 0)', 'GIVEUP'))
edit('edit-detach', E12, '(DETACH (eps) 0)', edited("[\\title: 'Act I'\\]"), out="[\\title: 'Act I'\\]")
E14 = "[\\codeBlock: 'x := 1'\\]"
edit('edit-string', E14, '(SETSTRING (%s) 0 (%s))' % (INTO(0), chars('y := 2')),
     edited("[\\codeBlock: 'y := 2'\\]"), out="[\\codeBlock: 'y := 2'\\]")
# A link's target is its field: setting the string changes it.
edit('edit-link-target', W10, '(SETSTRING (%s) 0 (%s))' % (path(INTO(0), INTO(1))[1:-1], chars('http://y')),
     edited("[\\paragraph\\]See [\\link: 'http://y'\\]the [\\emphasis\\]site[\\endEmphasis. endLink\\] now.[\\endParagraph\\]"),
     out="[\\paragraph\\]See [\\link: 'http://y'\\]the [\\emphasis\\]site[\\endEmphasis. endLink\\] now.[\\endParagraph\\]")
E16 = "[\\title: scratchTitle\\]"
edit('edit-computed-tree', E16, REPLACE(INP(path(FLD(0)), 0, 1), INP(path(FLD(0)), 0, 1), TXTI('x')),
     refusedE('GIVEUP'))

# Styling across the end of an emphasis closes it and opens it again inside.
O8s = ("[\\paragraph\\]a [\\emphasis\\]b[\\endEmphasis. strong. emphasis\\]c[\\endEmphasis\\] "
       "[\\endStrong\\]d[\\endParagraph\\]")
edit('edit-style-across', E8, STYLE(INP(path(INTO(0), INTO(1)), 0, 1), INP(path(INTO(0)), 2, 1), 'strong'),
     edited(mark(O8s, '[\\endStrong')), out=O8s)
tree('edit-style-across-tree', O8s, doc(DOCF, [para(run('a '), simple('emph', 'emphasis', 'endEmphasis', run('b')),
     simple('strong', 'strong', 'endStrong', simple('emph', 'emphasis', 'endEmphasis', run('c')), run(' ')), run('d'))]))

# Text next to an escape: the contents are written again with every escape.
E15 = "[\\paragraph\\]a\\[b[\\endParagraph\\]"
O15 = "[\\paragraph\\]a\\\\\\[b[\\endParagraph\\]"
edit('edit-escape', E15, REPLACE(INP(path(INTO(0)), 0, 1), INP(path(INTO(0)), 0, 1), TXTI('\\')), edited(mark(O15, '\\[b')), out=O15)
tree('edit-escape-tree', O15, doc(DOCF, [para(run('a\\[b'))]))
# The same with the escape to the left of the edit.
O15L = "[\\paragraph\\]a\\[!b[\\endParagraph\\]"
edit('edit-escape-left', E15, REPLACE(INP(path(INTO(0)), 0, 2), INP(path(INTO(0)), 0, 2), TXTI('!')), edited(mark(O15L, 'b[')), out=O15L)

# A mutating message between two paragraphs is kept, so they do not join.
E17 = "[\\paragraph\\]ab[\\endParagraph. title: [\\T\\]. paragraph\\]cd[\\endParagraph\\]"
O17 = "[\\paragraph\\]a[\\endParagraph. title: [\\T\\]. paragraph\\]d[\\endParagraph\\]"
edit('edit-delete-keeps-title', E17, REPLACE(INP(path(INTO(0)), 0, 1), INP(path(INTO(2)), 0, 1)), edited(mark(O17, '[\\endParagraph. title')), out=O17)

# The examples of Section 7, checked: anchors, located text, cut
# brackets, the keys, and templates.
def anchor(name, src, pt, expected):
    register(src); rel(name, 'LibAnchor', '(%s, %s)' % (chars(src), pt), expected)
def isPoint(name, src, pt, expected):
    register(src); rel(name, 'LibIsPoint', '(%s, %s)' % (chars(src), pt), expected)
def loc(name, src, st, j, ranges):
    register(src); rel(name, 'LibLoc', '(%s, %s, %d)' % (chars(src), st, j),
                       seq(*['(RNG %d %d)' % r for r in ranges]))
def key(name, relation, src, args, expected, truth='true'):
    register(src); rel(name, relation, '(%s, %s)' % (chars(src), args), expected, truth)

P_PARA_START = GAPP(path(INTO(0)), 0)
P_HI = INP(path(INTO(0)), 0, 2)
anchor('ex-anchor-in', E1, P_HI, 'TXT 1 2')
anchor('ex-anchor-first-gap', E1, P_PARA_START, 'TXT 1 0')
anchor('ex-anchor-emph-start', E1, GAPP(path(INTO(0), INTO(1)), 0), 'TXT 2 0')
anchor('ex-anchor-emph-end', E1, P_EMPH_END, 'TXT 2 3')
anchor('ex-anchor-after-emph', E1, GAPP(path(INTO(0)), 2), 'CUT 2 1')
anchor('ex-anchor-end', E1, GAPP(path(), 1), 'ENDA')
isPoint('ex-point-in', E1, P_HI, 'true')
isPoint('ex-point-in-end', E1, INP(path(INTO(0)), 0, 3), 'false')
isPoint('ex-point-gap-last', E1, GAPP(path(INTO(0)), 2), 'true')
isPoint('ex-point-gap-past', E1, GAPP(path(INTO(0)), 3), 'false')

# Located text: white space collapses, an escape is one character.
EL = "[\\paragraph\\]  a \\[  b [\\endParagraph\\]"
loc('ex-loc', EL, path(INTO(0)), 0, [(2, 3), (3, 4), (4, 5), (5, 7), (7, 8)])
anchor('ex-loc-anchor', EL, INP(path(INTO(0)), 0, 3), 'TXT 1 5')
anchor('ex-loc-anchor-b', EL, INP(path(INTO(0)), 0, 4), 'TXT 1 7')
OL = "[\\paragraph\\]  a \\[x  b [\\endParagraph\\]"
edit('ex-loc-type', EL, REPLACE(INP(path(INTO(0)), 0, 3), INP(path(INTO(0)), 0, 3), TXTI('x')), edited(mark(OL, '  b')), out=OL)
tree('ex-loc-type-tree', OL, doc(DOCF, [para(run('a [x b'))]))

# A bracket cut by an anchor is printed again as two.
EC = "[\\paragraph\\]ab[\\endParagraph. paragraph\\]cd[\\endParagraph\\]"
anchor('ex-cut-anchor', EC, GAPP(path(), 1), 'CUT 1 1')
PARA_T = (NEWS('paragraph'), NEWS('endParagraph'))
key('ex-insert', 'LibInsert', EC, '%s, "paragraph"' % ex(GAPP(path(), 1)),
    REPLACE(GAPP(path(), 1), GAPP(path(), 1), NEWS('paragraph'), after=[NEWS('endParagraph')]))
OC = "[\\paragraph\\]ab[\\endParagraph\\][\\paragraph. endParagraph\\][\\paragraph\\]cd[\\endParagraph\\]"
edit('ex-cut', EC, REPLACE(GAPP(path(), 1), GAPP(path(), 1), *PARA_T), edited(mark(OC, '[\\paragraph\\]cd')), out=OC)
tree('ex-cut-tree', OC, doc(DOCF, [para(run('ab')), para(), para(run('cd'))]))
key('ex-insertable', 'LibInsertable', EC, '%s, "paragraph"' % GAPP(path(), 1), 'true')
key('ex-insertable-row', 'LibInsertable', EC, '%s, "row"' % GAPP(path(), 1), 'false')
key('ex-insertable-emph', 'LibInsertable', EC, '%s, "emphasis"' % GAPP(path(INTO(0)), 0), 'true')
key('ex-insertable-para', 'LibInsertable', EC, '%s, "paragraph"' % GAPP(path(INTO(0)), 0), 'false')
key('ex-insert-table', 'LibInsert', EC, '%s, "table"' % ex(GAPP(path(), 1)),
    REPLACE(GAPP(path(), 1), GAPP(path(), 1), *[NEWS(x) for x in ('table', 'row', 'cell')],
            after=[NEWS(x) for x in ('endCell', 'endRow', 'endTable')]))

# The keys: Backspace and Enter are the edits of the examples above.
key('ex-backspace', 'LibBackspace', O2, '%s, 1' % path(), REPLACE(GAPP(path(INTO(0)), 1), GAPP(path(INTO(1)), 0)))
key('ex-enter', 'LibEnter', E1, ex(P_HI), SPLIT(P_HI, 1))
key('ex-enter-emph', 'LibEnter', E1, ex(INP(path(INTO(0), INTO(1)), 0, 1)), SPLIT(INP(path(INTO(0), INTO(1)), 0, 1), 1))
# In a list item, Enter splits the item, making a new one.
EL = "[\\list. item. paragraph\\]ab[\\endParagraph. endItem. endList\\]"
P_ITEM = INP(path(INTO(0), INTO(0), INTO(0)), 0, 1)
OL = "[\\list. item. paragraph\\]a[\\endParagraph. endItem. item. paragraph\\]b[\\endParagraph. endItem. endList\\]"
key('ex-enter-item', 'LibEnter', EL, ex(P_ITEM), SPLIT(P_ITEM, 2))
edit('edit-enter-item', EL, SPLIT(P_ITEM, 2), edited(mark(OL, 'b[\\endParagraph')), out=OL)

# Typing after a leaf (a newline: only a creating message) writes after it.
NL = "[\\paragraph\\]a[\\newline\\]b[\\endParagraph\\]"
P_NL = GAPP(path(INTO(0)), 2)
ONL = "[\\paragraph\\]a[\\newline\\]Qb[\\endParagraph\\]"
edit('edit-after-leaf', NL, REPLACE(P_NL, P_NL, TXTI('Q')), edited(mark(ONL, 'b[')), out=ONL)

# Deleting a leaf whole: an amplet between paragraphs, a newline in one.
AB = "[\\paragraph\\]a[\\endParagraph\\][\\amplet: aClosure\\][\\paragraph\\]b[\\endParagraph\\]"
OAB = "[\\paragraph\\]a[\\endParagraph\\][\\paragraph\\]b[\\endParagraph\\]"
edit('edit-delete-amplet', AB, REPLACE(GAPP(path(), 1), GAPP(path(), 2)), edited(mark(OAB, '[\\paragraph\\]b')), out=OAB)
ONL2 = "[\\paragraph\\]ab[\\endParagraph\\]"
edit('edit-delete-newline', NL, REPLACE(GAPP(path(INTO(0)), 1), GAPP(path(INTO(0)), 2)), edited(mark(ONL2, 'b')), out=ONL2)

anchor('ex-anchor-before-emph', E1, GAPP(path(INTO(0)), 1), 'TXT 1 3')
# Enter inside the emphasis splits the paragraph, closing the emphasis.
OS = "[\\paragraph\\]Hi [\\emphasis\\]a[\\endEmphasis. endParagraph. paragraph. emphasis\\]ll[\\endEmphasis. endParagraph\\]"
edit('ex-split-emph', E1, SPLIT(INP(path(INTO(0), INTO(1)), 0, 1), 1), edited(mark(OS, 'll[')), out=OS)
# An edit that writes nothing keeps an empty emphasis the source has.
EE = "[\\paragraph\\]a[\\emphasis. endEmphasis\\]b[\\endParagraph\\]"
edit('edit-identity-empty', EE, REPLACE(GAPP(path(INTO(0), INTO(1)), 0), GAPP(path(INTO(0), INTO(1)), 0)), edited(EE))

# Carets (Section 7.4): a caret is a point and an anchor; after an edit it
# goes where the written text ends.
def place(name, src, a, expected):
    register(src); rel(name, 'LibPlace', '(%s, %s)' % (chars(src), a), expected)
def caretOK(name, src, ca, expected):
    register(src); rel(name, 'LibCaretOK', '(%s, %s)' % (chars(src), ca), expected)
def editCaret(name, src, op, out, pi, expected):
    register(src); register(out)
    rel(name, 'LibEditCaret', '(%s, %s, %s)' % (chars(src), op, pi), expected)

# Typing a space at the end of a paragraph: the space is trimmed, so the
# caret's anchor lies after it, past its point's.
EH = "[\\paragraph\\]Hello[\\endParagraph\\]"
OH = "[\\paragraph\\]Hello [\\endParagraph\\]"
P_HELLO_END = GAPP(path(INTO(0)), 1)
edit('caret-space', EH, REPLACE(P_HELLO_END, P_HELLO_END, TXTI(' ')), edited(mark(OH, '[\\endParagraph')), out=OH)
editCaret('caret-space-caret', EH, REPLACE(P_HELLO_END, P_HELLO_END, TXTI(' ')), OH, path(),
          AT(P_HELLO_END, 'TXT 1 6'))
# So the next character goes after the space; at the point's own anchor it
# would go before it.
OHW = "[\\paragraph\\]Hello w[\\endParagraph\\]"
edit('caret-after-space', OH, REPLACE(AT(P_HELLO_END, 'TXT 1 6'), AT(P_HELLO_END, 'TXT 1 6'), TXTI('w')),
     edited(mark(OHW, '[\\endParagraph')), out=OHW)
OHX = "[\\paragraph\\]Hellow [\\endParagraph\\]"
edit('caret-exact-trims', OH, REPLACE(P_HELLO_END, P_HELLO_END, TXTI('w')), edited(mark(OHX, ' [')), out=OHX)
caretOK('caret-ok-slack', OH, AT(P_HELLO_END, 'TXT 1 6'), 'true')
caretOK('caret-ok-shown', OH, AT(INP(path(INTO(0)), 0, 1), 'TXT 1 2'), 'false')
caretOK('caret-ok-cut', E1, AT(GAPP(path(INTO(0)), 2), 'CUT 2 1'), 'false')

# A second space collapses into the first: the caret stays before the b.
EA = "[\\paragraph\\]a b[\\endParagraph\\]"
OA = "[\\paragraph\\]a  b[\\endParagraph\\]"
editCaret('caret-collapsed', EA, REPLACE(INP(path(INTO(0)), 0, 2), INP(path(INTO(0)), 0, 2), TXTI(' ')), OA, path(),
          AT(INP(path(INTO(0)), 0, 2), 'TXT 1 3'))

# Enter: the caret starts the new paragraph, whose leading space is trimmed.
editCaret('caret-enter', E1, SPLIT(INP(path(INTO(0)), 0, 2), 1), O2, path(), AT(GAPP(path(INTO(1)), 0), 'TXT 2 0'))
# Deleting all of an emphasis: the opener and closer cancel across the
# caret, which stays where the emphasis was.
editCaret('caret-delete-emph', E1, REPLACE(GAPP(path(INTO(0), INTO(1)), 0), P_EMPH_END), O6, path(),
          AT(GAPP(path(INTO(0)), 1), 'TXT 1 3'))
# A template puts the caret inside the new block; the bracket is split there.
OCT = "[\\paragraph\\]ab[\\endParagraph\\][\\paragraph\\][\\endParagraph\\][\\paragraph\\]cd[\\endParagraph\\]"
CT = REPLACE(GAPP(path(), 1), GAPP(path(), 1), NEWS('paragraph'), after=[NEWS('endParagraph')])
edit('caret-template', EC, CT, edited(mark(OCT, '[\\endParagraph\\][\\paragraph\\]cd')), out=OCT)
editCaret('caret-template-caret', EC, CT, OCT, path(), AT(GAPP(path(INTO(1)), 0), 'TXT 3 0'))
tree('caret-template-tree', OCT, doc(DOCF, [para(run('ab')), para(), para(run('cd'))]))
# In a title: the caret is placed in the literal, below the field's path.
editCaret('caret-title', E10, REPLACE(INP(path(FLD(0)), 0, 3), INP(path(FLD(0)), 0, 3), TXTI('-')), O10, path(FLD(0)),
          AT(INP(path(FLD(0)), 0, 4), 'TXT 0 4'))

# An escape is one character of the contents: the caret after the '!'
# typed beside an escaped bracket is at offset 3 of them, not 4.
editCaret('caret-escape', E15, REPLACE(INP(path(INTO(0)), 0, 2), INP(path(INTO(0)), 0, 2), TXTI('!')), O15L, path(),
          AT(INP(path(INTO(0)), 0, 3), 'TXT 1 3'))

# Placing anchors: after the last statement, in dropped white space, and in
# white space that trimming removed.
EP = "[\\paragraph\\]ab[\\endParagraph\\]"
place('caret-place-end', EP, 'ENDA', GAPP(path(), 1))
ED = "[\\paragraph\\]a[\\endParagraph\\]  [\\paragraph\\]b[\\endParagraph\\]"
place('caret-place-dropped', ED, 'TXT 2 1', GAPP(path(), 1))
ET = "[\\paragraph\\] there[\\endParagraph\\]"
place('caret-place-lead', ET, 'TXT 1 1', GAPP(path(INTO(0)), 0))
place('caret-place-in', ET, 'TXT 1 2', INP(path(INTO(0)), 0, 1))

# ---- The view (Section 7.11): keys, typed spaces, and the edits it makes.
CONST.update({"tick": 901, "fragile": 902})
def viewed(src):
    assert src.count(CARET) <= 1
    pos = 'SAMECARET' if CARET not in src else '(CARETAT %d)' % src.index(CARET)
    return 'VIEWED (%s) %s' % (chars(plain(src)), pos)
KEPT = 'VIEWKEPT'
def KTYPE(u): return '(KTYPE (%s))' % chars(u)
def KSTYLE(x): return '(KSTYLE "%s")' % x
def view(name, doc, p, q, key, result, templates=False, out=None):
    register(doc)
    if out is not None: register(plain(out))
    rel(name, 'ViewKey', '(%s, "doc", HOSTSTATE 0, STATE "doc" (NILV NILV NILV), %s, %s, %s)'
        % (image(doc, templates), ex(p), ex(q), key), result)
def view1(name, doc, p, key, result, **kw): view(name, doc, p, p, key, result, **kw)

P0 = path(INTO(0))
VB1 = "[\\paragraph\\]H [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
view1('view-backspace-char', E1, INP(P0, 0, 2), 'KBACKSPACE', viewed(mark(VB1, ' [\\emphasis')), out=VB1)
VB2 = "[\\paragraph\\]Hi[\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
view1('view-backspace-run-end', E1, GAPP(P0, 1), 'KBACKSPACE', viewed(mark(VB2, '[\\emphasis')), out=VB2)
view1('view-backspace-inline-start', E1, GAPP(path(INTO(0), INTO(1)), 0), 'KBACKSPACE',
      viewed(mark(VB2, '[\\emphasis')), out=VB2)
view1('view-backspace-doc-start', E1, GAPP(P0, 0), 'KBACKSPACE', KEPT)
view1('view-backspace-field-start', E10, GAPP(path(FLD(0)), 0), 'KBACKSPACE', KEPT)
view1('view-delete-char', E1, INP(P0, 0, 1), 'KDELETE', viewed(mark(VB1, ' [\\emphasis')), out=VB1)
VD2 = "[\\paragraph\\]i [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
view1('view-delete-start', E1, GAPP(P0, 0), 'KDELETE', viewed(mark(VD2, 'i [')), out=VD2)
view('view-enter-selection', E1, INP(P0, 0, 1), INP(P0, 0, 2), 'KENTER', viewed(mark(VB1, ' [\\emphasis')), out=VB1)
view1('view-enter', E1, INP(P0, 0, 2), 'KENTER', viewed(mark(O2, ' [\\emphasis')), out=O2)
VN = "[\\paragraph\\]Hi[\\newline\\] [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
view1('view-newline', E1, INP(P0, 0, 2), 'KNEWLINE', viewed(mark(VN, ' [\\emphasis')), out=VN)
VT = "[\\paragraph\\]HX [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
view('view-type-over', E1, INP(P0, 0, 1), INP(P0, 0, 2), KTYPE('X'), viewed(mark(VT, ' [\\emphasis')), out=VT)
VS1 = "[\\paragraph\\]H i [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
view1('view-space-plain', E1, INP(P0, 0, 1), KTYPE(' '), viewed(mark(VS1, 'i [')), out=VS1)
VS2 = "[\\paragraph\\]Hi  [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
view1('view-space-kept', E1, INP(P0, 0, 2), KTYPE(' '), viewed(mark(VS2, ' [\\emphasis')), out=VS2)
VS3 = "[\\paragraph\\]H  Xi [\\emphasis\\]all[\\endEmphasis. endParagraph\\]"
view1('view-spaces-typed', E1, INP(P0, 0, 1), KTYPE('  X'), viewed(mark(VS3, 'i [')), out=VS3)
view1('view-style-collapsed', E1, INP(P0, 0, 1), KSTYLE('underline'), KEPT)
view('view-style', E1, GAPP(P0, 0), INP(P0, 0, 2), KSTYLE('underline'), viewed(mark(O4u, '[\\endUnderline\\] ')), out=O4u)

EB = "[\\paragraph\\]a [\\emphasis\\]bc[\\endEmphasis\\]d[\\endParagraph\\]"
VBI = "[\\paragraph\\]a [\\emphasis\\]b[\\endEmphasis\\]d[\\endParagraph\\]"
view1('view-backspace-into', EB, GAPP(P0, 2), 'KBACKSPACE', viewed(mark(VBI, '[\\endEmphasis')), out=VBI)
VDI = "[\\paragraph\\]a [\\emphasis\\]bc[\\endEmphasis\\][\\endParagraph\\]"
view1('view-delete-inline-end', EB, GAPP(path(INTO(0), INTO(1)), 1), 'KDELETE',
      viewed(mark(VDI, '[\\endParagraph')), out=VDI)
EL = "[\\paragraph\\]a[\\amplet: aClosure\\]b[\\endParagraph\\]"
VL = "[\\paragraph\\]ab[\\endParagraph\\]"
view1('view-backspace-leaf', EL, GAPP(P0, 2), 'KBACKSPACE', viewed(mark(VL, 'b[')), out=VL)
view1('view-delete-leaf', EL, GAPP(P0, 1), 'KDELETE', viewed(mark(VL, 'b[')), out=VL)
EA = "[\\paragraph\\]a[\\endParagraph\\][\\amplet: aClosure\\][\\paragraph\\]b[\\endParagraph\\]"
VA = "[\\paragraph\\]a[\\endParagraph\\][\\paragraph\\]b[\\endParagraph\\]"
view1('view-backspace-leaf-block', EA, GAPP(path(INTO(2)), 0), 'KBACKSPACE',
      viewed(mark(VA, '[\\paragraph\\]b')), out=VA)
view1('view-delete-leaf-block', EA, GAPP(P0, 1), 'KDELETE', viewed(mark(VA, '[\\paragraph\\]b')), out=VA)
VJ = "[\\paragraph\\]abcd[\\endParagraph\\]"
view1('view-backspace-join', E7, GAPP(path(INTO(1)), 0), 'KBACKSPACE', viewed(mark(VJ, 'cd')), out=VJ)
view1('view-delete-join', E7, GAPP(P0, 1), 'KDELETE', viewed(mark(VJ, 'cd')), out=VJ)
view1('view-template-elsewhere', E11, INP(path(FLD(0)), 0, 4), KTYPE('Great '), KEPT, templates=True)
EF = "[\\paragraph\\]a[\\amplet: tick\\][\\amplet: fragile\\]b[\\endParagraph\\]"
view1('view-raises', EF, GAPP(P0, 2), 'KBACKSPACE', KEPT,
      out="[\\paragraph\\]a[\\amplet: fragile\\]b[\\endParagraph\\]")

# Refusals with nothing to offer.
edit('edit-two-trees', E10, REPLACE(INP(path(FLD(0)), 0, 1), GAPP(path(), 1)), refusedE('GIVEUP'))
edit('edit-split-unclosed', "[\\paragraph\\]abc", SPLIT(INP(path(INTO(0)), 0, 1), 1), refusedE('GIVEUP'))
edit('edit-style-flow', E7, STYLE(INP(path(INTO(0)), 0, 1), INP(path(INTO(1)), 0, 1), 'emphasis'),
     refusedE('GIVEUP'))

with open(sys.argv[2], 'w') as f:
    f.write(';; Generated by library/tests/gen_library.py. The fixture host parser for\n')
    f.write(';; the library regressions: a finite table of their brackets. Non-normative.\n\n')
    for pieces, result in host:
        f.write('def $hostParse(%s) = %s\n' % (pieces, result))
    for d in extra_defs:
        f.write(d + '\n')

with open(sys.argv[1], 'w') as f:
    f.write('# name\tkind\ttype-or-relation\tquery\texpected\n')
    for r in rows:
        f.write((r if isinstance(r, str) else '\t'.join(r)) + '\n')
