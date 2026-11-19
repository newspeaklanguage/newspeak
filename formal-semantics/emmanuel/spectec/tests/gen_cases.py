"""Generate tests/cases.tsv and tests/host-fixtures.spectec.

Run from emmanuel/spectec: python3 tests/gen_cases.py tests/cases.tsv tests/host-fixtures.spectec
Expected values are hand-written, never computed.
"""
import sys
ESC = {'\\': '\\\\', '\n': '\\n', '\t': '\\t', '\r': '\\r', '\x0b': '\\u{0B}', '\x0c': '\\u{0C}'}
def q(ch): return '"%s"' % ESC.get(ch, ch)
def chars(s): return ' '.join(q(c) for c in s) if s else 'eps'
def loc(lx, i, j): return '(LOC %s (SPAN %d %d))' % (lx, i, j)
def ch(c): return '(CHAR %s)' % q(c)
def code(s): return '(CODE %s)' % chars(s)
def lexed(*ls): return '(LEXED %s)' % (' '.join(ls) if ls else 'eps')
rows = []
def rel(name, rel, query, exp): rows.append((name, 'relation', rel, query, exp))
def val(name, typ, query, exp): rows.append((name, 'value', typ, query, exp))
def lexes(name, src, result, truth='true'):
    rel(name, 'Lexes', '(%s) => (%s)' % (chars(src), result), truth)

rows.append('# Lexing whole sources (Lexes / LexRun / LexStep). Every relation test')
rows.append('# also checks that exactly one derivation exists.')
lexes('lex-empty', '', lexed())
lexes('lex-plain-text', 'Hi', lexed(loc(ch('H'),0,1), loc(ch('i'),1,2)))
lexes('lex-escape-backslash', 'a\\\\b', lexed(loc(ch('a'),0,1), loc(ch('\\'),1,3), loc(ch('b'),3,4)))
lexes('lex-escape-bracket', '\\[', lexed(loc(ch('['),0,2)))
lexes('lex-text-backslash-alone', '\\x', lexed(loc(ch('\\'),0,1), loc(ch('x'),1,2)))
lexes('lex-escaped-close-is-text', '\\\\]', lexed(loc(ch('\\'),0,2), loc(ch(']'),2,3)))
lexes('lex-messages', 'x[\\f\\]', lexed(loc(ch('x'),0,1), loc('OPENMESSAGES',1,3), loc(code('f'),3,4), loc('CLOSEMESSAGES',4,6)))
lexes('lex-nested-markup', '[\\t: [\\y\\]\\]', lexed(
    loc('OPENMESSAGES',0,2), loc(code('t'),2,3), loc(code(':'),3,4), loc(code(' '),4,5),
    loc('OPENMARKUP',5,7), loc(ch('y'),7,8), loc('CLOSEMARKUP',8,10), loc('CLOSEMESSAGES',10,12)))
lexes('lex-string-hides-close', "[\\'\\]'\\]", lexed(loc('OPENMESSAGES',0,2), loc(code("'\\]'"),2,6), loc('CLOSEMESSAGES',6,8)))
lexes('lex-string-doubled-quote', "[\\'a''b'\\]", lexed(loc('OPENMESSAGES',0,2), loc(code("'a''b'"),2,8), loc('CLOSEMESSAGES',8,10)))
lexes('lex-string-then-string', "[\\'a' 'b'\\]", lexed(loc('OPENMESSAGES',0,2), loc(code("'a'"),2,5), loc(code(' '),5,6), loc(code("'b'"),6,9), loc('CLOSEMESSAGES',9,11)))
lexes('lex-nested-comment-hides-close', '[\\(*(*\\]*)*)\\]', lexed(loc('OPENMESSAGES',0,2), loc(code('(*(*\\]*)*)'),2,12), loc('CLOSEMESSAGES',12,14)))
lexes('lex-code-modulo', '[\\a\\\\b\\]', lexed(loc('OPENMESSAGES',0,2), loc(code('a'),2,3), loc(code('\\'),3,4), loc(code('\\'),4,5), loc(code('b'),5,6), loc('CLOSEMESSAGES',6,8)))
lexes('lex-code-bracket-escape-not-escape', '[\\\\[x\\]', lexed(loc('OPENMESSAGES',0,2), loc(code('\\'),2,3), loc(code('['),3,4), loc(code('x'),4,5), loc('CLOSEMESSAGES',5,7)))
lexes('lex-escape-inside-markup', '[\\[\\\\\\\\]\\]', lexed(loc('OPENMESSAGES',0,2), loc('OPENMARKUP',2,4), loc(ch('\\'),4,6), loc('CLOSEMARKUP',6,8), loc('CLOSEMESSAGES',8,10)))
rows.append('# Errors.')
lexes('lex-stray-close', 'a\\]', '(LEXERROR STRAYCLOSE 1)')
lexes('lex-unclosed-bracket', '[\\a', '(LEXERROR UNCLOSEDBRACKET 3)')
lexes('lex-unclosed-markup', '[\\[\\x', '(LEXERROR UNCLOSEDBRACKET 5)')
lexes('lex-unclosed-string', "[\\'a\\]", '(LEXERROR UNCLOSEDLITERAL 2)')
lexes('lex-unclosed-comment', '[\\(*a*\\]', '(LEXERROR UNCLOSEDLITERAL 2)')
lexes('lex-unclosed-nested-comment', '[\\(*(*a*)\\]', '(LEXERROR UNCLOSEDLITERAL 2)')
rows.append('# Negative queries: wrong results are not derivable.')
lexes('lex-stray-close-not-lexed', 'a\\]', lexed(loc(ch('a'),0,1)), 'false')
lexes('lex-wrong-span-rejected', 'Hi', lexed(loc(ch('H'),0,1), loc(ch('i'),1,3)), 'false')
lexes('lex-escape-not-two-chars', '\\[', lexed(loc(ch('\\'),0,1), loc(ch('['),1,2)), 'false')
rel('run-from-code-mode', 'LexRun', '(TEXTMODE CODEMODE, 5, %s) => (%s)' % (chars('x\\]'), lexed(loc(code('x'),5,6), loc('CLOSEMESSAGES',6,8))), 'true')
rel('step-text-char', 'LexStep', '(TEXTMODE, %s) => (CHAR "a", TEXTMODE, %s)' % (chars('ab'), chars('b')), 'true')
rel('step-open-messages', 'LexStep', '(TEXTMODE, %s) => (OPENMESSAGES, TEXTMODE CODEMODE, eps)' % chars('[\\'), 'true')
rel('step-stray-close-stuck', 'LexStep', '(TEXTMODE, %s) => (CHAR "\\\\", TEXTMODE, %s)' % (chars('\\]'), chars(']')), 'false')
rows.append('# Readers.')
val('lit-simple', 'scan', '$lit(%s)' % chars("ab'cd"), 'SCANNED %s REST %s' % (chars("ab'"), chars('cd')))
val('lit-doubled', 'scan', '$lit(%s)' % chars("a'''x"), 'SCANNED %s REST %s' % (chars("a'''"), chars('x')))
val('lit-at-end', 'scan', '$lit(%s)' % chars("a'"), 'SCANNED %s REST eps' % chars("a'"))
val('lit-unclosed', 'scan', '$lit(%s)' % chars("a''"), 'UNCLOSED')
val('com-flat', 'scan', '$com(1, %s)' % chars('a*)b'), 'SCANNED %s REST %s' % (chars('a*)'), chars('b')))
val('com-nested', 'scan', '$com(1, %s)' % chars('(*x*)*)y'), 'SCANNED %s REST %s' % (chars('(*x*)*)'), chars('y')))
val('com-star-paren-split', 'scan', '$com(1, %s)' % chars('(*)*)'), 'UNCLOSED')
val('com-unclosed', 'scan', '$com(1, %s)' % chars('(*a*)'), 'UNCLOSED')
rows.append('# Mode stacks.')
rel('modestack-initial', 'ModeStack', '(TEXTMODE)', 'true')
rel('modestack-deep', 'ModeStack', '(TEXTMODE CODEMODE TEXTMODE)', 'true')
rel('modestack-code-bottom', 'ModeStack', '(CODEMODE TEXTMODE)', 'false')
rel('modestack-empty', 'ModeStack', '(eps)', 'false')
val('alternating-yes', 'bool', '$alternating(TEXTMODE CODEMODE TEXTMODE CODEMODE)', 'true')
val('alternating-repeat', 'bool', '$alternating(TEXTMODE CODEMODE CODEMODE)', 'false')
val('alternating-code-bottom', 'bool', '$alternating(CODEMODE TEXTMODE)', 'false')
rows.append('# Tokens.')
val('tokens-coalesce', 'spantoken*', '$tokens(%s)' % ' '.join([
    loc(ch('a'),0,1), loc(ch('b'),1,2), loc('OPENMESSAGES',2,4), loc(code('f'),4,5), loc(code('o'),5,6),
    loc('CLOSEMESSAGES',6,8), loc(ch('c'),8,9)]),
    ' '.join(['(TOK (TEXT %s) (SPAN 0 2))' % chars('ab'), '(TOK OPENMESSAGES (SPAN 2 4))',
              '(TOK (CODE %s) (SPAN 4 6))' % chars('fo'), '(TOK CLOSEMESSAGES (SPAN 6 8))',
              '(TOK (TEXT %s) (SPAN 8 9))' % chars('c')]))
val('tokens-brackets-not-merged', 'spantoken*', '$tokens(%s)' % ' '.join([
    loc('OPENMARKUP',0,2), loc('CLOSEMARKUP',2,4)]),
    '(TOK OPENMARKUP (SPAN 0 2)) (TOK CLOSEMARKUP (SPAN 2 4))')
val('tokens-escape-merges-into-text', 'spantoken*', '$tokens(%s)' % ' '.join([
    loc(ch('a'),0,1), loc(ch('['),1,3), loc(ch('b'),3,4)]),
    '(TOK (TEXT %s) (SPAN 0 4))' % chars('a[b'))
val('tokens-empty', 'spantoken*', '$tokens(eps)', 'eps')
# ---- Section 3. Spans below are hand-computed from the sources.
def sp(i, j): return '(SPAN %d %d)' % (i, j)
def seq(*xs): return '(%s)' % ' '.join(xs) if xs else '(eps)'
def tok(kind, i, j, s=None):
    if kind in ('TEXT', 'CODE'): return '(TOK (%s %s) %s)' % (kind, chars(s), sp(i, j))
    return '(TOK %s %s)' % (kind, sp(i, j))
def rblock(u, su, pieces, s): return '(RBLOCK %s %s %s %s)' % (seq(chars(u)) if u else '(eps)', su, seq(*pieces), s)
def rfinal(u, s): return '(RFINAL (%s) %s)' % (chars(u), s)
def src(w, s): return '(SRC (%s) %s)' % (chars(w), s)
def hole(rhos, s): return '(HOLE %s %s)' % (seq(*rhos), s)
def block(u, su, stmts, s): return '(BLOCK %s %s %s %s)' % ('(%s)' % chars(u) if u else '(eps)', su, seq(*stmts), s)
def final(u, s): return '(FINAL (%s) %s)' % (chars(u), s)
def send(x, args, s): return '(SEND (eps) "%s" %s %s)' % (x, seq(*args), s)
def comment(s): return '(COMMENT %s)' % s
def hexpr(k, *lits): return '(HOSTEXPR %d %s)' % (k, seq(*lits))
def markup(nodes, s): return '(MARKUP "doc" %s %s)' % (seq(*nodes), s)
def hsrc(w, s): return '(HSRC (%s) %s)' % (chars(w), s)
def hhole(lit): return '(HHOLE %s)' % lit
host = []   # (pieces, result): the fixture host parser, a finite table
def H(pieces, result):
    if (seq(*pieces), result) not in host: host.append((seq(*pieces), result))
def parses(name, src_, result, truth='true'):
    rel(name, 'Parses', '("doc", %s) => (%s)' % (chars(src_), result), truth)

rows.append('# Structural parse (Markup / Messages) over tokens.')
toks = ' '.join([tok('OPENMESSAGES',0,2), tok('CODE',2,3,'a'), tok('OPENMARKUP',3,5), tok('TEXT',5,6,'b'),
                 tok('CLOSEMARKUP',6,8), tok('CODE',8,9,'c'), tok('CLOSEMESSAGES',9,11), tok('TEXT',11,12,'d')])
raw = ' '.join([rblock('', sp(0,0), [src('a',sp(2,3)), hole([rfinal('b',sp(5,6))], sp(3,8)), src('c',sp(8,9))], sp(0,11)),
                rfinal('d', sp(11,12))])
rel('markup-hole-between-code', 'Markup', '(%s) => (%s, eps)' % (toks, raw), 'true')
rawbad = raw.replace('(SPAN 0 11)', '(SPAN 0 9)')
rel('markup-block-span-is-whole-bracket', 'Markup', '(%s) => (%s, eps)' % (toks, rawbad), 'false')
toks2 = ' '.join([tok('TEXT',0,1,'a'), tok('OPENMESSAGES',1,3), tok('CLOSEMESSAGES',3,5)])
rel('markup-empty-bracket', 'Markup', '(%s) => (%s, eps)' % (toks2, rblock('a', sp(0,1), [], sp(0,5))), 'true')
rel('markup-stops-at-close', 'Markup', '(%s %s) => (%s, %s)' % (tok('TEXT',0,1,'a'), tok('CLOSEMARKUP',1,3), rfinal('a',sp(0,1)), tok('CLOSEMARKUP',1,3)), 'true')

rows.append('# Whole sources (Parses), with the fixture host parser.')
parses('parse-empty', '', 'PARSED (eps)')
parses('parse-text-only', 'Hi', 'PARSED (%s)' % final('Hi', sp(0,2)))
s_p = send('p', [], sp(3,4))
H([hsrc('p', sp(3,4))], 'STMTS (%s)' % s_p)
parses('parse-block-and-final', 'a[\\p\\]b', 'PARSED (%s %s)' % (block('a', sp(0,1), [s_p], sp(0,6)), final('b', sp(6,7))))
# [\title: [\Hamlet\]\]
lit1 = markup([final('Hamlet', sp(11,17))], sp(9,19))
s_t1 = send('title:', [hexpr(1, lit1)], sp(2,19))
H([hsrc('title: ', sp(2,9)), hhole(lit1)], 'STMTS (%s)' % s_t1)
parses('parse-title-literal', '[\\title: [\\Hamlet\\]\\]', 'PARSED (%s)' % block('', sp(0,0), [s_t1], sp(0,21)))
# [\title: [\[\emphasis\]Hamlet[\endEmphasis\]\]\]
s_em = send('emphasis', [], sp(13,21)); H([hsrc('emphasis', sp(13,21))], 'STMTS (%s)' % s_em)
s_ee = send('endEmphasis', [], sp(31,42)); H([hsrc('endEmphasis', sp(31,42))], 'STMTS (%s)' % s_ee)
lit2 = markup([block('', sp(11,11), [s_em], sp(11,23)), block('Hamlet', sp(23,29), [s_ee], sp(23,44))], sp(9,46))
s_t2 = send('title:', [hexpr(2, lit2)], sp(2,46))
H([hsrc('title: ', sp(2,9)), hhole(lit2)], 'STMTS (%s)' % s_t2)
parses('parse-title-emphasis', '[\\title: [\\[\\emphasis\\]Hamlet[\\endEmphasis\\]\\]\\]',
       'PARSED (%s)' % block('', sp(0,0), [s_t2], sp(0,48)))
s_a = send('a', [], sp(2,3)); s_b = send('b', [], sp(5,6))
H([hsrc('a. b', sp(2,6))], 'STMTS (%s %s)' % (s_a, s_b))
parses('parse-two-statements', '[\\a. b\\]', 'PARSED (%s)' % block('', sp(0,0), [s_a, s_b], sp(0,8)))
H([hsrc('(*c*)', sp(2,7))], 'STMTS (%s)' % comment(sp(2,7)))
parses('parse-comment-only', '[\\(*c*)\\]', 'PARSED (%s)' % block('', sp(0,0), [comment(sp(2,7))], sp(0,9)))
rows.append('# Errors. The nested failure is found before the outer bracket is parsed;')
rows.append('# the fixture host has no entry for that outer bracket.')
H([hsrc('x y', sp(2,5))], 'HOSTFAIL %s' % sp(4,5))
parses('parse-host-error', '[\\x y\\]', 'SYNTAXERROR %s' % sp(4,5))
H([hsrc('x y', sp(9,12))], 'HOSTFAIL %s' % sp(11,12))
parses('parse-nested-error-first', '[\\t: [\\[\\x y\\]\\]\\]', 'SYNTAXERROR %s' % sp(11,12))
parses('parse-lex-error', 'a\\]', 'LEXFAIL STRAYCLOSE 1')
parses('parse-lex-error-not-parsed', 'a\\]', 'PARSED (eps)', 'false')
val('lits-projection', 'markupliteral*', '$lits(%s)' % hexpr(1, lit1), lit1)

# ---- Section 4, with tests/signature-fixtures.spectec. Statement spans in
# the direct Interp tests are arbitrary; only the end-to-end Doc test uses
# real source spans.
def st(name, *vs): return '(STATE "%s" %s)' % (name, ' '.join(vs) if vs else 'eps')
def run_(u, s): return '(RUN (%s) %s)' % (chars(u), s)
def sub(tr): return '(SUB %s)' % tr
def tree(state, items, msgs, flag='CLOSED'): return '(TREE %s %s %s %s)' % (state, seq(*items), seq(*msgs), flag)
def interp(name, nodes, result, root=None, chi='(HOSTSTATE 0)', truth='true'):
    rel(name, 'Interp', '(%s, %s, %s) => (%s)' % (chi, root or st('doc'), seq(*nodes), result), truth)
def done(tr, chi='(HOSTSTATE 0)'): return 'DONE %s %s' % (chi, tr)
def bl(u, msgs, s=sp(0, 1)): return block(u, sp(0, 0) if not u else s, msgs, s)
DOC = st('doc')
rows.append('# Interpretation (Interp), direct on DocumentBlockASTs.')
interp('interp-empty', [], done(tree(DOC, [], [])))
interp('interp-flow-whitespace-dropped', [final(' \n\t ', sp(0, 4))], done(tree(DOC, [], [])))
interp('interp-flow-stray-text', [final('x', sp(0, 1))], done(tree(DOC, ['(STRAY (%s) %s)' % (chars('x'), sp(0, 1))], [])))
interp('interp-flow-stray-keeps-source', [final(' x  y', sp(0, 5))],
       done(tree(DOC, ['(STRAY (%s) %s)' % (chars(' x  y'), sp(0, 5))], [])))
sp_ = send('paragraph', [], sp(1, 2))
interp('interp-collapse-unclosed-untrimmed', [bl('', [sp_]), final(' a \n\t b ', sp(3, 11))],
       done(tree(DOC, [sub(tree(st('para'), [run_(' a b ', sp(3, 11))], [sp_], 'UNCLOSED'))], [])))
s_typo = send('itlaic', [], sp(1, 2))
interp('interp-dnu-leaf', [bl('', [s_typo, sp_])],
       done(tree(DOC, ['(DNU %s)' % s_typo, sub(tree(st('para'), [], [sp_], 'UNCLOSED'))], [])))
s_es = send('endSection', [], sp(1, 2))
interp('interp-root-pop', [bl('', [s_es])], done(tree(st('section'), ['(ROOTPOP %s)' % s_es], [])), root=st('section'))
interp('interp-root-pop-not-popped', [bl('', [s_es])], done(tree(st('section'), [], [s_es])), root=st('section'), truth='false')
s_sec = send('section:', [hexpr(5)], sp(1, 2))
interp('interp-section-push-pop', [bl('', [s_sec]), bl('', [s_es])],
       done(tree(DOC, [sub(tree(st('section', '(HOSTV 5)'), [], [s_sec, s_es]))], [])))
s_c1 = send('section:', [hexpr(901)], sp(1, 2)); s_c2 = send('section:', [hexpr(901)], sp(3, 4))
interp('interp-host-state-threaded', [bl('', [s_c1, s_c2])],
       done(tree(DOC, [sub(tree(st('section', '(HOSTV 0)'), [sub(tree(st('section', '(HOSTV 1)'), [], [s_c2], 'UNCLOSED'))], [s_c1], 'UNCLOSED'))], []),
            chi='(HOSTSTATE 2)'))
# refuse leaves an error leaf; popReject pops and flags the block rejected;
# at the root, popReject is a root pop like pop.
s_ref = send('refuseMe', [], sp(3, 4)); s_bad = send('endBad', [], sp(5, 6))
interp('interp-refuse', [bl('', [sp_, s_ref])],
       done(tree(DOC, [sub(tree(st('para'), ['(REFUSED %s)' % s_ref], [sp_], 'UNCLOSED'))], [])))
interp('interp-pop-reject', [bl('', [sp_]), bl(' a ', [s_bad], sp(2, 6))],
       done(tree(DOC, [sub(tree(st('para'), [run_('a', sp(2, 6))], [sp_, s_bad], 'REJECTED'))], [])))
s_bad0 = send('endBad', [], sp(1, 2))
interp('interp-root-pop-reject', [bl('', [s_bad0])], done(tree(DOC, ['(ROOTPOP %s)' % s_bad0], [])))
val('errors-refused-rejected', 'markuperror*', '$errors(%s)' % tree(DOC, [sub(tree(st('para'), ['(REFUSED %s)' % s_ref], [sp_, s_bad], 'REJECTED'))], []),
    '(REJECTEDBLOCK (%s %s)) (ERRORLEAF (REFUSED %s))' % (sp_, s_bad, s_ref))
val('print-rejected-has-closer', 'char*', '$print(%s, %s)' % (chars('[\\paragraph\\][\\endBad\\]'),
    tree(DOC, [sub(tree(st('para'), [], [send('paragraph', [], sp(2, 11)), send('endBad', [], sp(15, 21))], 'REJECTED'))], [])),
    chars('[\\paragraph\\][\\endBad\\]'))
lit_h = markup([final('Hamlet', sp(11, 17))], sp(9, 19))
s_title = send('title:', [hexpr(1, lit_h)], sp(2, 19))
inline_tree = tree(st('inline'), [run_('Hamlet', sp(11, 17))], [])
interp('interp-title-nested-root', [bl('', [s_title])],
       done(tree(st('doc', '(TREEV %s %s)' % (lit_h, inline_tree)), ['(MUT %s)' % s_title], [s_title])))
s_raise = send('section:', [hexpr(900)], sp(1, 2))
interp('interp-arg-raise', [bl('', [s_raise]), final('x', sp(3, 4))], 'RAISED (HOSTSTATE 0) (EXCEPTION 900)')
s_boom = send('boom', [], sp(3, 4))
interp('interp-effect-raise', [bl('', [sp_, s_boom])], 'RAISED (HOSTSTATE 0) (EXCEPTION 7)')
interp('interp-comment-note', [bl('', [comment(sp(1, 6))])], done(tree(DOC, ['(NOTE %s)' % sp(1, 6)], [])))
s_nl = send('newline', [], sp(5, 6)); s_ep = send('endParagraph', [], sp(8, 9))
interp('interp-para-trim-and-leaf', [bl('', [sp_]), bl(' a ', [s_nl], sp(2, 5)), bl(' ', [s_ep], sp(7, 8))],
       done(tree(DOC, [sub(tree(st('para'), [run_('a ', sp(2, 5)), sub(tree(st('newline'), [], [s_nl]))], [sp_, s_ep]))], [])))
s_em = send('emphasis', [], sp(1, 2)); s_ee = send('endEmphasis', [], sp(4, 5))
interp('interp-inline-keeps-space', [bl('', [sp_]), bl('', [s_em]), bl(' x ', [s_ee], sp(2, 5)), bl('', [s_ep])],
       done(tree(DOC, [sub(tree(st('para'), [sub(tree(st('emph'), [run_(' x ', sp(2, 5))], [s_em, s_ee]))], [sp_, s_ep]))], [])))
interp('interp-inline-space-not-trimmed', [bl('', [sp_]), bl('', [s_em]), bl(' x ', [s_ee], sp(2, 5)), bl('', [s_ep])],
       done(tree(DOC, [sub(tree(st('para'), [sub(tree(st('emph'), [run_('x', sp(2, 5))], [s_em, s_ee]))], [sp_, s_ep]))], [])), truth='false')
rows.append('# End to end: the LaTeX example of Section 4 (real spans).')
SRC4 = '[\\paragraph\\] Hi [\\emphasis\\]all[\\endEmphasis\\] [\\endParagraph\\]'
assert SRC4[2:11] == 'paragraph' and SRC4[13:17] == ' Hi ' and SRC4[19:27] == 'emphasis'
assert SRC4[29:32] == 'all' and SRC4[34:45] == 'endEmphasis' and SRC4[47:48] == ' ' and SRC4[50:62] == 'endParagraph' and len(SRC4) == 64
e1 = send('paragraph', [], sp(2, 11)); e2 = send('emphasis', [], sp(19, 27))
e3 = send('endEmphasis', [], sp(34, 45)); e4 = send('endParagraph', [], sp(50, 62))
for w, s, e in (('paragraph', sp(2, 11), e1), ('emphasis', sp(19, 27), e2), ('endEmphasis', sp(34, 45), e3), ('endParagraph', sp(50, 62), e4)):
    H([hsrc(w, s)], 'STMTS (%s)' % e)
ex_tree = tree(DOC, [sub(tree(st('para'), [run_('Hi ', sp(13, 17)), sub(tree(st('emph'), [run_('all', sp(29, 32))], [e2, e3]))], [e1, e4]))], [])
rel('doc-latex-example', 'Doc', '(HOSTSTATE 0, %s) => (%s)' % (chars(SRC4), done(ex_tree)), 'true')
rel('doc-latex-example-untrimmed-rejected', 'Doc', '(HOSTSTATE 0, %s) => (%s)' % (chars(SRC4), done(ex_tree.replace(run_('Hi ', sp(13, 17)), run_(' Hi ', sp(13, 17))))), 'false')
rows.append('# Whitespace and errors functions.')
val('collapse-runs', 'char*', '$collapse(%s)' % chars('a \n\tb  '), chars('a b '))
val('collapse-nbsp-kept', 'char*', '$collapse(%s)' % chars('a  b'), chars('a  b'))
val('child-inline-ws', 'childresult', '$child(INLINE, %s, %s)' % (chars('\n\n'), sp(0, 2)), 'CHILD (RUN (" ") %s)' % sp(0, 2))
val('child-flow-ws', 'childresult', '$child(FLOW, %s, %s)' % (chars('\n\n'), sp(0, 2)), 'NOCHILD')
val('child-empty', 'childresult', '$child(PARA, eps, %s)' % sp(0, 0), 'NOCHILD')
val('trim-both-ends', 'kid*', '$trim((RUN (%s) %s) (BLK 3) (RUN (" ") %s))' % (chars(' a '), sp(0, 3), sp(4, 5)),
    '(RUN (%s) %s) (BLK 3)' % (chars('a '), sp(0, 3)))
val('trim-single-run', 'kid*', '$trim((RUN (%s) %s))' % (chars(' a '), sp(0, 3)), '(RUN (%s) %s)' % (chars('a'), sp(0, 3)))
val('trim-non-run-edges', 'kid*', '$trim((BLK 1) (RUN (" ") %s) (BLK 2))' % sp(0, 1), '(BLK 1) (RUN (" ") %s) (BLK 2)' % sp(0, 1))
unc = tree(DOC, ['(DNU %s)' % s_typo, sub(tree(st('para'), ['(STRAY (%s) %s)' % (chars('z'), sp(0, 1))], [sp_], 'UNCLOSED'))], [])
val('errors-document-order', 'markuperror*', '$errors(%s)' % unc,
    '(ERRORLEAF (DNU %s)) (UNCLOSEDBLOCK (%s)) (ERRORLEAF (STRAY (%s) %s))' % (s_typo, sp_, chars('z'), sp(0, 1)))

# ---- Section 5: printing. Spans in the fixture host entries for printed
# sources are located with at(), which asserts that the located text is
# what the test expects; the trees and printed sources are hand-written.
def at(src, sub, nth=0):
    i = -1
    for _ in range(nth + 1):
        i = src.index(sub, i + 1)
    return sp(i, i + len(sub))
def simple(src, word, nth=0):
    s = at(src, word, nth); e = send(word, [], s); H([hsrc(word, s)], 'STMTS (%s)' % e); return e
rows.append('# Printing.')
val('esc-specials', 'char*', '$esc(%s)' % chars('a\\[b\\]['), chars('a\\\\\\[b\\\\]\\['))
# Escaped text lexes back to the text, even before a bracket (eq:escape-lexes).
lexes('esc-lexes-back', 'x\\\\\\[\\\\]y\\\\[\\p\\]', lexed(
    loc(ch('x'),0,1), loc(ch('\\'),1,3), loc(ch('['),3,5), loc(ch('\\'),5,7), loc(ch(']'),7,8),
    loc(ch('y'),8,9), loc(ch('\\'),9,11), loc('OPENMESSAGES',11,13), loc(code('p'),13,14), loc('CLOSEMESSAGES',14,16)))
val('slice', 'char*', '$slice(%s, %s)' % (chars('abcdef'), sp(2, 5)), chars('cde'))
# The Section 4 LaTeX example prints canonically and round-trips.
P4 = '[\\paragraph\\]Hi [\\emphasis\\]all[\\endEmphasis\\][\\endParagraph\\]'
for w in ('paragraph', 'emphasis', 'endEmphasis', 'endParagraph'): simple(P4, w)
val('print-latex-example', 'char*', '$print(%s, %s)' % (chars(SRC4), ex_tree), chars(P4))
rel('roundtrip-latex-example', 'RoundTrip', '(HOSTSTATE 0, %s) => (%s, true, true)' % (chars(SRC4), chars(P4)), 'true')
# A richer source: a mutation, stray text, a comment bracket, a comment
# before a message, escapes, a message not understood, an unclosed block.
W2 = ('[\\title: [\\Hamlet\\]\\]' + '\noops' + '[\\(*c*)\\]' + ' ' + '[\\(*n*)  paragraph\\]'
      + ' a\\\\b \\[x ' + '[\\itlaic\\]' + 'z' + '[\\endParagraph\\]' + '\n' + '[\\paragraph\\]' + 'end')
W2P = ('[\\title: [\\Hamlet\\]\\]' + '\noops' + '[\\(*c*)\\]' + '[\\(*n*) paragraph\\]'
       + 'a\\\\b \\[x ' + '[\\itlaic\\]' + 'z' + '[\\endParagraph\\]' + '[\\paragraph\\]' + 'end')
assert at(W2, 'title: ') == sp(2, 9) and at(W2, 'Hamlet') == sp(11, 17)   # as s_title / lit_h
for src in (W2, W2P):
    H([hsrc('(*c*)', at(src, '(*c*)'))], 'STMTS (%s)' % comment(at(src, '(*c*)')))
w2_stmts = {}
for src in (W2, W2P):
    code_ = '(*n*)  paragraph' if src is W2 else '(*n*) paragraph'
    pg = '(SEND (%s) "paragraph" (eps) %s)' % (at(src, '(*n*)'), at(src, 'paragraph'))
    H([hsrc(code_, at(src, code_))], 'STMTS (%s)' % pg)
    w2_stmts[src] = (pg, simple(src, 'itlaic'), simple(src, 'endParagraph'), simple(src, 'paragraph', 1))
pg, si, sep, pg2 = w2_stmts[W2]
lit_w2 = markup([final('Hamlet', sp(11, 17))], sp(9, 19))
w2_tree = tree(st('doc', '(TREEV %s %s)' % (lit_w2, inline_tree)), [
    '(MUT %s)' % s_title,
    '(STRAY (%s) %s)' % (chars('\noops'), at(W2, '\noops')),
    '(NOTE %s)' % at(W2, '(*c*)'),
    sub(tree(st('para'), [run_('a\\b [x ', at(W2, ' a\\\\b \\[x ')), '(DNU %s)' % si, run_('z', at(W2, 'z'))], [pg, sep])),
    sub(tree(st('para'), [run_('end', at(W2, 'end', 1))], [pg2], 'UNCLOSED'))], [s_title])
rel('doc-rich', 'Doc', '(HOSTSTATE 0, %s) => (%s)' % (chars(W2), done(w2_tree)), 'true')
val('print-rich', 'char*', '$print(%s, %s)' % (chars(W2), w2_tree), chars(W2P))
rel('roundtrip-rich', 'RoundTrip', '(HOSTSTATE 0, %s) => (%s, true, true)' % (chars(W2), chars(W2P)), 'true')
rel('roundtrip-rich-not-verbatim', 'RoundTrip', '(HOSTSTATE 0, %s) => (%s, true, true)' % (chars(W2), chars(W2)), 'false')
# Messages are printed by the host printer, not copied: the layout inside a
# send is normalized, and literals in its holes are printed by the core.
W3 = '[\\title:   [\\Hamlet\\]\\]'
W3P = '[\\title: [\\Hamlet\\]\\]'
lit_w3 = markup([final('Hamlet', at(W3, 'Hamlet'))], sp(11, 21))
s_w3 = send('title:', [hexpr(1, lit_w3)], sp(2, 21))
H([hsrc('title:   ', sp(2, 11)), hhole(lit_w3)], 'STMTS (%s)' % s_w3)
val('print-host-layout', 'char*', '$print(%s, %s)' % (chars(W3), tree(DOC, ['(MUT %s)' % s_w3], [s_w3])), chars(W3P))
rel('roundtrip-host-layout', 'RoundTrip', '(HOSTSTATE 0, %s) => (%s, true, true)' % (chars(W3), chars(W3P)), 'true')
W4 = '[\\title: [\\[\\emphasis\\]Hamlet[\\endEmphasis\\]\\]\\]'
val('print-literal-blocks', 'char*', '$print(%s, %s)' % (chars(W4), tree(DOC, ['(MUT %s)' % s_t2], [s_t2])), chars(W4))
val('print-literal-escapes', 'char*', '$print(eps, %s)' % tree(DOC, ['(MUT %s)' % send('title:', [hexpr(1, markup([final('a[b\\', sp(0, 0))], sp(0, 0)))], sp(0, 0))], []),
    chars('[\\title: [\\a\\[b\\\\\\]\\]'))
rows.append('# Canonical form: spans erased, adjacent runs and strays merged.')
val('canon-merges-runs', 'tree', '$canon(%s)' % tree(DOC, [run_('a ', sp(0, 2)), run_(' b', sp(5, 7)), '(STRAY (%s) %s)' % (chars('x'), sp(7, 8)), '(STRAY (%s) %s)' % (chars(' y'), sp(9, 11))], []),
    tree(DOC, [run_('a b', '$z'), '(STRAY (%s) $z)' % chars('x y')], []))
val('canon-distinguishes-text', 'bool', '$canon(%s) = $canon(%s)' % (tree(DOC, [run_('a', sp(0, 1))], []), tree(DOC, [run_('b', sp(0, 1))], [])), 'false')
val('canon-distinguishes-flag', 'bool', '$canon(%s) = $canon(%s)' % (tree(DOC, [], []), tree(DOC, [], [], 'UNCLOSED')), 'false')
val('canon-ignores-spans', 'bool', '$canon(%s) = $canon(%s)' % (tree(DOC, [run_('a', sp(0, 1))], [s_typo]), tree(DOC, [run_('a', sp(4, 5))], [send('itlaic', [], sp(7, 8))])), 'true')

with open(sys.argv[2], 'w') as f:
    f.write(';; Generated by tests/gen_cases.py. The fixture host parser: a finite\n')
    f.write(';; table of the brackets the regressions contain. Non-normative.\n\n')
    for pieces, result in host:
        f.write('def $hostParse%s = %s\n' % (pieces if pieces.startswith('((') else '(%s)' % pieces, result))

with open(sys.argv[1], 'w') as f:
    f.write('# name\tkind\ttype-or-relation\tquery\texpected\n')
    for r in rows:
        f.write((r if isinstance(r, str) else '\t'.join(r)) + '\n')
