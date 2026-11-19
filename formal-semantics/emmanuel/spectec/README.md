# Emmanuel in SpecTec

A **LaTeX-first transcription** of `../emmanuel-semantics.tex`, the formal
semantics of Emmanuel, the Ampleforth mark-edit language. The LaTeX is
authoritative; this directory checks it. Conventions follow the Newspeak
transcription in `../../spectec/` (see its README): distinct identity
constructors, explicit absent constructors, disjunctions as separately named
rules with no first-match priority, inductive relations without fuel, and
`;; @equation` / `;; @rule` / `;; @partial` origin labels audited into
[COVERAGE.md](COVERAGE.md) and `manifest.json`.

The whole parametric core is transcribed: **Section 2, lexical
structure**, **Section 3, grammar and abstract syntax**, **Section 4,
interpretation**, and **Section 5, printing**. Pending are only the six
obligations, which are theorems: lexical determinism (`eq:lex-determinism`),
structural totality (`eq:structural-totality`), interpretation determinism
(`eq:interp-determinism`), the escaping lemma (`eq:escape-lexes`), the round
trip (`eq:round-trip`), and idempotence of printing (`eq:print-idempotent`).
The regressions check the first three on every test and the last three on
the printing tests (see below).

**Section 6, the standard library** (its structural core) is transcribed in
[library/07-library.spectec](library/07-library.spectec), an instance of the
block signature: `$cls` and the `Effect` relation. It is checked and
rendered with the core, and regressed in a configuration of its own
(`library/tests/`), since the core's regressions run a toy signature
instead.

**Section 7, editing**, is transcribed in [08-edit.spectec](08-edit.spectec):
the image and provenance, the field interface (declared there; the
library defines its block side in `07-library.spectec`, the fixture host its
host side), points, anchors, carets, splices, the edits (`$replace`,
`$split`, `$style`, setting a string, detaching), tidying, and the
relation `Edit` with its refusals. A caret (`EXACT point` or `AT point
anchor`) can lie in white space the view does not show, such as a trimmed
trailing space; `$place` resolves an anchor to the point the view shows,
`$caretOK` checks that the two agree, and the relation `Caret` places the
caret offset an edit returns (`CARETAT k`, or `SAMECARET`) in the new
document. Edits carry a caret marker (`LCARET`) through tidying, which is
transparent to cancellation; a replacement's items after the caret are
wrapped in `AFTERCARET`, because the pinned SpecTec mis-elaborates two
adjacent lists of the same type in one constructor. Its regressions run in the library configuration, since
edits need real blocks. The keys of the view (`$typeText`, `$deleteRange`,
`$backspace`) are in 08-edit; Enter, block templates, and insertion
(`$enter`, `$template`, `$insertAt`) are the library's. Every example in
Section 7 of the LaTeX names the regression that checks it; the helper
relations `LibAnchor`, `LibLoc`, `LibIsPoint`, `LibBackspace`, `LibEnter`,
`LibInsertable`, `LibInsert`, `LibPlace`, `LibCaretOK`, and `LibEditCaret`
(in `library/tests/library-helpers.spectec`) expose what the edit layer
computes so those examples can be checked. In `gen_library.py` the expected
caret is placed by hand in the expected source (`mark`), and its offset is
derived from that placement. The
obligations and laws of Section 7, splicing (`eq:splice-items`), locality
(`eq:law-locality`), identity (`eq:law-identity`), and typing
(`eq:edit-typing`), are pending with the others; identity is checked on
instances (`edit-identity`, `edit-identity-empty`).

1. [00-domains.spectec](00-domains.spectec): characters, spans, the four
   distinguished sequences, mode stacks, lexemes, run results, tokens.
2. [01-lexical.spectec](01-lexical.spectec): the string and comment readers,
   the `LexStep` rules `Lex-*`, the run judgment `LexRun` with spans and the
   error rules `Run-*`, `Lexes`, and coalescing into tokens.
3. [02-grammar.spectec](02-grammar.spectec): raw nodes, the structural parse
   (`Markup`, `Messages`), abstract syntax, the host parser parameter
   `$hostParse` (declared, never defined), resolution, and `Parses`.
4. [03-parameters.spectec](03-parameters.spectec): host states, values,
   block states, finished trees, and the two parameters of interpretation:
   the host evaluator `Eval` and the block signature (`$cls`, `Effect`),
   declared with no rules.
5. [04-whitespace.spectec](04-whitespace.spectec): `$collapse`, the text
   child of a DocumentBlockAST's contents, and trimming.
6. [05-machine.spectec](05-machine.spectec): the block store, items,
   argument evaluation `Args`, the step relation `Step` (rules `Step-*`),
   `Run`, `Interp`, `InterpretWith`, reading the tree, and `$errors`.
7. [06-printing.spectec](06-printing.spectec): escaping, `$slice` (W[s]),
   printing messages and trees, and the canonical form `$canon` with
   `$mergeKids`.
8. [library/07-library.spectec](library/07-library.spectec): the standard
   library: block states and content classes, content models, `$plain`,
   the inline-argument rules (`Inline`, `Lib-Inline-*`), `$libErrors`, and
   its field interface (`$fields`, `$joins`, the styles).
9. [08-edit.spectec](08-edit.spectec): editing (Section 7).

## Transcription choices

- A `char` is a one-scalar `text`; that every char of a source is a single
  Unicode scalar is an input obligation. Sources are `char*`.
- Mode constructors are `TEXTMODE`/`CODEMODE`; single capitals are
  metavariables in SpecTec.
- The readers' `bot` is `UNCLOSED`; a reader success is `SCANNED u* REST w*`.
  (A tuple payload `SCANNED (char*, char*)` typechecks but crashes the
  pinned `--all-passes` type-family-removal pass when used in a function
  clause, hence the mixfix form.)
- `ModeStack` transcribes the grammar `eq:mode-stacks` (bottom `T`).
  `$alternating` transcribes the shape `eq:mode-alternation` as a predicate;
  that every stack reachable from `T` alternates is a lemma, not proved.
- `$alternating` uses head recursion via `$alternatesFrom`, avoiding the
  pinned evaluator's known-suffix list bug inside functions (as `resumeStack`
  does in the Newspeak transcription). Relation rules keep the LaTeX's
  rightward `mu T` patterns; the driver corrects that matcher.
- The host parser is declared and left undefined. Regressions supply a
  **fixture host**, `tests/host-fixtures.spectec`: a finite table with one
  clause per bracket the tests contain. A bracket missing from the table
  leaves `$hostParse` irreducible, so the driver fails loudly rather than
  inventing a parse. Host argument expressions are `HOSTEXPR nat L*`: an
  identity plus `lits(eta)`, the only thing the core observes.
- Resolution's guards "if node(rho) = ok(n)" are transcribed as dispatch
  functions (`$resolveOn`, `$blockOn`, `$hostOn`, `$holeOn`), one equation
  per LaTeX case: the pinned evaluator does not evaluate binding premises in
  function clauses (they work in relation rules).
- Sequence components of constructors are parenthesized, as in
  `RBLOCK (u*) s (p*) s'`, so ground terms parse unambiguously.
- Host states, values, exceptions, and block states are abstract in the
  LaTeX. They are transcribed as carriers wide enough for the regressions:
  `HOSTSTATE nat`, `LITV L | TREEV tree | HOSTV nat | STRV | INTV | NILV`
  (the last three for the library; a symbol is a string literal), `EXCEPTION nat`,
  `STATE text value*`. The evaluator and signature are rule-less relations;
  `tests/signature-fixtures.spectec` (hand-written) gives a toy instance in
  the shape of the standard library, including `title:`, whose effect
  interprets its literal with an inline root, so the mutual recursion of
  signature and interpretation is exercised.
- The store is a list indexed from 0 with head-recursive `$at`/`$put`; the
  LaTeX's `trimEnd` (a suffix match) is transcribed by reversal, for the
  same evaluator bug as `$alternating`. An item `sigma` is injected as
  `ISTMT sigma`.
- The printer's `closer` takes the last message with the head-recursive
  `$lastStmt` rather than a suffix pattern. Erasure on the host carriers
  (values, block states) is defined in `06-printing.spectec`; in the LaTeX
  it is the host's. `$mergeKids` is the LaTeX's `merge` (renamed: `$merge`
  coalesces tokens).
- Messages are printed by the host printer `$hostPrint` (the LaTeX's
  Q_W, declared in `03-parameters.spectec`), which returns code with
  literal holes; the core prints the holes (`$show`, `$showLit`,
  `$showNodes`). The fixture host printer (`tests/host-eval-fixtures.spectec`,
  shared with the library regressions, as is the fixture evaluator) prints a
  keyword send with one literal argument from its selector, so
  `title:   [\Hamlet\]` prints as `title: [\Hamlet\]`; other sends are
  copied from their source.
- A block record carries a mark `RECOK | RECREJECTED` (the LaTeX's
  `ok | rejected`). Closing a cell uses `$hasBlockKid`, `$hasTextKid`, and
  `$dropSpaces`; a white-space run is recognised as one that `$lstrip`
  empties, since runs are collapsed and never empty.
- The library's fields are positional values in `STATE kind (value*)`,
  with `NILV` for an absent field and `INTV` for a section's depth. Its
  regressions compare canonical trees (`LibTree`), so expected trees carry
  no spans; `LibErrors` reports `$libErrors` and the core's `$errors` of the
  canonical tree; `LibRoundTrip` is `RoundTrip` for the library.
- The fixture relation `RoundTrip` interprets a source, prints it,
  reinterprets the printed source from the same host state, and reports the
  printed source, whether the trees and host states agree up to `$canon`, and
  whether printing again is the identity; so each round-trip test checks
  instances of `eq:round-trip` and `eq:print-idempotent`.
- A literal records its source name, `MARKUP nm (n*) s`, and `Parses`
  takes the name of the source it parses; a tree value records its
  literal, `TREEV L tr`. The variable for source names is `nm`, since `d`
  is the lexer's comment depth.
- Edits are functions computing the new source text; `Edit` is the
  relation that parses and interprets the document, follows the points,
  and dispatches, with one rule per refusal. A point's navigation `NAV`
  carries the markup, the blocks on the path from the root of its tree,
  their child indices, the block, and the field the path last entered.
  Tidying marks items `LOP`/`LCL` with the creating message of their block
  and an origin (`OUTL`, `INS`, `OUTR`), cancels with a reversed stack, and
  widens the splice by the marked messages removed outside it.
- A statement given by the field interface has the span `[0, 0)`; the
  fixture host printer prints such a unary send from its selector. The
  fixture host takes a keyword send's argument to start one space after
  the selector (`$argSpan`), knows which constants are string literals, and
  prints a string as `'u'` and a tree value as a copy of its literal.
- `$merge` checks span adjacency (`j = j'`) as a guard rather than with a
  repeated pattern variable; runs always produce adjacent spans.

## Build and test

Uses the Newspeak toolchain; bootstrap it once in `../../spectec`
(`python3 tools/bootstrap.py`). Then, from this directory:

```sh
python3 tools/check_sources.py --write # refresh after source or LaTeX changes
python3 tools/build.py
```

`tests/cases.tsv` holds the regressions (value and relation tests, with
negative queries). The driver `tools/regress.ml` is forked from the Newspeak
driver and adds **mode-directed relation solving**: components left of `=>`
are inputs, premises are solved in order and may bind outputs, so a premise
such as `LexStep: (mu*, w*) => (lambda, mu'*, w'*)` with unknown outputs can
be checked. Every rule is tried; more than one solution fails the run as
overlapping derivations, so each test also witnesses determinism for its
input. Goals are memoized by relation and query; sibling rules that share
premises (Run-Step / Run-Step-Error) otherwise make the search exponential
in the input length. Mutation checks (removing a `Lex-Text-Char` guard; making the string
reader stop at the first quote; dropping a block's bracket from its span;
deleting Markup-Stop; letting a nested-literal error pass; in Section 4,
not trimming a closing paragraph, dropping the root-pop leaf, dropping stray
text, not flagging unclosed blocks, not threading the host state through
arguments, not recording the closing message; in Section 5, not escaping
`[`, dropping the closer, dropping a message's comments, dropping the `mut`
marker, merging runs without collapsing, erasing text in `$canon`, not
printing stray text, a verbatim host printer, unescaped literal text,
dropping a literal's statements, not printing comment brackets through the
host; in the cell and refusal machinery, never rejecting a mixed cell, keeping
layout in a flow cell, not trimming the cell shorthand, not flagging a
`popReject`, dropping the refused leaf, printing no closer for a rejected
block; in the library, allowing a second title, accepting any label value,
flat section depths, ignoring errors in fields, making an item a paragraph
block, interpreting a taken title's argument; in the edit layer, never cancelling an
adjacent open and close, never joining blocks, not widening the splice over
cancelled messages, not reopening blocks after a split, not closing crossed
blocks before a style, printing the text left or right of a splice
unescaped, treating a template literal as computed, dropping the detach
offer, losing mutating messages in a deletion, not reopening a style after
removing it, tidying an empty edit at one anchor) turn the suite red. The fixture and helper files are loaded by the driver only, never
by the checker. `tests/cases.tsv` and `tests/host-fixtures.spectec` are generated by
`python3 tests/gen_cases.py tests/cases.tsv tests/host-fixtures.spectec`;
their expected values are hand-written in the generator, never computed.
The library's `library/tests/library-cases.tsv` and
`library/tests/library-host.spectec` are generated by
`python3 library/tests/gen_library.py library/tests/library-cases.tsv library/tests/library-host.spectec`,
which derives the fixture host-parser table from the test sources with a
small parser for the restricted code they use; expected trees, errors, and
printed sources are hand-written. The driver is test
infrastructure, not a proof.

Outputs in ignored `build/`: `emmanuel.generated.tex`, `emmanuel.ast`,
`emmanuel.mechanization.ast`, and `report.json`; generation is checked to be
deterministic and path-independent.
