# Comments in front of a member are dropped by the IDE; the printer now moves them inside

**Status:** printer + tests done on disk 2026-09-07, tests 121/122 (the one
failure is the pre-existing `testEmptyBlock`). Tool snapshots NOT yet rebuilt
(needs a VM invocation the agent sandbox cannot approve) — see "What remains".

## The problem

The IDE never stores a file. On save it reassembles the class from the mirrors
(`ClassDeclarationMirror source` → `to:writeClassDeclaration:` in
MirrorsForPrimordialSoup.ns): the mixin's `_headerSource`, then each lazy
slot's source, then each method's source. Every one of those is the parser's
AST span for that member, which starts at the member's first token (access
modifier / pattern / `lazy` / `class`). A comment written between two members
is lexer whitespace that belongs to no span, so it is silently gone after the
next save from the IDE. Comments inside a method body and the class comment
inside the header parens are within a span and survive.

Confirmed live against the running IDE: DeploymentManager.ns on disk has a
comment in front of `lazy public CroquetRuntime`; the image's class source for
DeploymentManager is 71038 chars vs 71422 on disk, contains the slot, and does
not contain that comment, while a body comment and the class comment are both
present.

This is a different problem from PRETTY_PRINTER_COMMENT_ORPHANING_2026-08-16.md
(the printer reattaching comments during reordering). It is upstream of the
printer: the text is already gone before the printer runs.

Sites at risk in the tree on 2026-09-07: 34 comments in 12 files, mostly
NewspeakLazySlotMigrationTesting.ns (12), NewspeakTypecheckerTesting.ns (7),
NewspeakParsingTesting.ns (5), plus MirrorsForJS, DeploymentManager,
GraphicsForHTML5, HopscotchForCroquet, KernelForJS, NSCompilerTesting,
NewspeakPrettyPrinterTesting, RuntimeForCroquet, RuntimeForCroquetJS (1 each).
HostForCroquet.ns (untracked) also has a file-prologue comment before `class`.

## The decision (Gilad, 2026-09-07): convention + printer canonicalization

1. **Convention.** A member's comment goes inside the member. Method: first
   thing after `= (`. Class (nested or top-level): just inside the header's
   `(`, i.e. the class comment position. Lazy slot: inline after the `=`,
   ahead of the initializer (a lazy slot's span runs from `lazy` through the
   initializer; there is no other safe place). Recorded in CLAUDE.md (both
   worktrees) and in the AI chat's style guidelines in AI_IDE_Support.ns,
   which used to say the opposite ("Comments precede the construct").

2. **Printer.** `NewspeakPrettyPrinter` canonical form now moves a member's
   leading comments into the member. Changes:
   - `emitMember:of:from:with:` no longer emits leading comments in front of
     the member; the visitor does. Backstop rescans from the window's start.
   - `skipLeadingCommentsOf:` moves the cursor to the member's first token
     (also fixes a latent hazard: `emitInPatternMetadata:` /
     `findBodyOpenPosFrom:` searched for `=` from the window start, so an `=`
     inside a leading comment could be taken for the member's own).
   - `emitLeadingCommentsOf:from:inline:` / `emitCommentsFrom:upTo:inline:`
     emit the [window start, member start) comments from a rewound cursor.
   - `visitMethod:` emits them first inside the body; `visitClassHeader:` /
     `emitClassHeaderBody:leadingFrom:` emit them just inside the header `(`;
     `visitLazySlot:` drains everything up to the initializer inline after the
     `=` (so a comment already there prints the same way — fixed point).
   - `printClass:` / `printClassHeader:` / `printMethod:` / `printSlot:` (lazy)
     no longer call `emitCommentsBefore:` — a file prologue moves into the
     top-level class header too.
   - The round-trip checker's ownership rule ("a member owns its leading
     comments plus everything inside it") is unchanged and still holds, so
     `round-trip-check.sh` passes on moved comments.

   Tests (NewspeakPrettyPrinterTesting.ns): `testLeadingMethodCommentMovesIntoBody`,
   `testLeadingMethodCommentJoinsExistingBodyComment`,
   `testLeadingNestedClassCommentMovesIntoHeader`,
   `testLeadingTopLevelClassCommentMovesIntoHeader`,
   `testLeadingLazySlotCommentMovesAfterEquals`,
   `testLeadingCommentMovesArePrinterFixedPoint`;
   `testLeadingCommentFollowsMethodPrintedOutOfOrder` updated to the new
   placement.

Not covered: comments after the LAST member of a side. No member owns them, the
printer leaves them where they are, and the IDE still drops them.

## What remains

- Rebuild the three tool snapshots that embed the printer
  (`NewspeakPrettyPrintApp`, `NewspeakRoundTripCheckApp`,
  `NewspeakAttachmentDiffApp`): `sh scratch/rebuild-printer-snapshots.sh`
  (= tool/build.sh steps 4c–4e, no emscripten). Until then
  `tool/pretty-print.sh` still runs the OLD printer.
- With the new snapshots: print every tracked .ns to a temp copy and diff.
  Expected: only the 12 files above change, each change a comment moving
  into its member; printer is a fixed point on its own output;
  `round-trip-check.sh` OK on all.
- Reprint those 12 files in place (Gilad's call — several are mid-edit).
  NOTE the reprint only helps files the image is later (re)loaded from; the
  image's copies of those classes have ALREADY lost the comments, so an IDE
  save of e.g. DeploymentManager before a reload drops them regardless.
- Load the new NewspeakPrettyPrinter.ns into the IDE (hot-load is fine) so
  the IDE's own pretty-print-on-accept moves a comment typed in front of a
  method header into the body instead of losing it.

## Verification 2026-09-09 — the fix works

Snapshots were rebuilt 2026-09-08 09:41. Sweep: every tracked .ns in the main
tree (198, excluding `squeak/`) printed to a scratch dir with the new printer,
and again with the OLD printer (HEAD's `NewspeakPrettyPrinter.ns` compiled to a
scratch `NewspeakPrettyPrintApp.vfuel`) to separate this change from drift.

- **18 files** differ between old and new printer output; every hunk is a
  member-leading comment moving into its member (54 moves total). More than the
  12 listed above because the tree grew since 2026-09-07 (Grok provider, peer
  messaging, HostForCroquet mounts) and because the scan also catches the
  `lazy x ::= <newline> (* c *) <newline> init` form, which the printer now
  inlines after the `=` (Browsing, Repositories). NSCompilerTesting drops off:
  its one hit was a comment inside a method body, oddly indented, never at risk.
  Affected: AI_IDE_Support, AsyncBridgeProbe, Browsing, DeploymentManager,
  GraphicsForHTML5, HopscotchForCroquet, KernelForJS, MirrorsForJS,
  Newspeak2JSCompilation, NewspeakLazySlotMigrationTesting,
  NewspeakParsingTesting, NewspeakPrettyPrinterTesting,
  NewspeakTypecheckerTesting, Repositories, RuntimeForCroquet,
  RuntimeForCroquetJS, VCSIsomorphicGitBackendProvider, WebFiles.
- Fixed point: reprinting the new output reproduces it byte-for-byte (all 33
  files that changed at all). `parse-validate` OK on all 33 outputs.
  `round-trip-check.sh` OK on all 198 originals. Printer suite 121/122
  (`testEmptyBlock`, pre-existing).
- Separately, **18 files have pre-existing drift** the OLD printer already
  reformats (not this change): BytecodeSimulatorForJS (426 diff lines: missing
  `Object new` superclass clauses, blank-line indentation), NewspeakTypechecker
  (199), NewspeakTypecheckerTesting (146), Newspeak2V5BytecodeCompilation (108),
  V5BytecodeSimulation (45), Newspeak2V5BytecodeCompilationTesting (36),
  AmpleforthViewer (31), V5BytecodeSimulationTesting (18),
  VCSIsomorphicGitBackendProvider (17), JavascriptGeneration (5), and ≤4 lines
  each in Newspeak2V5BytecodeCompilationTestingConfiguration,
  Newspeak2JSDualEmissionTestingConfiguration,
  V5BytecodeSimulationTestingConfiguration, RuntimeForJSWithMirrorBuilders,
  ListProbe, AIAccess, WebFiles, BuildInfo (the last few are a missing trailing
  newline or one blank-line indent). Reprinting these is a separate decision.
- Cosmetic note for the lazy-slot placement: a long comment inlined after `=`
  makes a very long line, and the initializer may then wrap
  (`lazy public host = (* ... *) HostForCroquet usingPlatform: self` / `hostClass: Host.`).

Still open: reprint in place (Gilad's call), and hot-load the new
NewspeakPrettyPrinter.ns into the IDE.

## Close-out 2026-09-09

- IDE ⇄ offline agreement verified: Gilad printed HopscotchForHTML5.ns and
  AI_IDE_Support.ns from the IDE (saved via the OS file dialog into the main
  tree). The offline printer is a no-op on both except for a trailing newline
  after the final `) : ()` — the IDE writes none, the offline tool writes one.
  That newline is the only remaining difference between the two printers.
- The first IDE print of AI_IDE_Support.ns had already lost the comments in
  front of `lazy public GrokProvider` and `lazy pendingPeerMessages` (image
  copies lost them before the printer ran, as predicted above). Spliced back
  from the sweep output, inline after `=`; a second IDE print preserved both.
- The other 17 affected files were reprinted in place in the main tree
  (byte-identical to the sweep outputs; round-trip + parse-validate OK).
  Three of them also absorbed pre-existing drift in the same reprint:
  NewspeakTypecheckerTesting (~146 lines), VCSIsomorphicGitBackendProvider
  (~17), WebFiles (1). Suites after the reprint: typechecker 275/275,
  parsing 32/32, lazy-slot migration 53/53, printer 121/122 (testEmptyBlock).
- Still open: hot-load the new NewspeakPrettyPrinter.ns into the IDE;
  the remaining 15 drifted files listed under "Verification" are untouched.
