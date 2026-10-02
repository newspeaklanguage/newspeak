# Newspeak formal semantics

This directory contains a formal, executable-minded account of Newspeak's
runtime semantics.  Its normative language reference is working version 0.109
of the Newspeak specification.  Section 3.3 of *Modules as Objects in
Newspeak* (ECOOP 2010) is supporting explanatory material, especially for
implicit-receiver selection; where the two differ, the current specification
wins.

The project deliberately separates four things that are often conflated:

1. the surface PEG and its AST;
2. elaboration of syntactic conveniences and implicit members;
3. the sequential operational semantics;
4. concurrency and causally connected reflective change.

Design draft 0.14, `newspeak-semantics.tex`, fixes the semantic domains, the
lookup/dispatch kernel, the complete sequential language, and its actor lift:
isolated heaps, remote representation, asynchronous sends, FIFO turns, promise
settlement and pipelining, actor creation, and causal/E-ordered delivery.
It also includes mirrors, exact-instance and mixin-application population
queries, transactional reflective program change, and an explicit
garbage-collection overlay.  The reflective layer also gives every live frame
an explicit current term and source/PC location, supports immutable stack
snapshots, pause-token guarded actor suspension, atomic whole-stack
replacement, fresh frame and segment copying, resumable-exception transfer,
and resumption under the normal VM execution relation.  It states the
refinement obligation connecting the Newspeak Simulator's bytecode frames to
these abstract frame images.  The garbage-collection layer is isolated in
`gc-semantics.tex`; removing its single `\input` line restores the
monotonically growing-store semantics without altering the actor or reflection
rules.  When included, that layer also gives `WeakArray` weak-element clearing
and `WeakMap` ephemeron/key-weak behavior, including atomic clearing during a
partial collection.  The draft also gives a normalized concrete Newspeak PEG,
production-complete concrete-tree actions, metadata attachment, stable AST
identities, exhaustive static elaboration, annotated-core validation, and
executable artifacts.  The
active parser, elaborator, and compiler are ordinary Newspeak objects selected
through a reified language descriptor; their replacement uses existing
mutation and reflection, while the VM retains a fixed core-verification and
artifact-loading boundary.  `coverage.md` is a
ledger against the language specification.  A feature may not disappear merely
because it is inconvenient to formalize: it remains in the ledger until it has
rules or is explicitly classified as a host/platform parameter.

`lookup_model.py` is a non-normative executable oracle for the lookup rules.
Its tests pin down access barriers, lexical private dispatch, virtual protected
dispatch, DNU, and the starting point of super lookup.
`class_init_model.py` similarly pins down freshness, mixin sharing, physical
layout, initialization order, simultaneous installation, lazy nil behavior,
and per-receiver nested-class caching.
`actor_model.py` pins down remote-representation normalization, immediate
promise creation, FIFO turns, causal delivery barriers, pipelined sends, and
broken-promise propagation.
`gc_model.py` pins down strong and conditional weak-map reachability,
`WeakArray` clearing, `WeakMap` entry removal, closed partial reclamation,
observable instance and mixin-application enumeration, and permanent non-reuse
of collected identities.
`debugger_model.py` pins down stack imaging, push/pop/copy construction,
fresh-identity rewiring, stale pause-token rejection, atomic replacement, and
full-speed resumption.
`frontend_model.py` pins down PEG ordered choice, greedy repetition, capture
spans, grammar admissibility, complete-input recognition, front-end image
capture, ordinary component replacement, and fixed-boundary rejection of
invalid core images.

`lean/` is the machine-checked companion development.  Its theorem inventory
tracks every obligation in section 14, while `Newspeak.Properties` exports
only completed proofs.  The initial checked slice covers typed semantic
identities, the static-program/heap separation, static program coherence,
finite superclass and lexical-class chains, deterministic unrestricted,
public, and protected lookup, equivalence with the named lookup rules, and the
static `bind = scan` theorem.  The current runtime bridge keeps mixin
definitions in the program while giving mixin identities ordinary heap object
representation; it also proves determinism of nearest application, lexical
depth, ordinary dispatch, super dispatch, and DNU target selection.
It also covers the special depth-one enclosing-object rule, deterministic
outer/self dispatch, and the dynamic equivalence of the elaborated and
ECOOP-style class-scope implicit-send presentations.

## Building

From this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error newspeak-semantics.tex
bibtex newspeak-semantics
pdflatex -interaction=nonstopmode -halt-on-error newspeak-semantics.tex
pdflatex -interaction=nonstopmode -halt-on-error newspeak-semantics.tex
python3 -m unittest -v
cd lean && ~/.elan/bin/lake build
```

The semantics is currently a design draft, not yet a replacement for any
normative text in the language specification.
