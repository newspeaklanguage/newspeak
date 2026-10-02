#!/usr/bin/env python3
"""Generate the linked reference data from the formal-semantics LaTeX source."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SEMANTICS = ROOT.parent
MAIN = SEMANTICS / "newspeak-semantics.tex"
ACTORS = SEMANTICS / "actor-semantics.tex"
REFLECTION = SEMANTICS / "reflection-semantics.tex"
GC = SEMANTICS / "gc-semantics.tex"
FRONTEND = SEMANTICS / "front-end-semantics.tex"
AUX = SEMANTICS / "newspeak-semantics.aux"
OUTPUT = ROOT / "app" / "definitions.generated.json"


def symbol(pattern: str, notation: str, description: str) -> tuple[re.Pattern[str], str, str]:
    return re.compile(pattern), notation, description


# Longer and more specific notations come first.  Descriptions are deliberately
# phrased so they remain correct wherever a metavariable is reused by a family
# of closely related definitions.
PARAMETERS = [
    symbol(r"\\mathcal\s*(?:\{A\}|A)", "\\mathcal A", "Activation stack: the ordered stack of active activations and their continuation links."),
    symbol(r"\\mathcal\s*(?:\{X\}|X)", "\\mathcal X", "Actor run-state map, recording whether each actor is idle, executing a turn, or paused with a resumable stack."),
    symbol(r"\\mathcal\s*(?:\{Q\}|Q)", "\\mathcal Q", "Mailbox map; \\mathcal Q(A) is actor A's FIFO queue."),
    symbol(r"\\mathcal\s*(?:\{N\}|N)", "\\mathcal N", "Multiset of cross-actor packets emitted but not yet delivered."),
    symbol(r"\\mathcal\s*(?:\{E\}|E)", "\\mathcal E", "Permanent event ledger mapping an event identity to source, destination, and causal history."),
    symbol(r"\\mathcal\s*(?:\{D\}|D)", "\\mathcal D", "Per-actor arrival ledger, including delivered and retired events in arrival order."),
    symbol(r"\\mathcal\s*(?:\{H\}|H)", "\\mathcal H", "Actor-heap map; \\mathcal H(A) is the private mutable heap owned by actor A."),
    symbol(r"\\mathcal\s*(?:\{L\}|L)", "\\mathcal L", "Host registry of installed language front ends used to compile a compilation unit."),
    symbol(r"\\mathcal\s*(?:\{P\}|P)", "\\mathcal P", "Finite power-set operator used to type a set-valued program component."),
    symbol(r"\\mathcal\s*(?:\{U\}|U)_r", "\\mathcal U_r", "Set of unauthorized command indices in the reflection transaction being diagnosed."),
    symbol(r"\\mathcal\s*(?:\{C\}|C)_r", "\\mathcal C_r", "Set of conflicting command-index pairs in the reflection transaction being diagnosed."),
    symbol(r"\\mathcal\s*(?:\{B\}|B)_r", "\\mathcal B_r", "Nonempty set of failed reflection-validation kinds for the prepared candidate."),
    symbol(r"\\mathcal\s*(?:\{R\}|R)_h", "\\mathcal R_h", "Finite set of strong references temporarily retained by the embedding host during an atomic platform operation."),
    symbol(r"\\mathcal\s*(?:\{S\}|S)_\{?\\Omega(?:')?\}?", "\\mathcal S_\\Omega", "Disjoint collectable reference store of VM heap objects, promises, and far-reference routing records."),
    symbol(r"\\mathcal\s*(?:\{S\}|S)(?!_)", "\\mathcal S", "Immutable debugger stack template: an ordered sequence of retained or fresh frame specifications."),
    symbol(r"\\mathcal\s*(?:\{K\}|K)", "\\mathcal K", "Resolved control image: an ordered sequence pairing concrete activation identities with their frame controls."),
    symbol(r"\\mathcal\s*(?:\{I\}|I)", "\\mathcal I", "Allocation-history set containing every reference identity used so far in this execution."),
    symbol(r"\\widehat\s*H", "\\widehat H_A", "Heap view visible to actor A: its private heap together with any shared immutable value heap."),
    symbol(r"\\bar\s*\\lambda", "\\bar\\lambda", "Ordered declarations in a simultaneous local-slot group."),
    symbol(r"\\bar\s*\\ell", "\\bar\\ell", "Ordered sequence of normalized local-slot declarations or their physical identities."),
    symbol(r"\\bar\s*x", "\\bar x", "Ordered formal-parameter list."),
    symbol(r"\\bar\s*O", "\\bar O", "Remaining ordered sequence of ordinary object identities in a reconciliation phase."),
    symbol(r"\\bar\s*o", "\\bar o", "Ordered argument-value list."),
    symbol(r"\\bar\s*e", "\\bar e", "Ordered expression list, normally unevaluated arguments."),
    symbol(r"\\bar\s*s", "\\bar s", "Ordered statement list."),
    symbol(r"\\bar\s*g", "\\bar g", "Ordered list of sequential or simultaneous slot-initializer groups."),
    symbol(r"\\bar\s*d", "\\bar d", "Ordered sequence of normalized slot declarations in one initializer group."),
    symbol(r"\\bar\s*\\delta", "\\bar\\delta", "Remaining ordered sequence of commands in a fold."),
    symbol(r"\\bar\s*m", "\\bar m", "Ordered message sequence used by a tuple cascade."),
    symbol(r"\\bar\s*k", "\\bar k", "Ordered tuple of keyword-symbol atoms in a keyword pattern."),
    symbol(r"\\bar\s*p", "\\bar p", "Ordered tuple of component patterns in a keyword pattern."),
    symbol(r"\\bar\s*u", "\\bar u", "Ordered segment of frame-template keys selected for copying."),
    symbol(r"\\bar\s*y", "\\bar y", "Ordered sequence of WeakArray cell values."),
    symbol(r"\\bar\s*t", "\\bar t", "Ordered forest of concrete parse trees returned by PEG recognition."),
    symbol(r"\\bar\s*R", "\\bar R", "Ordered sequence of surface-AST nodes."),
    symbol(r"\\bar\s*B", "\\bar B", "Innermost-first sequence of lexical binder maps."),
    symbol(r"\\bar\s*v", "\\bar v", "Ordered argument-value sequence supplied to an ordinary service call."),
    symbol(r"\\mathcal\s*(?:\{J\}|J)_G", "\\mathcal J_G", "Semantic-action map from a captured PEG production, child ASTs, and source slice to a raw AST node."),
    symbol(r"\\mathcal\s*(?:\{B\}|B)(?!_r)", "\\mathcal B", "Finite family of immutable concrete code images in an executable artifact."),
    symbol(r"\\rho_G", "\\rho_G", "Finite PEG production map from nonterminals to parsing expressions."),
    symbol(r"I_L", "I_L", "Immutable front-end image captured for one compilation, containing parser, elaborator, compiler, grammar, and revision."),
    symbol(r"v_L", "v_L", "Language-defined revision value captured in the front-end image and artifact."),
    symbol(r"v_s", "v_s", "Ordinary Newspeak value returned by the parser and decoded as a surface AST."),
    symbol(r"v_k", "v_k", "Ordinary Newspeak value returned by the elaborator and decoded as an annotated core image."),
    symbol(r"v_b", "v_b", "Ordinary Newspeak value returned by the compiler and decoded as an executable artifact."),
    symbol(r"o_L", "o_L", "Ordinary language object selected from the host language registry."),
    symbol(r"o_p", "o_p", "Ordinary Newspeak parser object captured in a front-end image."),
    symbol(r"o_e", "o_e", "Ordinary Newspeak elaborator object captured in a front-end image."),
    symbol(r"o_c", "o_c", "Ordinary Newspeak compiler object captured in a front-end image."),
    symbol(r"r_k", "r_k", "Classified surface receiver kind used to construct the appropriate core send form."),
    symbol(r"r_t", "r_t", "Context flag recording whether a local return is permitted at the source site."),
    symbol(r"h_t", "h_t", "Context flag recording whether a non-local return is permitted at the source site."),
    symbol(r"q_c", "q_c", "Fresh synthetic closure identity introduced by cascade expansion."),
    symbol(r"d_c", "d_c", "Fresh synthetic formal-declaration identity introduced by cascade expansion."),
    symbol(r"x_c", "x_c", "Fresh synthetic formal name introduced by cascade expansion."),
    symbol(r"a_w", "a_w", "WeakArray object identity."),
    symbol(r"m_w", "m_w", "WeakMap object identity."),
    symbol(r"E(?:')?_w", "E_w", "Finite WeakMap entry map from weak object keys to conditionally retained values."),
    symbol(r"y(?:')?_[A-Za-z0-9]+", "y_i", "WeakArray cell value at an indicated position, before or after weak-reference clearing."),
    symbol(r"u_f", "u_f", "Template-local name of a fresh activation to be allocated when a debugger stack template is installed."),
    symbol(r"r_s", "r_s", "Unforgeable pause token identifying one particular suspended actor state."),
    symbol(r"d_s", "d_s", "Immutable debugger stop-reason descriptor retained with a paused actor."),
    symbol(r"b_c", "b_c", "Immutable executable code image containing the suspended machine instruction."),
    symbol(r"n_c", "n_c", "Concrete program-counter offset within immutable code image b_c."),
    symbol(r"\\lambda_c", "\\lambda_c", "Stable control location, represented either by a source site or by an immutable code-image identity and concrete program counter."),
    symbol(r"u_i", "u_i", "Template-local name of the fresh activation allocated for frame position i."),
    symbol(r"u_k", "u_k", "Template-local name assigned to the copied frame at position k."),
    symbol(r"\\kappa_w", "\\kappa_w", "Causal history captured when a dependent eventual send was registered."),
    symbol(r"\\kappa_r", "\\kappa_r", "Reflection-validation kind identifying one explicitly defined invariant check."),
    symbol(r"p_r", "p_r", "Fresh promise that will receive the result of the current eventual send."),
    symbol(r"p_0", "p_0", "Reply promise of the actor turn already in progress."),
    symbol(r"u_0", "u_0", "Event whose delivery started the actor turn already in progress."),
    symbol(r"D_0", "D_0", "Declaration identity of the immediately enclosing lexical class body."),
    symbol(r"D_t", "D_t", "Declaration identity naming the lexical target of an outer send."),
    symbol(r"C_f", "C_f", "Runtime class in which the selected method was found."),
    symbol(r"C_m", "C_m", "Fresh metaclass paired with runtime class C."),
    symbol(r"I_m", "I_m", "Fresh metaclass paired with the class produced by a mixin application."),
    symbol(r"C_0", "C_0", "Class at which a failed lookup began; retained for DNU lookup."),
    symbol(r"M_c", "M_c", "Class-side mixin used to construct a metaclass."),
    symbol(r"N_t", "N_t", "Runtime class corresponding to a selected lexical target."),
    symbol(r"N_0", "N_0", "Runtime class corresponding to the immediately enclosing lexical class."),
    symbol(r"o_t", "o_t", "Enclosing receiver selected as the target of an outer send."),
    symbol(r"o_L", "o_L", "Receiver of the object literal that supplies a lexical binding."),
    symbol(r"a_T", "a_T", "Fresh top activation used to start a program or actor turn."),
    symbol(r"a_I", "a_I", "Fresh activation for a synthesized instance initializer."),
    symbol(r"a_c", "a_c", "Activation captured by a closure."),
    symbol(r"a_q", "a_q", "Activation selected from a lexical-scope map for an enclosing declaration."),
    symbol(r"a_S", "a_S", "Fresh activation executing a superclass initializer."),
    symbol(r"a_M", "a_M", "Fresh activation executing an applied-mixin initializer."),
    symbol(r"q_a", "q_a", "Continuability flag of an activation."),
    symbol(r"L_o", "L_o", "Set of physical slot identities required by object o's final class layout."),
    symbol(r"i_f", "i_f", "Stable identity of a method definition."),
    symbol(r"i_I", "i_I", "Stable synthetic identity of a mixin or class instance initializer."),
    symbol(r"i_A", "i_A", "Stable identity of a normalized mixin-application site."),
    symbol(r"i_M", "i_M", "Stable identity of an applied-mixin initializer."),
    symbol(r"A_n", "A_n", "Generated send that allocates the temporary n-element Array used to elaborate a tuple literal."),
    symbol(r"s_f", "s_f", "Primary-factory selector."),
    symbol(r"s_I", "s_I", "Selector of a normalized mixin initializer."),
    symbol(r"m_S", "m_S", "Deferred superclass-initializer message template."),
    symbol(r"m_M", "m_M", "Deferred applied-mixin initializer message template."),
    symbol(r"b_I", "b_I", "Body of a normalized mixin initializer."),
    symbol(r"E_C", "E_C", "Normalized class form associated with a nested or top-level class declaration."),
    symbol(r"e_F", "e_F", "Annotated core expression denoting Past`Future for lazy or simultaneous initialization."),
    symbol(r"x_z", "x_z", "Pattern-variable occurrence annotated with stable source-site identity z."),
    symbol(r"\\chi_C", "\\chi_C", "Class-creation provenance, distinguishing ordinary expression creation from actor creation."),
    symbol(r"\\chi_b", "\\chi_b", "Normalized descriptor for a class-body expression."),
    symbol(r"\\chi_a", "\\chi_a", "Normalized descriptor for a mixin-application expression."),
    symbol(r"\\delta_\{\\mathrm\{objectClass\}\}", "\\delta_{\\mathrm{objectClass}}", "Object-reclassification command: changes one object's runtime class."),
    symbol(r"\\delta_\{\\mathrm\{objectSlot\}\}", "\\delta_{\\mathrm{objectSlot}}", "Object-slot command: writes one slot without changing the object's class."),
    symbol(r"\\delta_\{\\mathrm\{continuation\}\}", "\\delta_{\\mathrm{continuation}}", "Continuation-transfer command that resumes a selected activation."),
    symbol(r"\\delta_\{\\mathrm\{activation\}\}", "\\delta_{\\mathrm{activation}}", "Activation-record command that edits activation state without transferring control."),
    symbol(r"\\delta_\{\\mathrm\{debug\}\}", "\\delta_{\\mathrm{debug}}", "Debugger-control command that atomically pauses, replaces, or resumes an actor stack."),
    symbol(r"\\delta_\{\\mathrm\{class\}\}", "\\delta_{\\mathrm{class}}", "Class-record command that changes a runtime class's superclass or enclosing object."),
    symbol(r"\\delta_\{\\mathrm\{code\}\}", "\\delta_{\\mathrm{code}}", "Source-code command applied before deterministic re-elaboration."),
    symbol(r"\\delta_r", "\\delta_r", "One reflective transaction command, including its authorizing mirror."),
    symbol(r"\\delta_s", "\\delta_s", "Replacement sequence of physical slot declarations for a reflected mixin."),
    symbol(r"\\delta_n", "\\delta_n", "Replacement sequence of nested-class declarations for a reflected mixin."),
    symbol(r"\\delta_c", "\\delta_c", "Continuation-transfer command being applied to the actor run state."),
    symbol(r"q_r", "q_r", "Reflective inspection query naming the descriptor to reify."),
    symbol(r"C_g", "C_g", "Platform mirror class of mirror object g."),
    symbol(r"\\Gamma", "\\Gamma", "Causal-history map; \\Gamma(A) contains events causally prior to actor A's next emission."),
    symbol(r"\\Phi", "\\Phi", "Far-reference table mapping a far-reference identity to its home actor and near object."),
    symbol(r"\\Pi", "\\Pi", "Promise table recording each promise's owner and pending, fulfilled, or broken state."),
    symbol(r"\\Omega", "\\Omega", "Complete VM-cohort configuration: program and version, shared and actor-local heaps, run states, mailboxes, network, eventual-reference tables, and event history."),
    symbol(r"\\Sigma", "\\Sigma", "Complete sequential-machine configuration: program, heap, activation stack, and control term."),
    symbol(r"\\Psi", "\\Psi", "Garbage-collection wrapper state pairing a VM configuration with its permanent allocation history."),
    symbol(r"\\Delta", "\\Delta", "Validated reflective transaction descriptor, including program edits, runtime changes, and debugger control commands installed atomically."),
    symbol(r"\\psi(?:_[A-Za-z0-9]+)?", "\\psi", "Debugger frame-template constructor, optionally decorated to identify a selected or copied frame."),
    symbol(r"\\kappa", "\\kappa", "Finite causal history carried by an event, promise waiter, or factory descriptor as indicated by context."),
    symbol(r"\\chi", "\\chi", "Settlement tag: ok for fulfillment or error for breaking."),
    symbol(r"\\mu", "\\mu", "Message value consisting of a selector and an ordered argument-value list."),
    symbol(r"\\beta", "\\beta", "Packet template that fills every packet field except event identity, source, destination, and history."),
    symbol(r"\\theta", "\\theta", "Evaluated receiver/request descriptor used while constructing or routing a send."),
    symbol(r"\\gamma", "\\gamma", "Lexical-scope map from enclosing declaration identities to runtime activations."),
    symbol(r"\\rho", "\\rho", "Activation environment mapping formal-parameter identities to argument values."),
    symbol(r"\\sigma", "\\sigma", "Object slot store mapping physical slot identities to values."),
    symbol(r"\\eta", "\\eta", "Per-object cache of nested-class values."),
    symbol(r"\\phi", "\\phi", "Finite selector-to-method map defined directly by a mixin."),
    symbol(r"\\delta", "\\delta", "Source-ordered physical slot declarations of a mixin."),
    symbol(r"\\nu", "\\nu", "Nested-class declarations of a mixin."),
    symbol(r"\\iota", "\\iota", "Normalized mixin initializer, or its projection from the static program."),
    symbol(r"\\tau", "\\tau", "Initialization continuation tag describing what should happen after local initialization."),
    symbol(r"\\lambda", "\\lambda", "One normalized local-slot declaration, or a binder used as a packet constructor in a rule."),
    symbol(r"\\mathbb\s*(?:\{N\}|N)", "\\mathbb N", "Natural-number domain used for indices, counters, and fixed-point iteration."),
    symbol(r"\\alpha", "\\alpha", "Method access level, or a continuously enabled action in the fairness condition."),
    symbol(r"\\xi_r", "\\xi_r", "Reflection-rejection diagnostic selected by the formally ordered failure function."),
    symbol(r"\\xi", "\\xi", "Reified runtime error or inheritance error value."),
    symbol(r"\\prec(?!e)", "\\prec", "Fixed total order on object identities used to make reconciliation deterministic."),
    symbol(r"\\omega", "\\omega", "Surface spelling of an atomic literal."),
    symbol(r"\\varepsilon", "\\varepsilon", "Numeric sign, either -1 or 1, in decoded number literals."),
    symbol(r"\\epsilon", "\\epsilon", "Empty sequence, empty frame stack, or absent list, as determined by the containing domain."),
    symbol(r"\\pi", "\\pi", "Continuation-frame sequence beneath the currently executing activation."),
    symbol(r"\\ell", "\\ell", "Local-slot declarations in a method/closure, or an activation's local-slot map."),
    symbol(r"\\zeta", "\\zeta", "Intermediate value or control datum introduced by the definition."),
    symbol(r"\\varphi", "\\varphi", "Auxiliary finite map introduced by the definition."),
    symbol(r"\\varrho", "\\varrho", "Reflective authority right carried by a mirror capability."),
    symbol(r"\\mathfrak\s*F", "\\mathfrak F", "Distributed family mapping each VM identity to its independently versioned actor configuration."),
    symbol(r"(?<![A-Za-z])U(?![A-Za-z])", "U", "Complete object store of the current VM cohort."),
    symbol(r"(?<![A-Za-z])w(?![A-Za-z])", "w", "Virtual-machine identity defining one reflective propagation cohort."),
    symbol(r"(?<![A-Za-z])P(?![A-Za-z])", "P", "Static program: immutable maps from stable declaration identities to syntax and metadata."),
    symbol(r"(?<![A-Za-z])H(?:'|_[A-Za-z0-9]+)?(?![A-Za-z])", "H", "Heap (with primes or subscripts denoting related states or actor-local heaps)."),
    symbol(r"(?<![A-Za-z])A(?![A-Za-z])", "A", "Actor identity in actor rules; otherwise a metavariable explicitly typed by the displayed judgment."),
    symbol(r"(?<![A-Za-z])B(?![A-Za-z])", "B", "Destination or promise-owning actor identity."),
    symbol(r"(?<![A-Za-z])C(?![A-Za-z])", "C", "Runtime class identity; in actor rules it may also name a waiting actor where the context says so."),
    symbol(r"(?<![A-Za-z])M(?![A-Za-z])", "M", "Static mixin identity."),
    symbol(r"(?<![A-Za-z])D(?![A-Za-z])", "D", "Stable class-body declaration identity."),
    symbol(r"(?<![A-Za-z])K(?![A-Za-z])", "K", "Stable declaration identity that owns a method or mixin."),
    symbol(r"(?<![A-Za-z])L(?![A-Za-z])", "L", "Object-literal or class-expression declaration identity, according to the form."),
    symbol(r"(?<![A-Za-z])N(?![A-Za-z])", "N", "Runtime class occurring on a class chain or lexical-class correspondence."),
    symbol(r"(?<![A-Za-z])S(?![A-Za-z])", "S", "Superclass value or runtime superclass identity."),
    symbol(r"(?<![A-Za-z])R(?![A-Za-z])", "R", "Receiver's runtime class, or an intermediate class/mixin result."),
    symbol(r"(?<![A-Za-z])V(?![A-Za-z])", "V", "Shared heap containing only immutable, reachable value objects."),
    symbol(r"(?<![A-Za-z])W(?![A-Za-z])", "W", "Ordered promise-waiter sequence."),
    symbol(r"(?<![A-Za-z])Q(?![A-Za-z])", "Q", "Remaining FIFO mailbox tail."),
    symbol(r"(?<![A-Za-z])F(?![A-Za-z])", "F", "Continuation-frame grammar or one continuation frame."),
    symbol(r"(?<![A-Za-z])G(?![A-Za-z])", "G", "Slot-initializer group."),
    symbol(r"(?<![A-Za-z])I(?![A-Za-z])", "I", "Fresh runtime class produced by a mixin application."),
    symbol(r"(?<![A-Za-z])E(?![A-Za-z])", "E", "Normalized class form or top-level expression, as fixed by the defining judgment."),
    symbol(r"(?<![A-Za-z])X(?![A-Za-z])", "X", "Least set of activations dependent on a non-local return target."),
    symbol(r"(?<![A-Za-z])Y(?![A-Za-z])", "Y", "Second set, syntax node, or span endpoint paired with X by the displayed definition."),
    symbol(r"(?<![A-Za-z])a(?:'|_[A-Za-z0-9]+)?(?![A-Za-z])", "a", "Runtime activation identity (decorations distinguish related or freshly allocated activations)."),
    symbol(r"(?<![A-Za-z])c(?![A-Za-z])", "c", "Runtime closure identity."),
    symbol(r"(?<![A-Za-z])o(?:'|_[A-Za-z0-9]+)?(?![A-Za-z])", "o", "Runtime object/value identity; decorations distinguish related values or receivers."),
    symbol(r"(?<![A-Za-z])f(?![A-Za-z])", "f", "Method definition selected by lookup or stored in the static program."),
    symbol(r"(?<![A-Za-z])s(?![A-Za-z])", "s", "Message selector symbol."),
    symbol(r"e_p", "e_p", "Arbitrary partial semantic expression whose definedness is being tested."),
    symbol(r"(?<![A-Za-z])e(?:'|_[A-Za-z0-9]+)?(?![A-Za-z])", "e", "Expression (a subscript identifies a particular syntactic role)."),
    symbol(r"(?<![A-Za-z])b(?![A-Za-z])", "b", "Method/closure body in sequential definitions, or a mailbox/network packet in actor definitions."),
    symbol(r"(?<![A-Za-z])v(?![A-Za-z])", "v", "Computed runtime value."),
    symbol(r"(?<![A-Za-z])x(?:'|_[A-Za-z0-9]+)?(?![A-Za-z])", "x", "Value, identifier, or signaled exception selected by the definition's declared domain."),
    symbol(r"(?<![A-Za-z])y(?![A-Za-z])", "y", "Value after remote representation or another helper transformation."),
    symbol(r"(?<![A-Za-z])z(?![A-Za-z])", "z", "Auxiliary result value."),
    symbol(r"(?<![A-Za-z])d(?![A-Za-z])", "d", "Stable declaration selected by initial elaboration, or a pattern descriptor."),
    symbol(r"(?<![A-Za-z])j(?![A-Za-z])", "j", "Physical local-slot or instance-slot identity."),
    symbol(r"(?<![A-Za-z])i(?![A-Za-z])", "i", "Natural-number index, depth, or execution position."),
    symbol(r"(?<![A-Za-z])n(?![A-Za-z])", "n", "Arity, finite length, normalized source name, or VM program version, according to the definition."),
    symbol(r"(?<![A-Za-z])m(?![A-Za-z])", "m", "Message template, method identity, or finite count determined by context."),
    symbol(r"(?<![A-Za-z])k(?![A-Za-z])", "k", "Continuation link: the activation at which execution resumes, or nil."),
    symbol(r"(?<![A-Za-z])h(?![A-Za-z])", "h", "Home activation used for lexical ancestry and non-local return."),
    symbol(r"(?<![A-Za-z])g(?:'|_[A-Za-z0-9]+)?(?![A-Za-z])", "g", "Unforgeable mirror-object identity; decorations distinguish a freshly derived mirror."),
    symbol(r"(?<![A-Za-z])t(?![A-Za-z])", "t", "Current control term; in return definitions it may be the selected target activation."),
    symbol(r"(?<![A-Za-z])l(?![A-Za-z])", "l", "Literal payload occurring in a literal pattern."),
    symbol(r"(?<![A-Za-z])p(?![A-Za-z])", "p", "Promise identity in actor definitions; otherwise a pattern or activation provenance value."),
    symbol(r"(?<![A-Za-z])q(?![A-Za-z])", "q", "Factory descriptor or closure declaration identity, as fixed by the enclosing record."),
    symbol(r"(?<![A-Za-z_])r(?![A-Za-z])", "r", "Far-reference identity or a dispatch/lookup result."),
    symbol(r"(?<![A-Za-z])u(?![A-Za-z])", "u", "Fresh actor event identity."),
]


def clean_title(value: str) -> str:
    value = re.sub(r"\\(?:NS|kw)\{([^}]*)\}", r"\1", value)
    value = value.replace("\\", "").replace("{}", "")
    return value.strip()


def title_from_id(identifier: str) -> str:
    name = identifier.split(":", 1)[-1].replace("-", " ")
    initialisms = {"dnu": "DNU", "rr": "RR", "ast": "AST", "gc": "GC"}
    words = [initialisms.get(word, word) for word in name.split()]
    title = " ".join(words)
    return title[:1].upper() + title[1:]


def classify(formula: str, is_rule: bool) -> str:
    if is_rule:
        return "Rule"
    if "::=" in formula:
        return "Grammar"
    if "\\dfrac" in formula or "\\longrightarrow" in formula:
        return "Transition"
    if "\\vdash" in formula or "\\Downarrow" in formula:
        return "Judgment"
    return "Definition"


def clean_formula(formula: str) -> str:
    formula = re.sub(r"(?m)%.*$", "", formula)
    formula = re.sub(r"\\label\{[^}]+\}", "", formula)
    formula = re.sub(r"\\quad\(\\rulelabel\{[^}]+\}\)\.?", "", formula)
    formula = re.sub(r"\\(?:small|footnotesize|scriptsize)\b", "", formula)
    formula = re.sub(r"^\s*\\begin\{equation\}\s*", "", formula)
    formula = re.sub(r"\s*\\end\{equation\}\s*$", "", formula)
    lines = [line.rstrip() for line in formula.strip().splitlines()]
    while lines and not lines[0].strip():
        lines.pop(0)
    return "\n".join(lines)


def read_equation_numbers() -> dict[str, str]:
    if not AUX.exists():
        return {}
    numbers: dict[str, str] = {}
    for match in re.finditer(r"\\newlabel\{(eq:[^}]+)\}\{\{([^}]*)\}", AUX.read_text()):
        numbers[match.group(1)] = match.group(2)
    return numbers


def balanced_group(text: str, start: int) -> tuple[str, int] | None:
    while start < len(text) and text[start].isspace():
        start += 1
    if start >= len(text) or text[start] != "{":
        return None
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{" and (index == 0 or text[index - 1] != "\\"):
            depth += 1
        elif text[index] == "}" and (index == 0 or text[index - 1] != "\\"):
            depth -= 1
            if depth == 0:
                return text[start : index + 1], index + 1
    return None


def rule_formula(text: str, marker: int) -> str:
    # Match display delimiters only when they occupy their own line.  A plain
    # rfind("\\[") also matches the second backslash in an aligned-row spacing
    # command such as \\[-1mm], truncating rules whose conclusions use aligned.
    display_starts = list(
        re.finditer(r"(?m)^[ \t]*\\\[[ \t]*$", text[:marker])
    )
    display_start = display_starts[-1].end() if display_starts else -1
    display_end_match = re.search(r"(?m)^[ \t]*\\\][ \t]*$", text[marker:])
    display_end = (
        marker + display_end_match.start() if display_end_match else -1
    )
    fraction_start = text.rfind("\\dfrac", max(display_start, 0), marker)
    if fraction_start >= 0:
        cursor = fraction_start + len("\\dfrac")
        numerator = balanced_group(text, cursor)
        if numerator:
            denominator = balanced_group(text, numerator[1])
            if denominator:
                return clean_formula(text[fraction_start : denominator[1]])
    if display_start >= 0 and display_end >= 0:
        return clean_formula(text[display_start:display_end])
    line_start = text.rfind("\n", 0, marker) + 1
    return clean_formula(text[line_start:marker])


def parameter_list(formula: str) -> list[dict[str, str]]:
    found: list[dict[str, str]] = []
    seen: set[str] = set()
    working = formula
    for pattern, notation, description in PARAMETERS:
        if notation not in seen and pattern.search(working):
            found.append({"notation": notation, "description": description})
            seen.add(notation)
            # Prevent a specific notation such as M_c, \\bar x, or \\mathcal A
            # from also being reported as its constituent one-letter symbols.
            working = pattern.sub(" ", working)
    if not found:
        found.append(
            {
                "notation": "—",
                "description": "This closed definition has no free parameters; its constructors are introduced by the displayed grammar.",
            }
        )
    return found


def refine_descriptions(
    parameters: list[dict[str, str]], identifier: str, section: str
) -> list[dict[str, str]]:
    """Resolve the few one-letter metavariables whose domains vary by section."""
    replacements: dict[str, str] = {}
    if section.startswith("10 "):
        replacements.update(
            {
                "A": "Actor identity, normally the source or currently executing actor.",
                "B": "Actor identity, normally the destination or owner of a promise.",
                "C": "Actor identity used as a far-reference home or promise waiter.",
                "p": "Promise identity.",
                "r": "Far-reference identity.",
                "b": "Application, settlement, or wake packet in a mailbox or the network.",
            }
        )
        if identifier == "eq:create-actor":
            replacements["C"] = "Fresh runtime class that forms the root object of the new actor."
    if section.startswith("11 "):
        replacements.update(
            {
                "A": "Actor invoking the mirror operation; its heap must contain the authorizing mirror.",
                "g": "Unforgeable mirror-object identity authorizing this inspection or change.",
                "R": "Finite set of reflective rights held by a mirror capability.",
                "Q": "Patched source-program candidate before deterministic re-elaboration.",
                "n": "Committed program-version number of the current VM cohort.",
                "p": "Reply promise retained by a running actor turn.",
                "b": "Replacement method body or another command payload fixed by the constructor.",
                "d": "Immutable descriptor value returned by reflective inspection.",
                "x": "Parameter name or replacement runtime value, according to the command constructor.",
                "C": "Runtime class identity named by the reflected structure or object.",
                "M": "Mixin identity named by the reflected structure or source command.",
                "m": "Finite number of commands in the reflective transaction.",
                "\\delta": "One command element of the reflective transaction sequence.",
                "\\zeta": "Mirror target describing the VM, actor, program, mixin, method, class, object, or activation covered by the capability.",
            }
        )
        debugger_ids = {
            "eq:control-location-domain",
            "eq:frame-control-domain",
            "eq:frame-current-term-and-location",
            "eq:stack-control-image",
            "eq:decode-control-image",
            "eq:debug-frame-image",
            "eq:actor-stack-snapshot",
            "eq:live-activation-control",
            "eq:stack-template-domain",
            "eq:promote-demote-frame-control",
            "eq:pop-stack-frames",
            "eq:push-stack-frame",
            "eq:copy-stack-frame-segment",
            "eq:debug-activation-descriptor",
            "eq:debugger-command-projection",
            "eq:resolve-stack-template-keys",
            "eq:debug-stack-image-validity",
            "eq:retire-removed-stack-activations",
            "eq:materialize-stack-template",
            "eq:pause-actor-effect",
            "eq:replace-current-actor-stack",
            "eq:resume-exception-stack-template",
            "eq:replace-paused-actor-stack",
            "eq:resume-paused-actor-full-speed",
            "eq:replace-resume-paused-actor-stack",
            "eq:debugger-command-fold",
            "eq:simulator-step-correspondence",
            "eq:remote-debugger-component-step",
        }
        if identifier in debugger_ids:
            replacements.update(
                {
                    "B": "Actor whose execution stack is being observed, paused, replaced, or resumed.",
                    "R": "Activation record being reified or installed, or the finite set of activation identities retired by stack replacement.",
                    "D": "Newspeak-level Simulator state corresponding to the selected concrete actor state.",
                    "m": "Stack length, snapshot mode, or finite frame count fixed by the displayed definition.",
                    "i": "Natural-number frame position or segment boundary within the debugger stack image.",
                    "j": "Natural-number frame position or segment boundary within the debugger stack image.",
                    "x": "Signaled exception, parameter value, local value, or replacement value carried by a debugger frame.",
                    "z": "Stable source site used to identify source-level control independently of a generated machine address.",
                    "S": "Immutable debugger stack template to inspect, transform, or install.",
                    "\\eta": "Debugger frame key naming either a retained activation or a fresh frame within a stack template.",
                    "\\nu": "Finite debugger key-resolution or activation-renaming map used while materializing or copying stack frames.",
                    "\\kappa": "Per-frame control image: either an active current term and location or a suspended continuation location.",
                    "\\varphi": "Reified debugger frame containing activation state, structural links, and explicit control.",
                }
            )
        if identifier == "eq:copy-stack-frame-segment":
            replacements["k"] = "Natural-number frame position ranging over the copied segment from i through j."
        if identifier == "eq:mirror-query-grammar":
            replacements["A"] = "Actor identity named by a current-activation or actor-stack query."
        if identifier in {"eq:mirror-query-target", "eq:mirror-query-result"}:
            replacements["A"] = "Actor identity named by a current-activation or actor-stack query case."
        if identifier == "eq:all-instances-of":
            replacements.update(
                {
                    "C": "Exact runtime class whose currently live instances are requested; subclass instances are excluded.",
                    "x": "Object identity currently present in the VM cohort store and tested for exact runtime class C.",
                    "\\prec": "Implementation-chosen total order used only to give the returned snapshot sequence an observable order.",
                }
            )
        if identifier == "eq:mixin-applications":
            replacements.update(
                {
                    "C": "Live runtime class identity whose class record applies exactly mixin M.",
                    "M": "Exact static mixin whose currently live class applications are requested.",
                    "\\prec": "Implementation-chosen total order used only to give the returned snapshot sequence an observable order.",
                }
            )
        if identifier == "eq:reflective-descriptors":
            replacements["p"] = "Method, closure, or top-level provenance stored in an activation."
    else:
        replacements["g"] = "One sequential or simultaneous slot-initializer group."
    if section.startswith("12 "):
        replacements.update(
            {
                "G": "Nonempty, closed set of unreachable reference records selected for reclamation.",
                "K": "Set of reference-store keys retained after the selected garbage set is removed.",
                "x": "Reference identity whose payload or reachability successors are being inspected.",
                "i": "Natural-number iteration index in the least-fixed-point construction of reachability.",
                "A": "Actor identity whose private heap is restricted during collection.",
                "C": "Exact runtime class used to observe the effect of collection on instance enumeration.",
                "P": "Static program component whose referenced platform objects and atoms are roots.",
                "n": "Committed program version retained unchanged by collection.",
                "\\lambda_r": "Label of a reflective commit or rejection transition.",
                "\\lambda": "Actor or reflective transition label lifted through the optional GC wrapper.",
            }
        )
        weak_container_ids = {
            "eq:weak-container-records",
            "eq:weak-container-validity",
            "eq:weak-array-operations",
            "eq:weak-map-operations",
            "eq:gc-strong-payload",
            "eq:gc-roots-and-successors",
            "eq:gc-clear-weak-payload",
            "eq:gc-weak-array-effect",
            "eq:gc-weak-map-effect",
        }
        if identifier in weak_container_ids:
            replacements.update(
                {
                    "H": "Actor-local heap containing the WeakArray or WeakMap record.",
                    "C": "Runtime class of the WeakArray or WeakMap object.",
                    "y": "Value stored in a WeakArray cell.",
                    "v": "Value stored in, written to, or returned from a weak container.",
                    "k": "WeakMap key object identity.",
                    "i": "One-based WeakArray cell index.",
                    "r": "Arbitrary runtime record other than a WeakArray or WeakMap record.",
                }
            )
        if identifier == "eq:gc-roots-and-successors":
            replacements["L"] = "Candidate set of reference identities already known to be live."
        if identifier == "eq:gc-underlying-transition":
            replacements["A"] = "Actor invoking the labeled reflective commit or rejection."
        if identifier == "eq:gc-mixin-applications-effect":
            replacements["C"] = "Runtime class identity retained by the filtered mixin-application snapshot."
    if section.startswith("13 "):
        replacements.update(
            {
                "G": "Finite PEG grammar whose production map is used for this recognition, projection, or front-end stage.",
                "u": "Finite Unicode source text supplied to the parser.",
                "r": "PEG expression recognized at the indicated source offset.",
                "t": "Concrete parse tree carrying source spans and captured child trees.",
                "R": "Raw or identified surface-AST node, as fixed by the displayed stage.",
                "S": "Complete identified surface AST produced before core elaboration.",
                "X": "Set of Unicode scalar values accepted by a PEG character-set expression.",
                "N": "PEG nonterminal named by a grammar production.",
                "i": "Zero-based source offset at which recognition begins or a span starts.",
                "j": "Zero-based source offset immediately after a successful recognition or span.",
                "k": "Later source offset reached by the second part of a PEG sequence.",
                "h": "Diagnostic failure offset returned by PEG recognition.",
                "n": "Capture name attached to a concrete PEG node.",
                "c": "Unicode scalar matched by an atomic PEG character expression.",
                "q": "PEG success result or enclosing activation declaration, according to the displayed definition.",
                "m": "Metadata token or finite sequence length, according to the displayed definition.",
                "w": "Uninterpreted payload of a source metadata token.",
                "A": "Actor executing the ordinary parser, elaborator, or compiler service calls.",
                "B": "Immutable executable artifact produced by the compiler and admitted by the VM verifier.",
                "P": "Annotated static program consumed by the dynamic semantics.",
                "e": "Elaborated core expression paired with the annotated program.",
                "D": "Class-declaration identity used by a receiver annotation or derived program map.",
                "K": "Enclosing class-body declaration, or top, in an elaboration context.",
                "L": "Language registry, language identity, or candidate live set as fixed by the displayed definition.",
                "\\Gamma": "Static elaboration context containing the enclosing declarations, lexical binders, and return permissions.",
                "\\kappa": "Optional stable-identity retention map from structural node keys to declaration or site identities.",
                "\\lambda": "Language identity selecting an ordinary language object from the host registry.",
                "\\rho": "Finite PEG production map from nonterminals to parsing expressions.",
                "\\tau": "Tag identifying the kind of a metadata token.",
                "N_0": "Start nonterminal of the PEG grammar.",
                "\\prec": "Syntactic subexpression relation; r* ranges over repetition expressions occurring in a grammar production.",
            }
        )
        if identifier in {"eq:peg-atomic-recognition", "eq:peg-complete-parse"}:
            replacements["u_i"] = "Unicode scalar at zero-based source offset i."
        if identifier == "eq:ast-tree-projection":
            replacements["k"] = "Child position within the captured concrete-tree node."
        if identifier == "eq:metadata-trivia-gap":
            replacements.update(
                {
                    "X": "Earlier source-spanned token or AST node.",
                    "Y": "Later source-spanned token or AST node.",
                }
            )
        if identifier == "eq:surface-receiver-kind":
            replacements["x"] = "Source class name used by an explicit outer receiver."
        if identifier == "eq:static-binding-function":
            replacements.update(
                {
                    "B": "One lexical binder map from source names to stable declarations.",
                    "x": "Source identifier whose nearest lexical declaration is requested.",
                    "d": "Stable declaration bound to x by the nearest binder map.",
                    "i": "Zero-based position of a binder map in the innermost-first sequence.",
                    "j": "Least binder-map position containing x.",
                    "m": "Last valid position in the finite binder-map sequence.",
                }
            )
        if identifier == "eq:stable-ast-identity-validity":
            replacements.update(
                {
                    "a": "Declaration or expression node in the identified surface AST.",
                    "n": "Declaration or expression node whose stable identity is checked.",
                }
            )
        if identifier == "eq:static-well-formedness-components":
            replacements.update(
                {
                    "B": "One lexical binder map contained in an elaboration context.",
                    "a": "Source declaration or expression node quantified by the static check.",
                    "x": "Declared source name or formal parameter name being checked.",
                    "z": "Stable source-site identity selecting the elaboration context for an occurrence.",
                    "i": "Binder-map position within the elaboration context.",
                    "q": "Enclosing activation declaration recorded at a super-send source site.",
                }
            )
        if identifier in {"eq:expression-elaboration", "eq:cascade-expansion"}:
            replacements.update(
                {
                    "z": "Stable source-site identity attached to the surface expression.",
                    "p": "Surface pattern AST expanded before ordinary elaboration.",
                }
            )
        if identifier == "eq:cascade-expansion":
            replacements.update(
                {
                    "i": "One-based position of a cascaded message in source order.",
                    "m": "Number of messages in the cascade.",
                }
            )
        if identifier == "eq:front-end-reflective-change":
            replacements["n"] = "Current committed program-version number before the reflective transaction."
        if identifier == "eq:front-end-phase-behavior":
            replacements.update(
                {
                    "c": "Compilation already in progress and past front-end-image capture.",
                    "a": "Materialized parser, elaborator, or compiler activation that survives the commit.",
                }
            )
    if identifier in {"eq:tuple-platform-bindings", "eq:tuple-expansion"}:
        replacements.update(
            {
                "B": "Fixed platform Array class used for the tuple's temporary mutable array.",
                "R": "Fixed platform ReadOnlyTuple class receiving the final construction message.",
            }
        )
    if "pattern" in identifier:
        replacements["p"] = "Pattern or component-pattern AST interpreted by this elaboration."
    if identifier in {"eq:core-expressions", "eq:heap-records", "eq:method-activation"}:
        replacements["p"] = "Pattern payload or activation provenance, as indicated by the enclosing record constructor."
    if identifier == "eq:atom-payload":
        replacements.update(
            {
                "\\omega": "Canonical payload of an atomic literal.",
                "n": "Arbitrary-precision mathematical integer represented by an integer literal.",
                "q": "Exact rational value represented by a non-integral numeric literal.",
                "b": "Mathematical Boolean selected by true or false syntax.",
                "u": "Unicode-normal-form-C string used as a string or symbol payload.",
            }
        )

    for parameter in parameters:
        replacement = replacements.get(parameter["notation"])
        if replacement:
            parameter["description"] = replacement
    return parameters


def summary(title: str, kind: str) -> str:
    if kind == "Rule":
        return f"Gives the premises and conclusion of the {title} operational rule."
    if kind == "Grammar":
        return f"Introduces the alternatives and components of {title.lower()}."
    if kind == "Transition":
        return f"Defines the state change performed by {title.lower()}."
    if kind == "Judgment":
        return f"Defines the cases of the {title.lower()} judgment or partial operation."
    return f"Defines {title.lower()} and fixes the meaning of its displayed components."


def source_with_included_sections() -> str:
    main = MAIN.read_text()
    main = main.replace("\\input{actor-semantics}", ACTORS.read_text())
    main = main.replace("\\input{reflection-semantics}", REFLECTION.read_text())
    main = main.replace("\\input{gc-semantics}", GC.read_text())
    return main.replace("\\input{front-end-semantics}", FRONTEND.read_text())


def context_at(text: str, position: int) -> tuple[str, str]:
    section_matches = list(re.finditer(r"\\section\{([^}]*)\}", text[:position]))
    subsection_matches = list(re.finditer(r"\\subsection\{([^}]*)\}", text[:position]))
    section_number = len(section_matches)
    section_title = clean_title(section_matches[-1].group(1)) if section_matches else "Front matter"
    subsection_title = ""
    if subsection_matches and (not section_matches or subsection_matches[-1].start() > section_matches[-1].start()):
        subsection_title = clean_title(subsection_matches[-1].group(1))
    return f"{section_number} {section_title}", subsection_title


def build_entries() -> list[dict[str, object]]:
    text = source_with_included_sections()
    numbers = read_equation_numbers()
    entries: list[dict[str, object]] = []

    equation_pattern = re.compile(
        r"\\begin\{equation\}\\label\{(eq:[^}]+)\}(.*?)\\end\{equation\}",
        re.DOTALL,
    )
    for match in equation_pattern.finditer(text):
        identifier = match.group(1)
        formula = clean_formula(match.group(2))
        section, subsection = context_at(text, match.start())
        title = title_from_id(identifier)
        kind = classify(formula, False)
        entries.append(
            {
                "id": identifier.replace(":", "-"),
                "sourceId": identifier,
                "number": numbers.get(identifier, "—"),
                "title": title,
                "kind": kind,
                "section": section,
                "subsection": subsection,
                "summary": summary(title, kind),
                "formula": formula,
                "parameters": refine_descriptions(parameter_list(formula), identifier, section),
                "order": match.start(),
            }
        )

    rule_pattern = re.compile(r"\\quad\(\\rulelabel\{([^}]+)\}\)")
    for match in rule_pattern.finditer(text):
        name = match.group(1)
        formula = rule_formula(text, match.start())
        section, subsection = context_at(text, match.start())
        title = (
            name.replace("-", " ")
            .title()
            .replace("Dnu", "DNU")
            .replace("Rr ", "RR ")
            .replace("Gc ", "GC ")
        )
        entries.append(
            {
                "id": "rule-" + name.lower(),
                "sourceId": name,
                "number": name,
                "title": title,
                "kind": "Rule",
                "section": section,
                "subsection": subsection,
                "summary": summary(title, "Rule"),
                "formula": formula,
                "parameters": refine_descriptions(parameter_list(formula), name, section),
                "order": match.start(),
            }
        )

    entries.sort(key=lambda entry: int(entry["order"]))
    for entry in entries:
        entry.pop("order")
    return entries


def main() -> None:
    entries = build_entries()
    OUTPUT.write_text(json.dumps(entries, indent=2, ensure_ascii=True) + "\n")
    equations = sum(entry["kind"] != "Rule" for entry in entries)
    rules = sum(entry["kind"] == "Rule" for entry in entries)
    print(f"wrote {len(entries)} entries ({equations} numbered forms, {rules} rules) to {OUTPUT}")


if __name__ == "__main__":
    main()
