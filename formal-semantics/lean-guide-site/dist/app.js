const layers = {
  static: {
    index: "01 · foundations",
    title: "Identity, syntax, and finite stores",
    text: "Distinct identity types prevent accidental aliasing. Core syntax names every annotation the runtime will need. FiniteStore gives partial maps an exact executable domain—the key prerequisite for reflection, enumeration, and collection.",
    files: ["Id.lean", "FiniteStore.lean", "Syntax.lean", "SurfaceSyntax.lean"]
  },
  lookup: {
    index: "02 · object model",
    title: "Program, heap, class chains, and dispatch",
    text: "Static mixin definitions live in Program; runtime classes and objects live in Heap. A unique finite class chain supports unrestricted, public, and protected lookup, followed by ordinary, implicit, self, outer, super, or DNU dispatch.",
    files: ["Program.lean", "Heap.lean", "ClassChain.lean", "Lookup.lean", "Dispatch.lean"]
  },
  sequential: {
    index: "03 · local execution",
    title: "The complete sequential machine",
    text: "Small-step relations cover evaluation order, invocation, closures, returns, slots, class construction, initialization, object literals, exceptions, compound literals, and top-level entry. Their union is deterministic and preserves a global well-formedness invariant.",
    files: ["SequentialStep.lean", "SequentialWellFormed.lean", "Closures.lean", "Returns.lean", "TopLevel.lean"]
  },
  actors: {
    index: "04 · distributed execution",
    title: "Actors, eventual sends, promises, and E-order",
    text: "The sequential machine is lifted into isolated actor heaps. Far references normalize at boundaries, eventual sends create promises immediately, turns are FIFO, and causal packet delivery respects E-order while global scheduling remains nondeterministic.",
    files: ["ActorSemantics.lean", "ActorTurns.lean", "ActorTransitions.lean", "ActorPromiseSafety.lean"]
  },
  reflection: {
    index: "05 · causal change",
    title: "Reflection, source images, and debugger control",
    text: "Mirror authority gates exact operations. A transaction prepares and validates a complete candidate before one atomic commit. Stack images expose current terms and locations; whole stacks can be copied or replaced and then resumed by ordinary execution.",
    files: ["ReflectionCommands.lean", "ReflectionTransactions.lean", "ReflectionDebugger.lean", "ReflectionSourceImage.lean"]
  },
  gc: {
    index: "06 · optional observation",
    title: "Strong reachability, ephemerons, and collection",
    text: "An optional overlay computes exact roots, unconditional strong closure, and the WeakMap conditional fixed point. Collection prunes all heap stores and clears WeakArray/WeakMap observations atomically, yielding a stuttering refinement of the base machine.",
    files: ["StrongReferences.lean", "ConditionalReachability.lean", "GarbageCollection.lean", "CollectingExecution.lean"]
  },
  frontend: {
    index: "07 · source to execution",
    title: "PEG, elaboration, artifacts, and metacircularity",
    text: "The checked pipeline runs from PEG recognition through semantic projection, stable identification, surface checks, elaboration, Program derivation, and core validation. Replaceable Newspeak front-end objects meet a fixed artifact-admission boundary.",
    files: ["PEG.lean", "FrontEnd.lean", "CompleteStaticChecking.lean", "Metacircularity.lean", "Properties.lean"]
  }
};

const sourceFiles = [
  "README.md", "FORMALIZATION.md", "THEOREMS.md", "Newspeak.lean",
  "Newspeak/ActorCreation.lean", "Newspeak/ActorDeterminism.lean", "Newspeak/ActorEventualSends.lean",
  "Newspeak/ActorExecution.lean", "Newspeak/ActorPromiseSafety.lean", "Newspeak/ActorRoots.lean",
  "Newspeak/ActorRouting.lean", "Newspeak/ActorSemantics.lean", "Newspeak/ActorSystemSteps.lean",
  "Newspeak/ActorTransitions.lean", "Newspeak/ActorTurns.lean", "Newspeak/BodiedMixinDerivation.lean",
  "Newspeak/Bodies.lean", "Newspeak/ClassApplications.lean", "Newspeak/ClassChain.lean",
  "Newspeak/ClassConstruction.lean", "Newspeak/ClassDerivation.lean", "Newspeak/Closures.lean",
  "Newspeak/CollectingExecution.lean", "Newspeak/CompleteStaticChecking.lean", "Newspeak/CompoundLiterals.lean",
  "Newspeak/ConditionalReachability.lean", "Newspeak/ConditionalReachabilityProofs.lean", "Newspeak/CoreValidity.lean",
  "Newspeak/DerivedProgramImage.lean", "Newspeak/DirectProgramDerivation.lean", "Newspeak/Dispatch.lean",
  "Newspeak/DnuFallback.lean", "Newspeak/EmbeddedArtifacts.lean", "Newspeak/Enclosing.lean",
  "Newspeak/ExceptionBoundary.lean", "Newspeak/ExpressionOrder.lean", "Newspeak/FactoryInitialization.lean",
  "Newspeak/FiniteStore.lean", "Newspeak/FrontEnd.lean", "Newspeak/GarbageCollection.lean",
  "Newspeak/GarbageCollectionState.lean", "Newspeak/Heap.lean", "Newspeak/HeapEnumeration.lean",
  "Newspeak/Id.lean", "Newspeak/IdentificationElaboration.lean", "Newspeak/ImplicitClassDispatch.lean",
  "Newspeak/ImplicitDispatch.lean", "Newspeak/InitializationCoordinator.lean", "Newspeak/InstanceAllocation.lean",
  "Newspeak/LexicalBinding.lean", "Newspeak/Lookup.lean", "Newspeak/LookupProofs.lean",
  "Newspeak/LookupRules.lean", "Newspeak/MessageEvaluation.lean", "Newspeak/Metacircularity.lean",
  "Newspeak/MethodInvocation.lean", "Newspeak/MixinChainDerivation.lean", "Newspeak/Modules.lean",
  "Newspeak/NewspeakGrammar.lean", "Newspeak/NewspeakSurfaceActions.lean", "Newspeak/ObjectLiteralDerivation.lean",
  "Newspeak/ObjectLiteralsAndNestedClasses.lean", "Newspeak/ObjectSlots.lean", "Newspeak/OrdinarySend.lean",
  "Newspeak/OuterDispatch.lean", "Newspeak/PEG.lean", "Newspeak/PEGCertificate.lean",
  "Newspeak/PEGCertificateSoundness.lean", "Newspeak/PEGProjection.lean", "Newspeak/PEGWellFormed.lean",
  "Newspeak/Program.lean", "Newspeak/Properties.lean", "Newspeak/ReflectionActivationUpdates.lean",
  "Newspeak/ReflectionAuthority.lean", "Newspeak/ReflectionCommands.lean", "Newspeak/ReflectionCommutation.lean",
  "Newspeak/ReflectionDebugger.lean", "Newspeak/ReflectionHeapUpdates.lean", "Newspeak/ReflectionQueries.lean",
  "Newspeak/ReflectionRuntimePreparation.lean", "Newspeak/ReflectionSourceImage.lean", "Newspeak/ReflectionStackImages.lean",
  "Newspeak/ReflectionTransactions.lean", "Newspeak/ReflectionVMs.lean", "Newspeak/ReflectionValidation.lean",
  "Newspeak/ReflectionVersionObservation.lean", "Newspeak/RequestResolution.lean", "Newspeak/Returns.lean",
  "Newspeak/RuntimeRoots.lean", "Newspeak/SequentialInitialization.lean", "Newspeak/SequentialStep.lean",
  "Newspeak/SequentialWellFormed.lean", "Newspeak/SimulatorRefinement.lean", "Newspeak/SlotInitialization.lean",
  "Newspeak/SourceIdentification.lean", "Newspeak/StaticElaboration.lean", "Newspeak/StrongReachabilityProofs.lean",
  "Newspeak/StrongReferences.lean", "Newspeak/StructuralArtifactDerivation.lean", "Newspeak/SurfaceNodes.lean",
  "Newspeak/SurfaceSyntax.lean", "Newspeak/SurfaceWellFormed.lean", "Newspeak/Syntax.lean",
  "Newspeak/SynthesizedDeclarations.lean", "Newspeak/TopLevel.lean", "Newspeak/V5Bytecode.lean",
  "Newspeak/WeakContainers.lean", "Newspeak/WellFormed.lean"
];

const sourceKeywords = {
  "Id.lean": "identity object class activation promise mirror actor selector",
  "Lookup.lean": "method access public protected private class chain",
  "SequentialStep.lean": "small step deterministic evaluation machine",
  "ActorSemantics.lean": "actor promise far reference packet causal",
  "ReflectionTransactions.lean": "reflection atomic validation commit failure",
  "GarbageCollection.lean": "gc weak array map ephemeron collection",
  "FrontEnd.lean": "peg ast source identify elaborate core",
  "Metacircularity.lean": "parser compiler simulator admission certificate",
  "Properties.lean": "theorem index exports all proofs"
};

function renderLayer(key) {
  const detail = layers[key];
  const box = document.querySelector("#arch-detail");
  if (!detail || !box) return;
  box.innerHTML = `
    <span class="arch-index">${detail.index}</span>
    <h3>${detail.title}</h3>
    <p>${detail.text}</p>
    <div class="arch-files">${detail.files.map(file =>
      `<a href="source/Newspeak/${file}" target="_blank">${file}</a>`).join("")}</div>`;
  document.querySelectorAll(".arch-rail button").forEach(button => {
    button.setAttribute("aria-selected", String(button.dataset.layer === key));
  });
}

document.querySelectorAll(".arch-rail button").forEach(button => {
  button.addEventListener("click", () => renderLayer(button.dataset.layer));
});
renderLayer("static");

const lookupCopy = {
  unrestricted: "Accept the first direct definition, regardless of access. This mode is reserved for system lookup such as DNU selection.",
  public: "Accept only public methods. A private method is skipped; a protected method is a barrier that stops the search with failure.",
  protected: "Accept public or protected methods. Private methods are skipped and cannot be inherited through this path."
};
document.querySelectorAll(".mode-buttons button").forEach(button => {
  button.addEventListener("click", () => {
    document.querySelectorAll(".mode-buttons button").forEach(item => item.classList.remove("active"));
    button.classList.add("active");
    document.querySelector("#lookup-explanation").textContent = lookupCopy[button.dataset.mode];
  });
});

const proofSteps = [
  { lines: [1,2,3], title: "State the claim", text: "Two pieces of evidence, h₁ and h₂, say that lookup produced r₁ and r₂ under identical inputs. The goal after the colon is to prove r₁ = r₂." },
  { lines: [4], title: "Open the first derivation", text: "Lookup is defined by existence of a class chain plus the result of scanning it. rcases extracts chain₁, evidence hc₁ that it is valid, and equation hr₁ for its scan result." },
  { lines: [5], title: "Open the second derivation", text: "The second lookup evidence yields chain₂, its validity proof hc₂, and its scan equation hr₂." },
  { lines: [6,7], title: "Use the structural theorem", text: "ClassChain.unique says a starting class has only one finite chain to Top. Once chain₁ = chain₂, subst replaces the second chain everywhere with the first." },
  { lines: [8], title: "Rewrite both results", text: "Both r₁ and r₂ are now equal to the same executable scan of the same chain. Rewriting those two equations closes the goal." }
];
let proofIndex = 0;
function renderProofStep() {
  const step = proofSteps[proofIndex];
  document.querySelectorAll("[data-proof-line]").forEach(line => {
    line.classList.toggle("highlight", step.lines.includes(Number(line.dataset.proofLine)));
  });
  document.querySelector("#proof-step-number").textContent = `${proofIndex + 1} / ${proofSteps.length}`;
  document.querySelector("#proof-step-title").textContent = step.title;
  document.querySelector("#proof-step-text").textContent = step.text;
  document.querySelector("#proof-prev").disabled = proofIndex === 0;
  document.querySelector("#proof-next").disabled = proofIndex === proofSteps.length - 1;
}
document.querySelector("#proof-prev")?.addEventListener("click", () => { proofIndex -= 1; renderProofStep(); });
document.querySelector("#proof-next")?.addEventListener("click", () => { proofIndex += 1; renderProofStep(); });
renderProofStep();

const sourceList = document.querySelector("#source-list");
const sourceCount = document.querySelector("#source-count");
function renderSources(query = "") {
  const normalized = query.trim().toLowerCase();
  const matches = sourceFiles.filter(path => {
    const base = path.split("/").pop();
    const keywords = sourceKeywords[base] || "";
    return `${path} ${keywords}`.toLowerCase().includes(normalized);
  });
  sourceCount.textContent = `${matches.length} of ${sourceFiles.length} files`;
  sourceList.innerHTML = matches.length ? matches.map(path => {
    const name = path.split("/").pop();
    const kind = path.endsWith(".lean") ? "Lean" : "notes";
    return `<a class="source-file" href="source/${path}" target="_blank"><span>${name}</span><small>${kind} ↗</small></a>`;
  }).join("") : `<div class="empty-state">No source file matches “${query.replace(/[<>&]/g, "")}”.</div>`;
}
document.querySelector("#source-search")?.addEventListener("input", event => renderSources(event.target.value));
renderSources();

const menuButton = document.querySelector("#menu-button");
const sidebar = document.querySelector("#sidebar");
menuButton?.addEventListener("click", () => {
  const open = sidebar.classList.toggle("open");
  menuButton.setAttribute("aria-expanded", String(open));
});
document.querySelectorAll(".sidebar nav a").forEach(link => {
  link.addEventListener("click", () => {
    sidebar.classList.remove("open");
    menuButton?.setAttribute("aria-expanded", "false");
  });
});

const sections = [...document.querySelectorAll("main section[id]")];
const navLinks = [...document.querySelectorAll(".sidebar nav a")];
const observer = new IntersectionObserver(entries => {
  const visible = entries.filter(entry => entry.isIntersecting)
    .sort((a, b) => b.intersectionRatio - a.intersectionRatio)[0];
  if (!visible) return;
  navLinks.forEach(link => link.classList.toggle("active", link.hash === `#${visible.target.id}`));
}, { rootMargin: "-20% 0px -65% 0px", threshold: [0, .2, .6] });
sections.forEach(section => observer.observe(section));

function updateProgress() {
  const max = document.documentElement.scrollHeight - window.innerHeight;
  const ratio = max > 0 ? window.scrollY / max : 0;
  document.querySelector("#reading-progress").style.width = `${Math.min(100, Math.max(0, ratio * 100))}%`;
}
document.addEventListener("scroll", updateProgress, { passive: true });
updateProgress();

document.querySelectorAll(".code-card").forEach(card => {
  card.addEventListener("toggle", () => {
    const label = card.querySelector(".disclosure");
    if (label && !card.open) label.textContent = "Show Lean";
  });
});
