import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import katex from 'katex';

const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const referenceRoot = path.resolve(scriptDir, '..');
const semanticsRoot = path.resolve(referenceRoot, '..');
const outputRoot = process.argv[2] && path.resolve(process.argv[2]);

if (!outputRoot) {
  throw new Error('usage: node export_newspeak_site.mjs OUTPUT_DIRECTORY');
}
if (fs.existsSync(outputRoot) && fs.readdirSync(outputRoot).length) {
  throw new Error(`output directory is not empty: ${outputRoot}`);
}

const definitions = JSON.parse(
  fs.readFileSync(path.join(referenceRoot, 'app', 'definitions.generated.json'), 'utf8'),
);

const mathMacros = {
  '\\kw': '\\mathsf{#1}',
  '\\undef': '\\mathord{\\uparrow}',
  '\\nil': '\\mathsf{nil}',
  '\\Top': '\\mathsf{Top}',
  '\\Object': '\\mathsf{Object}',
  '\\Public': '\\mathsf{public}',
  '\\Protected': '\\mathsf{protected}',
  '\\Private': '\\mathsf{private}',
  '\\dom': '\\mathop{\\mathrm{dom}}',
  '\\classof': '\\mathop{\\mathrm{classOf}}',
  '\\super': '\\mathop{\\mathrm{super}}',
  '\\mixin': '\\mathop{\\mathrm{mixin}}',
  '\\decl': '\\mathop{\\mathrm{decl}}',
  '\\access': '\\mathop{\\mathrm{access}}',
  '\\selector': '\\mathop{\\mathrm{selector}}',
  '\\methods': '\\mathop{\\mathrm{methods}}',
  '\\lookup': '\\mathop{\\mathrm{lookup}}',
  '\\definingClass': '\\mathop{\\mathrm{definingClass}}',
  '\\kws': '\\mathsf{#1\\mathord{:}}',
  '\\selsym': '\\mathord{\\#}\\text{\\texttt{#1}}',
  '\\dnu': '\\mathsf{doesNotUnderstand\\mathord{:}}',
  '\\PastFuture': '\\text{\\texttt{Past`Future}}',
};

const notationReplacements = [
  ['\\mathcal A', '𝒜'], ['\\mathcal X', '𝒳'], ['\\mathcal Q', '𝒬'],
  ['\\mathcal N', '𝒩'], ['\\mathcal E', 'ℰ'], ['\\mathcal D', '𝒟'],
  ['\\mathcal H', 'ℋ'], ['\\mathcal L', 'ℒ'], ['\\mathcal P', '𝒫'],
  ['\\widehat H_A', 'Ĥ_A'], ['\\Gamma', 'Γ'], ['\\Phi', 'Φ'],
  ['\\Pi', 'Π'], ['\\Omega', 'Ω'], ['\\Sigma', 'Σ'], ['\\Delta', 'Δ'],
  ['\\kappa_w', 'κ_w'], ['\\kappa', 'κ'], ['\\chi_C', 'χ_C'],
  ['\\chi_b', 'χ_b'], ['\\chi_a', 'χ_a'], ['\\chi', 'χ'],
  ['\\mu', 'μ'], ['\\beta', 'β'], ['\\theta', 'θ'], ['\\gamma', 'γ'],
  ['\\rho', 'ρ'], ['\\sigma', 'σ'], ['\\eta', 'η'], ['\\phi', 'φ'],
  ['\\delta', 'δ'], ['\\nu', 'ν'], ['\\iota', 'ι'], ['\\tau', 'τ'],
  ['\\lambda', 'λ'], ['\\alpha', 'α'], ['\\xi', 'ξ'], ['\\omega', 'ω'],
  ['\\varepsilon', 'ε'], ['\\epsilon', 'ε'], ['\\pi', 'π'], ['\\ell', 'ℓ'],
  ['\\bar\\lambda', 'λ̄'], ['\\bar\\ell', 'ℓ̄'], ['\\bar x', 'x̄'],
  ['\\bar o', 'ō'], ['\\bar e', 'ē'], ['\\bar s', 's̄'], ['\\bar g', 'ḡ'],
  ['\\bar d', 'd̄'], ['\\bar m', 'm̄'], ['\\bar k', 'k̄'], ['\\bar p', 'p̄'],
];

const escapeHtml = (value) => String(value)
  .replaceAll('&', '&amp;')
  .replaceAll('<', '&lt;')
  .replaceAll('>', '&gt;')
  .replaceAll('"', '&quot;')
  .replaceAll("'", '&#39;');

const readableNotation = (value) => notationReplacements.reduce(
  (result, [source, replacement]) => result.replaceAll(source, replacement),
  value,
);

const renderMath = (formula, displayMode = false) => katex.renderToString(formula, {
  displayMode,
  throwOnError: false,
  strict: 'ignore',
  output: 'htmlAndMathml',
  macros: mathMacros,
});

const searchableText = (entry) => [
  entry.number,
  entry.sourceId,
  entry.title,
  entry.kind,
  entry.section,
  entry.subsection,
  entry.summary,
  entry.formula,
  ...entry.parameters.flatMap((parameter) => [
    parameter.notation,
    readableNotation(parameter.notation),
    parameter.description,
    readableNotation(parameter.description),
  ]),
].join(' ').toLocaleLowerCase();

function groupedEntries() {
  const groups = new Map();
  for (const entry of definitions) {
    const group = groups.get(entry.section) ?? [];
    group.push(entry);
    groups.set(entry.section, group);
  }
  return groups;
}

function definitionLinks() {
  return Array.from(groupedEntries(), ([section, entries]) => `
    <section class="section-group">
      <h3 class="section-label">${escapeHtml(section)}</h3>
      <div class="definition-links">
        ${entries.map((entry) => `
          <a class="definition-link" data-entry-id="${escapeHtml(entry.id)}" href="#${escapeHtml(entry.id)}">
            <span class="definition-link-number">${escapeHtml(entry.number)}</span>
            <span>${escapeHtml(entry.title)}</span>
          </a>`).join('')}
      </div>
    </section>`).join('');
}

function definitionCard(entry) {
  const parameters = entry.parameters.length
    ? entry.parameters.map((parameter) => `
        <div class="parameter-row">
          <dt><span class="math-inline">${renderMath(parameter.notation)}</span></dt>
          <dd>${escapeHtml(readableNotation(parameter.description))}</dd>
        </div>`).join('')
    : '<div class="parameter-row parameter-empty"><dd>No explicit parameters or record components.</dd></div>';

  return `
    <article class="definition-card" id="${escapeHtml(entry.id)}" data-search="${escapeHtml(searchableText(entry))}">
      <header class="card-header">
        <div class="card-kicker">
          <span class="definition-number">${escapeHtml(entry.number)}</span>
          <span class="definition-kind">${escapeHtml(entry.kind)}</span>
          <span class="definition-section">${escapeHtml(entry.subsection || entry.section)}</span>
        </div>
        <h2 class="card-title">${escapeHtml(entry.title)}</h2>
        <p class="card-summary">${escapeHtml(entry.summary)}</p>
        <a class="anchor-link" href="#${escapeHtml(entry.id)}" aria-label="Link to ${escapeHtml(entry.title)}" title="Permanent link">#</a>
      </header>
      <div class="formal-source">
        <div class="source-label">Formal definition</div>
        <div class="math-display">${renderMath(entry.formula, true)}</div>
      </div>
      <section class="parameter-panel">
        <h3>Parameters and components</h3>
        <dl class="parameter-list">${parameters}</dl>
      </section>
    </article>`;
}

const referenceHtml = `<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="description" content="Rendered definitions, rules, and parameter descriptions for the Newspeak formal semantics.">
  <title>Newspeak Semantics Reference</title>
  <link rel="icon" href="favicon.svg" type="image/svg+xml">
  <link rel="stylesheet" href="assets/reference.css">
  <link rel="stylesheet" href="assets/static.css">
</head>
<body>
  <div class="reference-shell">
    <header class="masthead">
      <div class="masthead-inner">
        <div>
          <p class="eyebrow">Design draft 0.14 · Companion index</p>
          <h1 class="site-title">Newspeak Semantics Reference</h1>
          <nav class="site-links" aria-label="Related formal-semantics resources">
            <a href="../">Overview</a><a href="../newspeak-semantics.pdf">PDF</a><a href="../lean-guide/">Lean guide</a>
          </nav>
        </div>
        <label class="search-wrap">
          <span class="sr-only">Search definitions and rules</span>
          <span aria-hidden="true" class="search-icon">⌕</span>
          <input id="definition-search" class="definition-search" type="search" placeholder="Search by name, number, notation, or description" autocomplete="off">
          <span aria-hidden="true" class="search-key">/</span>
        </label>
        <span class="count-pill"><span id="visible-count">${definitions.length}</span> / ${definitions.length}</span>
      </div>
    </header>
    <div class="workspace">
      <aside class="definition-index">
        <div class="index-heading"><h2>All definitions</h2><span><span class="directory-count">${definitions.length}</span> shown</span></div>
        <nav aria-label="Definition index">${definitionLinks()}</nav>
      </aside>
      <main class="main-column">
        <details class="mobile-directory">
          <summary>All definitions (<span class="directory-count">${definitions.length}</span>)</summary>
          <nav class="mobile-links" aria-label="Definition index">${definitionLinks()}</nav>
        </details>
        <div class="intro-panel"><p><strong>Every numbered form and named operational rule</strong> from the current semantics draft appears below. Each anchor is stable; the typeset definition is followed by descriptions of every metavariable, parameter, and record component used in that entry.</p></div>
        <p id="result-heading" class="result-heading" aria-live="polite">${definitions.length} definitions and rules in document order</p>
        <div id="definitions" class="definitions">${definitions.map(definitionCard).join('')}</div>
        <div id="empty-state" class="empty-state" hidden>No definition matches this search. Try a rule name, equation number, or metavariable.</div>
      </main>
    </div>
  </div>
  <script src="assets/app.js"></script>
</body>
</html>`;

const referenceJs = `(() => {
  const input = document.querySelector('#definition-search');
  const cards = [...document.querySelectorAll('.definition-card')];
  const links = [...document.querySelectorAll('.definition-link')];
  const groups = [...document.querySelectorAll('.section-group')];
  const visibleCount = document.querySelector('#visible-count');
  const directoryCounts = [...document.querySelectorAll('.directory-count')];
  const heading = document.querySelector('#result-heading');
  const empty = document.querySelector('#empty-state');

  function update() {
    const raw = input.value.trim();
    const query = raw.toLocaleLowerCase();
    const visible = new Set();
    for (const card of cards) {
      const show = !query || card.dataset.search.includes(query);
      card.hidden = !show;
      if (show) visible.add(card.id);
    }
    for (const link of links) link.hidden = !visible.has(link.dataset.entryId);
    for (const group of groups) group.hidden = !group.querySelector('.definition-link:not([hidden])');
    const count = visible.size;
    visibleCount.textContent = count;
    for (const item of directoryCounts) item.textContent = count;
    heading.textContent = query ? count + ' matches for “' + raw + '”' : cards.length + ' definitions and rules in document order';
    empty.hidden = count !== 0;
  }

  input.addEventListener('input', update);
  window.addEventListener('keydown', (event) => {
    const target = event.target;
    const typing = target?.tagName === 'INPUT' || target?.tagName === 'TEXTAREA' || target?.isContentEditable;
    if (event.key === '/' && !typing) { event.preventDefault(); input.focus(); }
    if (event.key === 'Escape' && document.activeElement === input) { input.value = ''; update(); input.blur(); }
  });
  window.addEventListener('hashchange', () => {
    const target = document.getElementById(location.hash.slice(1));
    if (target?.hidden) { input.value = ''; update(); }
  });
  update();
})();`;

const referenceCss = `
[hidden] { display: none !important; }
.definition-search { width: 100%; border: 1px solid #afc4d8; outline: none; }
.definition-search:focus { border-color: #3685ce; box-shadow: 0 0 0 3px rgb(54 133 206 / 18%); }
.search-icon { display: grid; place-items: center; font-size: 1.35rem; }
.site-links { display: flex; gap: .8rem; margin-top: .25rem; font-size: .75rem; }
.site-links a { color: #406d97; text-decoration: none; }
.site-links a:hover, .site-links a:focus-visible { color: #175ea8; text-decoration: underline; }
.anchor-link { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-weight: 800; }
.parameter-empty { grid-column: 1 / -1; }
.parameter-empty dd { font-style: italic; }
`;

const landingHtml = `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="description" content="Quasi-formal and Lean formalizations of the Newspeak programming language.">
<title>Newspeak Formal Semantics</title><style>
:root{color-scheme:light;--ink:#142b3d;--blue:#175ea8;--pale:#edf5fc;--line:#c8d8e7}*{box-sizing:border-box}body{margin:0;background:linear-gradient(135deg,#f5f9fd,#e8f2fb);color:var(--ink);font:17px/1.6 system-ui,-apple-system,sans-serif}main{max-width:980px;margin:auto;padding:8vh 24px}.eyebrow{color:var(--blue);font-size:.78rem;font-weight:800;letter-spacing:.13em;text-transform:uppercase}h1{max-width:760px;margin:.2rem 0 1rem;font:clamp(2.6rem,7vw,5rem)/1.02 Georgia,serif}.lead{max-width:760px;color:#496174;font-size:1.18rem}.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:18px;margin-top:3rem}.card{display:block;border:1px solid var(--line);border-radius:14px;background:#fff;padding:24px;box-shadow:0 12px 34px #193f6210;color:inherit;text-decoration:none}.card:hover{border-color:#4e91cc;transform:translateY(-2px)}.card strong{display:block;margin-bottom:.4rem;color:#153f65;font:1.45rem Georgia,serif}.card span{color:#607486}.primary{grid-column:1/-1;background:#163f67;color:#fff}.primary strong,.primary span{color:inherit}.foot{margin-top:2.5rem;color:#63788a;font-size:.85rem}@media(max-width:680px){.grid{grid-template-columns:1fr}.primary{grid-column:auto}}
</style></head><body><main><p class="eyebrow">Newspeak programming language</p><h1>Formal semantics</h1>
<p class="lead">A complete operational account of Newspeak, accompanied by an executable Lean formalization and navigable references for readers.</p>
<div class="grid"><a class="card primary" href="newspeak-semantics.pdf"><strong>Read the semantics</strong><span>The current 90-page quasi-formal specification (PDF).</span></a>
<a class="card" href="reference/"><strong>Definition reference</strong><span>Rendered definitions and explanations of every parameter, with full-text search and stable anchors.</span></a>
<a class="card" href="lean-guide/"><strong>Guide to the Lean formalization</strong><span>A top-down interactive essay with collapsible code and links to complete source files.</span></a></div>
<p class="foot">Design draft 0.14 · The Lean development builds without <code>sorry</code>, <code>admit</code>, or additional axioms.</p></main></body></html>`;

const referenceOutput = path.join(outputRoot, 'reference');
const guideOutput = path.join(outputRoot, 'lean-guide');
const assetsOutput = path.join(referenceOutput, 'assets');
fs.mkdirSync(assetsOutput, { recursive: true });

fs.writeFileSync(path.join(outputRoot, 'index.html'), landingHtml);
fs.copyFileSync(path.join(semanticsRoot, 'newspeak-semantics.pdf'), path.join(outputRoot, 'newspeak-semantics.pdf'));
fs.writeFileSync(
  path.join(referenceOutput, 'index.html'),
  referenceHtml.replace(/^[ \t]+$/gm, ''),
);
fs.writeFileSync(path.join(assetsOutput, 'app.js'), referenceJs);
fs.writeFileSync(path.join(assetsOutput, 'static.css'), referenceCss);
fs.copyFileSync(path.join(referenceRoot, 'public', 'favicon.svg'), path.join(referenceOutput, 'favicon.svg'));

const builtCssRoot = path.join(referenceRoot, 'dist', 'client', '_next', 'static', 'css');
const builtCssName = fs.readdirSync(builtCssRoot).find((name) => name.endsWith('.css'));
const builtCss = fs.readFileSync(path.join(builtCssRoot, builtCssName), 'utf8')
  .replaceAll('/_next/static/media/', 'fonts/')
  .replaceAll('../media/', 'fonts/');
fs.writeFileSync(path.join(assetsOutput, 'reference.css'), builtCss);
fs.cpSync(
  path.join(referenceRoot, 'dist', 'client', '_next', 'static', 'media'),
  path.join(assetsOutput, 'fonts'),
  { recursive: true },
);
fs.cpSync(path.join(semanticsRoot, 'lean-guide-site', 'dist'), guideOutput, { recursive: true });

console.log(`exported ${definitions.length} definitions and both companion pages to ${outputRoot}`);
