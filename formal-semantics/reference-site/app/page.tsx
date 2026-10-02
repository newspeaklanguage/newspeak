'use client';

import { useEffect, useMemo, useRef, useState } from 'react';
import { Hash, Search } from 'lucide-react';
import katex from 'katex';

import { Input } from '@/components/ui/input';
import rawDefinitions from './definitions.generated.json';

type Parameter = {
  notation: string;
  description: string;
};

type DefinitionEntry = {
  id: string;
  sourceId: string;
  number: string;
  title: string;
  kind: 'Definition' | 'Grammar' | 'Judgment' | 'Transition' | 'Rule';
  section: string;
  subsection: string;
  summary: string;
  formula: string;
  parameters: Parameter[];
};

const definitions = rawDefinitions as DefinitionEntry[];

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
} as const;

function MathExpression({
  formula,
  display = false,
}: {
  formula: string;
  display?: boolean;
}) {
  const rendered = useMemo(
    () =>
      katex.renderToString(formula, {
        displayMode: display,
        throwOnError: false,
        strict: 'ignore',
        output: 'htmlAndMathml',
        macros: mathMacros,
      }),
    [display, formula],
  );

  const Element = display ? 'div' : 'span';
  return (
    <Element
      className={display ? 'math-display' : 'math-inline'}
      dangerouslySetInnerHTML={{ __html: rendered }}
    />
  );
}

const notationReplacements: Array<[string, string]> = [
  ['\\mathcal A', '𝒜'],
  ['\\mathcal X', '𝒳'],
  ['\\mathcal Q', '𝒬'],
  ['\\mathcal N', '𝒩'],
  ['\\mathcal E', 'ℰ'],
  ['\\mathcal D', '𝒟'],
  ['\\mathcal H', 'ℋ'],
  ['\\mathcal L', 'ℒ'],
  ['\\mathcal P', '𝒫'],
  ['\\widehat H_A', 'Ĥ_A'],
  ['\\Gamma', 'Γ'],
  ['\\Phi', 'Φ'],
  ['\\Pi', 'Π'],
  ['\\Omega', 'Ω'],
  ['\\Sigma', 'Σ'],
  ['\\Delta', 'Δ'],
  ['\\kappa_w', 'κ_w'],
  ['\\kappa', 'κ'],
  ['\\chi_C', 'χ_C'],
  ['\\chi_b', 'χ_b'],
  ['\\chi_a', 'χ_a'],
  ['\\chi', 'χ'],
  ['\\mu', 'μ'],
  ['\\beta', 'β'],
  ['\\theta', 'θ'],
  ['\\gamma', 'γ'],
  ['\\rho', 'ρ'],
  ['\\sigma', 'σ'],
  ['\\eta', 'η'],
  ['\\phi', 'φ'],
  ['\\delta', 'δ'],
  ['\\nu', 'ν'],
  ['\\iota', 'ι'],
  ['\\tau', 'τ'],
  ['\\lambda', 'λ'],
  ['\\alpha', 'α'],
  ['\\xi', 'ξ'],
  ['\\omega', 'ω'],
  ['\\varepsilon', 'ε'],
  ['\\epsilon', 'ε'],
  ['\\pi', 'π'],
  ['\\ell', 'ℓ'],
  ['\\bar\\lambda', 'λ̄'],
  ['\\bar\\ell', 'ℓ̄'],
  ['\\bar x', 'x̄'],
  ['\\bar o', 'ō'],
  ['\\bar e', 'ē'],
  ['\\bar s', 's̄'],
  ['\\bar g', 'ḡ'],
  ['\\bar d', 'd̄'],
  ['\\bar m', 'm̄'],
  ['\\bar k', 'k̄'],
  ['\\bar p', 'p̄'],
];

function readableNotation(value: string) {
  return notationReplacements.reduce(
    (result, [source, replacement]) => result.replaceAll(source, replacement),
    value,
  );
}

function groupBySection(items: DefinitionEntry[]) {
  const groups = new Map<string, DefinitionEntry[]>();
  for (const item of items) {
    const group = groups.get(item.section) ?? [];
    group.push(item);
    groups.set(item.section, group);
  }
  return Array.from(groups.entries());
}

function DefinitionLinks({ entries }: { entries: DefinitionEntry[] }) {
  return (
    <>
      {groupBySection(entries).map(([section, sectionEntries]) => (
        <section className="section-group" key={section}>
          <h3 className="section-label">{section}</h3>
          <div className="definition-links">
            {sectionEntries.map((entry) => (
              <a className="definition-link" href={`#${entry.id}`} key={entry.id}>
                <span className="definition-link-number">{entry.number}</span>
                <span>{entry.title}</span>
              </a>
            ))}
          </div>
        </section>
      ))}
    </>
  );
}

function searchableText(entry: DefinitionEntry) {
  return [
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
  ]
    .join(' ')
    .toLocaleLowerCase();
}

export default function Home() {
  const [query, setQuery] = useState('');
  const searchRef = useRef<HTMLInputElement>(null);
  const normalizedQuery = query.trim().toLocaleLowerCase();

  const filteredDefinitions = useMemo(() => {
    if (!normalizedQuery) return definitions;
    return definitions.filter((entry) =>
      searchableText(entry).includes(normalizedQuery),
    );
  }, [normalizedQuery]);

  useEffect(() => {
    function handleKeyDown(event: KeyboardEvent) {
      const target = event.target as HTMLElement | null;
      const typing =
        target?.tagName === 'INPUT' ||
        target?.tagName === 'TEXTAREA' ||
        target?.isContentEditable;

      if (event.key === '/' && !typing) {
        event.preventDefault();
        searchRef.current?.focus();
      }
      if (event.key === 'Escape' && document.activeElement === searchRef.current) {
        setQuery('');
        searchRef.current?.blur();
      }
    }

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, []);

  return (
    <div className="reference-shell">
      <header className="masthead">
        <div className="masthead-inner">
          <div>
            <p className="eyebrow">Design draft 0.14 · Companion index</p>
            <h1 className="site-title">Newspeak Semantics Reference</h1>
          </div>
          <label className="search-wrap">
            <span className="sr-only">Search definitions and rules</span>
            <Search aria-hidden="true" className="search-icon" />
            <Input
              ref={searchRef}
              className="definition-search"
              type="search"
              value={query}
              onChange={(event) => setQuery(event.target.value)}
              placeholder="Search by name, number, notation, or description"
              autoComplete="off"
            />
            <span aria-hidden="true" className="search-key">
              /
            </span>
          </label>
          <span className="count-pill">
            {filteredDefinitions.length} / {definitions.length}
          </span>
        </div>
      </header>

      <div className="workspace">
        <aside className="definition-index">
          <div className="index-heading">
            <h2>All definitions</h2>
            <span>{filteredDefinitions.length} shown</span>
          </div>
          <nav aria-label="Definition index">
            <DefinitionLinks entries={filteredDefinitions} />
          </nav>
        </aside>

        <main className="main-column">
          <details className="mobile-directory">
            <summary>All definitions ({filteredDefinitions.length})</summary>
            <nav className="mobile-links" aria-label="Definition index">
              <DefinitionLinks entries={filteredDefinitions} />
            </nav>
          </details>

          <div className="intro-panel">
            <p>
              <strong>Every numbered form and named operational rule</strong> from
              the current semantics draft appears below. Each anchor is stable;
              the typeset definition is followed by descriptions of every
              metavariable, parameter, and record component used in that entry.
            </p>
          </div>

          <p className="result-heading" aria-live="polite">
            {normalizedQuery
              ? `${filteredDefinitions.length} matches for “${query.trim()}”`
              : `${definitions.length} definitions and rules in document order`}
          </p>

          {filteredDefinitions.length ? (
            <div className="definitions">
              {filteredDefinitions.map((entry) => (
                <article className="definition-card" id={entry.id} key={entry.id}>
                  <header className="card-header">
                    <div className="card-kicker">
                      <span className="definition-number">{entry.number}</span>
                      <span className="definition-kind">{entry.kind}</span>
                      <span className="definition-section">
                        {entry.subsection || entry.section}
                      </span>
                    </div>
                    <h2 className="card-title">{entry.title}</h2>
                    <p className="card-summary">{entry.summary}</p>
                    <a
                      className="anchor-link"
                      href={`#${entry.id}`}
                      aria-label={`Link to ${entry.title}`}
                      title="Permanent link"
                    >
                      <Hash aria-hidden="true" size={17} />
                    </a>
                  </header>

                  <div className="formal-source">
                    <div className="source-label">Formal definition</div>
                    <MathExpression formula={entry.formula} display />
                  </div>

                  <section className="parameter-panel">
                    <h3>Parameters and components</h3>
                    <dl className="parameter-list">
                      {entry.parameters.map((parameter) => (
                        <div
                          className="parameter-row"
                          key={`${entry.id}-${parameter.notation}`}
                        >
                          <dt>
                            <MathExpression formula={parameter.notation} />
                          </dt>
                          <dd>{readableNotation(parameter.description)}</dd>
                        </div>
                      ))}
                    </dl>
                  </section>
                </article>
              ))}
            </div>
          ) : (
            <div className="empty-state">
              No definition matches “{query.trim()}”. Try a rule name, equation
              number, or metavariable such as <code>allocClass</code>,{' '}
              <code>6.4</code>, or <code>κ</code>.
            </div>
          )}
        </main>
      </div>
    </div>
  );
}
