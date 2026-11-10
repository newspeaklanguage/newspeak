# Semantics website (static export)

Builds the static site published at newspeaklanguage.org/formal-semantics:
the landing page, the definition reference and the Lean guide.

    python3 generate_reference.py              # re-extract definitions from the .tex sources
    npm install                                # once: KaTeX, the only dependency
    node export_newspeak_site.mjs OUTPUT_DIR   # OUTPUT_DIR must be empty or absent

Node 22 or later is required (the fnm default on PATH is fine).
`generate_reference.py` reads `../newspeak-semantics.aux`, so build the PDF first.

`assets/reference.css` and `assets/fonts/` are static. They were compiled once by
the React reference app this directory replaced (removed 2026-11-10), and the
export reproduced the deployed site byte for byte. To change the reference
page's styling, edit `reference.css` directly. The Lean guide comes from
`../lean-guide-site/dist`.
