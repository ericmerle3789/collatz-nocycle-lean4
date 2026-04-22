# paper/

LaTeX source for the `collatz-nocycle-lean4` paper (draft v1, April 2026).

## Structure

- `paper.tex` — main file, imports `sections/*.tex`
- `sections/` — one file per logical section
- `references.bib` — BibTeX entries (DOI/arXiv-verified as of 2026-04-22, see `../docs/BIBLE/env-snapshots/2026-04-22-doi-check.txt`)
- `figures/` — optional diagrams

## Compilation

Standard LaTeX toolchain :

```bash
cd paper
latexmk -pdf paper.tex
# or, equivalently :
pdflatex paper.tex
bibtex paper
pdflatex paper.tex
pdflatex paper.tex
```

`paper.pdf` is generated but **not committed** (use `.gitignore`).

## Conventions

- **English only** (no French in the paper body).
- Every mathematical claim must reference either a published source (by DOI/arXiv ID) or a Lean 4 file/line in `ProjetCollatz/`.
- Passages still pending author validation are marked `% [ERIC-REVIEW]` as LaTeX comments. These markers must be resolved (either validated or corrected) before any public release.
- No promotional language. State results conditionally : *"we establish, conditional on \dots, that \dots"*.

## Status

Draft v1 (April 2026). This is a G3 artefact per the NASA-grade operating manual (see `docs/BIBLE/`). It is NOT yet intended for external distribution. Any public release requires :

1. All `[ERIC-REVIEW]` markers resolved.
2. Red Team audit of the full draft.
3. Eric sign-off explicit per MISSION `§12.G6` or subsequent gate.
4. `paper-v1-draft` git tag (to be applied at that point, not before).

See `../docs/BIBLE/JOURNAL.md` for the G3 audit trail.
