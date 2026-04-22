# G1 — Draft `docs/LINEAGE.md` (à ajouter à `collatz-nocycle-lean4`)

**Statut** : DRAFT LOCAL, non commité. Destiné à être publié dans `collatz-nocycle-lean4/docs/LINEAGE.md` AVANT l'archivage (recommandation Red Team HIGH-3).

**Scope G1 étendu** : ce document ajoute une 3ème action P1 au plan G1 initial (en plus d'archiver Junction et cycles-lean). Décision requise Eric.

---

**Contenu proposé** pour `docs/LINEAGE.md` :

```markdown
# Project Lineage — collatz-nocycle-lean4

This repository is the consolidated home for Eric Merle's formalization work on the non-existence of nontrivial Collatz cycles in Lean 4. This document records the preceding repositories and explains the scientific progression that led to the current design.

## Timeline

| Date | Repo | Status | Role |
|------|------|--------|------|
| 2025 — 2026-02 | `Projet_Collatz` (archived 2026-04-01) | archived | Initial NEXUS Collatz exploration (AI pipeline + formal pieces, τ₂₅₆, PySR, Lean 4). Superseded by focused formalization efforts. |
| 2026-02 — 2026-03 | `collatz-cycles-lean` (archived 2026-04-XX) | archived | Companion code for the first preprint. Contains a documented formula error in `lean/range-exclusion/` (see that repo's `docs/AUDIT_CORRSUM.md`). Correct results preserved in `lean/verified/` (k=3..15) and `lean/skeleton/` (Junction skeleton). |
| 2026-03 | `Collatz-Junction-Theorem` (archived 2026-04-XX) | archived | Junction Theorem formalization — entropic barriers + blocking mechanism, conditional on GRH + Conjecture 7.4. 280 Lean theorems, Lean 4.15. Preprint preserved in-repo. |
| 2026-03 | `collatz-audit-2026` | [archived/active per Eric's G1 decision] | Meta-audit that cross-referenced the three formalization repos (March 2026 state of the art). |
| 2026-04 — present | `collatz-nocycle-lean4` (this repo) | **active, official** | Continued-fractions approach. Conditional on `BakerSeparation` (Baker 1966 + Rhin 1987, published), `BarinaVerification` (Barina 2025, DOI 10.1007/s11227-025-07337-0, published), and `DerivedLargeKBound` (Lean structure encoding a bound derived via continued fractions of log₂3). The Phase Legendre plan (M2-M3) aims to promote `DerivedLargeKBound` from `structure` to a fully proven theorem via Legendre 1798. |

## Rationale for the pivot from Junction to continued fractions

The Junction Theorem (archived repo) is mathematically valid under GRH + Conjecture 7.4. The pivot to the continued-fractions formulation in this repo was driven by three concerns identified in the April 2026 adversarial audit :

1. **Publishability** — A conditional-on-2-published-hypotheses form (Baker + Barina) is a clearer ask for peer review in a top formal-mathematics venue than a conditional-on-GRH-plus-Conjecture form.
2. **Integrity margin** — The Junction approach's `ZeroExclusionHypothesis` (formerly `QuasiUniformity`) was internally audited as a pétition-de-principe risk (Signal #1 of the 2026-04-21 audit). The continued-fractions approach names the analogous load-bearing element as `DerivedLargeKBound` and has a concrete plan (Phase Legendre) to formalize it in Lean.
3. **Scope** — Targets the strong form (all k, conditional on B+B+DLK) rather than a family of approaches with separate sub-cases.

Both formalizations are complete in their own frames; neither subsumes the other. The archival of Junction and cycles-lean concentrates maintenance effort on the target-publication pathway.

## What readers should cite

- **For the active, publication-target result** : this repo (`collatz-nocycle-lean4`), preferably a tagged release once Phase Legendre is complete (target tag `v2.0-preprint`). Current state : baseline `d2fa81a`, 36 files, 393 theorems, 0 sorry, central theorem `no_nontrivial_cycle_phase59` depends on `propext, Classical.choice, Quot.sound` (verified 2026-04-22).
- **For the Junction Theorem result (conditional on GRH + Conjecture 7.4)** : the archived `Collatz-Junction-Theorem` repo preserves the preprint and Lean 4.15 code unchanged.
- **Do NOT cite** any theorem from `collatz-cycles-lean/lean/range-exclusion/` — that module is archived with a documented formula error banner.

## Archival convention

Archived repos are kept read-only on GitHub for citation continuity. No git history is destroyed. All archived READMEs carry an explicit banner explaining status and pointing to the active repo.

## Local backup preserved (not on GitHub)

A local backup `Collatz-Junction-N2-Merge/` (HEAD `1d71484`, tag `v1.0-preprint`) is retained outside GitHub. It contains 788 lines of preprint v5 (`preprint_v5.tex`), probe templates, reference `reproduce.sh` and `.github/workflows/verify.yml`. These artifacts will be reused as S2 Hardening templates for the active repo (`collatz-nocycle-lean4`). The intent of the consolidation is zero scientific content lost, only concentrated on the publication-target pathway.

---

_This document is append-only. Additions are dated ; previous entries are not rewritten._
```

---

## Classification du commit LINEAGE.md dans nocycle-lean4

- **P1** (modification du repo public officiel, réversible via `git revert`)
- Doit être commit AVANT tout archivage des autres repos
- Inclus dans le protocole §3 pre-commit complet (build + axioms + reproduce + journal)
- Le commit n'affecte pas le code Lean, uniquement `docs/LINEAGE.md` nouveau fichier
- Red Team minimal recommandé : relire que le contenu ne fait pas de claim non justifiée

## Extension du plan G1

| Action P1 | Cible | Commande clé |
|-----------|-------|--------------|
| 1. Add `docs/LINEAGE.md` | `collatz-nocycle-lean4` (repo actif) | git add + commit + push avec message "docs: add LINEAGE.md for consolidation context" |
| 2. Archive Junction | `Collatz-Junction-Theorem` | note README + `gh repo archive` |
| 3. Archive cycles-lean | `collatz-cycles-lean` | note README + `gh repo archive` |
| 4. Archive ou update audit-2026 | `collatz-audit-2026` | [Option A ou B selon Eric] |

Ordre d'exécution recommandé : 1 → 2 → 3 → 4. Chaque action est réversible indépendamment.
