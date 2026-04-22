# Project Lineage — collatz-nocycle-lean4

This repository is the consolidated home for Eric Merle's formalization work on the non-existence of nontrivial Collatz cycles in Lean 4. This document records the preceding repositories and explains the scientific progression that led to the current design.

## Timeline

| Date | Repo | Status | Role |
|------|------|--------|------|
| 2025 — 2026-02 | [`Projet_Collatz`](https://github.com/ericmerle3789/Projet_Collatz) | archived 2026-04-01 | Initial NEXUS Collatz exploration (AI pipeline + formal pieces, τ₂₅₆, PySR, Lean 4). Superseded by focused formalization efforts. |
| 2026-02 — 2026-03 | [`collatz-cycles-lean`](https://github.com/ericmerle3789/collatz-cycles-lean) | archived 2026-04-XX | Companion code for the first preprint. Contains a documented formula error in `lean/range-exclusion/` (see that repo's `docs/AUDIT_CORRSUM.md`). Correct results preserved in `lean/verified/` (k = 3..15) and `lean/skeleton/` (Junction skeleton). |
| 2026-03 | [`Collatz-Junction-Theorem`](https://github.com/ericmerle3789/Collatz-Junction-Theorem) | archived 2026-04-XX | Junction Theorem formalization — entropic barriers + blocking mechanism, conditional on GRH + Conjecture 7.4. 280 Lean theorems, Lean 4.15. Preprint preserved in-repo. |
| 2026-03 | [`collatz-audit-2026`](https://github.com/ericmerle3789/collatz-audit-2026) | archived 2026-04-XX | Meta-audit that cross-referenced the three formalization repos (March 2026 state of the art). Audit artifacts preserved as-is. |
| 2026-04 — present | [`collatz-nocycle-lean4`](https://github.com/ericmerle3789/collatz-nocycle-lean4) (this repo) | **active, official** | Continued-fractions approach. Conditional on `BakerSeparation` (Baker 1966 + Rhin 1987, published), `BarinaVerification` (Barina 2025, DOI [10.1007/s11227-025-07337-0](https://doi.org/10.1007/s11227-025-07337-0), published), and `DerivedLargeKBound` (Lean `structure` encoding a bound derived via continued fractions of log₂3). The Phase Legendre plan (M2-M3) aims to promote `DerivedLargeKBound` from `structure` to a fully proven theorem via Legendre 1798. |

## Rationale for the pivot from Junction to continued fractions

The Junction Theorem (archived repo) is mathematically valid under GRH + Conjecture 7.4. The pivot to the continued-fractions formulation in this repo was driven by three concerns identified in the April 2026 adversarial audit :

1. **Publishability** — A conditional-on-two-published-hypotheses form (Baker + Barina) is a clearer ask for peer review in a top formal-mathematics venue than a conditional-on-GRH-plus-Conjecture-7.4 form.
2. **Integrity margin** — The Junction approach's `ZeroExclusionHypothesis` (formerly `QuasiUniformity`) was internally audited as a pétition-de-principe risk (Signal #1 of the 2026-04-21 audit). The continued-fractions approach names the analogous load-bearing element as `DerivedLargeKBound` and has a concrete plan (Phase Legendre, M2-M3) to formalize it in Lean.
3. **Scope** — Targets the strong form (all k, conditional on Baker + Barina + DerivedLargeKBound) via a single consolidated proof pathway rather than a family of approaches with separate sub-cases.

Both formalizations are complete in their own frames ; neither subsumes the other. The archival of Junction, cycles-lean, and audit-2026 concentrates maintenance effort on the target-publication pathway.

## What readers should cite

- **For the active, publication-target result** : this repo (`collatz-nocycle-lean4`), preferably a tagged release once Phase Legendre is complete (target tag `v2.0-preprint`). Current baseline (2026-04-22) : commit `d2fa81a`, 36 `.lean` files, 393 theorems, 0 `sorry`, central theorem `no_nontrivial_cycle_phase59` depends on `propext`, `Classical.choice`, `Quot.sound` (verified by `#print axioms` on 2026-04-22 — see `docs/BIBLE/env-snapshots/2026-04-22-axioms-central.txt`).
- **For the Junction Theorem result (conditional on GRH + Conjecture 7.4)** : the archived `Collatz-Junction-Theorem` repo preserves the preprint and Lean 4.15 code unchanged. Cite the archived URL — it remains accessible read-only.
- **Do NOT cite** any theorem from `collatz-cycles-lean/lean/range-exclusion/` — that module is archived with a documented formula error banner.

## Archival convention

Archived repos are kept read-only on GitHub for citation continuity. No git history is destroyed. All archived READMEs carry an explicit banner explaining status and pointing to the active repo.

## Local backup preserved (not on GitHub)

A local backup `Collatz-Junction-N2-Merge/` (HEAD `1d71484`, tag `v1.0-preprint`) is retained outside GitHub. It contains 788 lines of preprint v5 (`preprint_v5.tex`), probe templates, a reference `reproduce.sh` with exit codes 0/1/2/3/4, and a `.github/workflows/verify.yml` template. These artifacts will be reused as S2 Hardening templates for the active repo. The intent of the consolidation is **zero scientific content lost, only concentrated on the publication-target pathway**.

Policy for this backup is formalized in `docs/BIBLE/decisions/ADR-002-junction-backup-policy.md` (TL;DR : never push, reversible only post-v2.0 acceptance).

---

_This document is append-only. Additions are dated ; previous entries are not rewritten._
