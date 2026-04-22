# G1 — Drafts de notes d'archivage v2 (post-Red Team)

**Statut** : DRAFT LOCAL v2, non commité, destiné à être publié APRÈS sign-off Eric G1.
**Changelog v1 → v2** : intégration des findings Red Team HIGH-4 (durcissement langage erreur cycles-lean) et HIGH-5 (inclusion `#print axioms` verbatim).

---

## Draft 1 v2 — `ericmerle3789/Collatz-Junction-Theorem`

```markdown
> **⚠️ Repository archived 2026-04-XX — historical reference only.**
>
> **Active repo** : [collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4)
>
> ## Logical status of the two formalizations (read before citing)
>
> Both repos formalize conditional results on the non-existence of nontrivial Collatz cycles, but they are **mathematically distinct and not equivalent**:
>
> | Aspect | This repo (Junction, archived) | collatz-nocycle-lean4 (active) |
> |--------|---------------------------------|--------------------------------|
> | Approach | Entropic barriers + blocking mechanism (Steiner equation on corrSum mod d) | Continued fractions of log₂3 + Baker 1966 + Barina 2025 |
> | Conditional on | GRH + Conjecture 7.4 (Artin-like, unconditional for k ≤ 10001) | `BakerSeparation` (published), `BarinaVerification` (published, DOI 10.1007/s11227-025-07337-0), `DerivedLargeKBound` (structure hypothesis, to be proven via Legendre 1798 in Phase Legendre) |
> | Lean axioms (central theorem) | (historical — see Lean 4.15 `#print axioms` inside this repo) | `propext, Classical.choice, Quot.sound` — the 3 fundamental Mathlib axioms, verified by `#print axioms ProjetCollatz.no_nontrivial_cycle_phase59` on 2026-04-22 |
> | `sorry` | 0 | 0 |
> | User-declared `axiom` | 0 | 0 |
> | `native_decide` in central chain | (see repo) | 0 at baseline; `Lean.ofReduceBool + Lean.trustCompiler` will be added in Phase Legendre and declared in `expected_axioms.md` at that point |
>
> **Note on `DerivedLargeKBound`** : it is a Lean `structure` (a typed hypothesis container), **not a Lean `axiom`**. It encapsulates the mathematically derived bound `∀ n k, IsOddCycle n k → k > 1322 → n < 2^71`, justified in the paper by continued fractions of log₂3. The Phase Legendre plan in the active repo aims to promote this structure to a fully proven theorem.
>
> ## Why the pivot
>
> The Junction Theorem approach remains mathematically interesting and the preprint is preserved here unchanged. The pivot to continued fractions in `collatz-nocycle-lean4` was motivated by:
> 1. **Publishability** : dependency on GRH + Conjecture 7.4 was identified as a harder reviewer target than dependency on Baker + Barina, both fully published.
> 2. **Integrity margin** : the Junction approach's `ZeroExclusionHypothesis` was flagged in internal audit (2026-04-21) as a pétition-de-principe risk. The continued-fractions approach isolates the analogous role in a named structure (`DerivedLargeKBound`) that will be proven in Phase Legendre.
> 3. **Simpler logical conditional** : the conditional-on-2-published-hypotheses form is clearer for a formal mathematics publication.
>
> Neither repo is a superset of the other; both are complete under their respective hypotheses.
>
> ## Maintenance
>
> No further commits to this repo are planned. Issues → [active repo issue tracker](https://github.com/ericmerle3789/collatz-nocycle-lean4/issues).
>
> — Eric Merle, 2026-04-XX

---
```

---

## Draft 2 v2 — `ericmerle3789/collatz-cycles-lean`

```markdown
> **⚠️ Repository archived 2026-04-XX — historical reference only.**
>
> **Active repo** : [collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4)
>
> ## ⚠️ Known formula error — do NOT cite the `lean/range-exclusion/` module
>
> The `lean/range-exclusion/` directory of this repository contains a Lean module with a **documented formula error** : the function computed in that module differs from Steiner's `corrSum`, so any result proven in `range-exclusion/` does NOT establish cycle non-existence. See `docs/AUDIT_CORRSUM.md` in this repo for the full diagnostic.
>
> **Rule for readers and reviewers** :
> - ❌ Do NOT copy, cite, or re-use any theorem from `lean/range-exclusion/`.
> - ❌ Do NOT treat the `range-exclusion/` results as valid Collatz cycle non-existence proofs.
> - ✅ The correct results of this archived repo are in `lean/verified/` (k = 3..15, 280 theorems, 0 sorry, 0 axiom, Lean 4.15) and `lean/skeleton/` (Junction Theorem skeleton).
> - ✅ For current and publication-target work, consult [collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4).
>
> ## Relationship to the active repo
>
> `collatz-nocycle-lean4` supersedes this companion repo with :
> - A single consolidated Lean tree (36 files, 393 theorems, 0 sorry).
> - No known formula errors.
> - Central theorem `no_nontrivial_cycle_phase59` depends on `propext, Classical.choice, Quot.sound` only — verified via `#print axioms` on 2026-04-22.
>
> ## Maintenance
>
> No further commits. Issues → [active repo issue tracker](https://github.com/ericmerle3789/collatz-nocycle-lean4/issues).
>
> — Eric Merle, 2026-04-XX

---
```

---

## Draft 3 v2 — `ericmerle3789/collatz-audit-2026` (Option A épinglée par auditor)

**Statut** : Option A (archiver) autosignée par auditor 2026-04-22 via ADR-001 (Eric a délégué Q1). Contestable par Eric via "contest Q1".

**Justification** : cohérence avec stratégie "1 seul repo public officiel" (anti-dilution). Les artefacts d'audit méta (`audit/SYNTHESE_MARS2026.md`, etc.) sont préservés en lecture seule, accessibles via l'interface GitHub archive. Le meta-trail est doublé dans `docs/BIBLE/` + `docs/LINEAGE.md` du repo officiel.

Draft README à insérer en entête du README actuel de `collatz-audit-2026` :

```markdown
> **⚠️ Repository archived 2026-04-XX — historical audit, Mars 2026.**
>
> This meta-repository cross-referenced three Collatz research repos during the audit conducted March 2026. After the April 2026 consolidation, the **active project is [collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4)**. Two of the three originally audited repos (`Collatz-Junction-Theorem`, `collatz-cycles-lean`) have also been archived as part of that consolidation, each with a banner redirecting readers to the active project.
>
> Audit artifacts (`audit/SYNTHESE_MARS2026.md`, `audit/COMPLEMENT_RECHERCHE.md`, `audit/PISTES_CROISEES.md`) remain here unchanged for historical reference. The March 2026 state-of-the-art snapshot is thus preserved as-is.
>
> No further maintenance is planned here. Issues or questions → [active repo issue tracker](https://github.com/ericmerle3789/collatz-nocycle-lean4/issues).
>
> — Eric Merle, 2026-04-XX

---
```
