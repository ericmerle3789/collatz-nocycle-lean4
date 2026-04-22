# G2 Sign-off — Hardening

**Date** : 2026-04-22
**Gate** : G2 (hardening infrastructure : `lakefile` fix + `probes/` + `expected_axioms.md` + `reproduce.sh` + CI upgrade + DOI-check)
**Autorité** : Eric via délégation ADR-003 (extended gate delegation, 8/8 conditions PASS)
**Sign-off auditor** : 2026-04-22T17:50:00Z (session auditor-handoff-20260422, indépendamment vérifié le rapport worker 0009 + artefacts filesystem)
**Worker exécution** : 2026-04-22T17:49:00Z → ~2026-04-22T18:00:00Z

---

## Actions exécutées

| Sous-étape | Action | Commit / artefact |
|------------|--------|-------------------|
| G2.1 | `lakefile.toml` : `defaultTargets = ["ProjetCollatz", "projetcollatz"]` (lib + exe) | `f05f3cc` |
| G2.2 | `probes/check_central_axioms.lean` (10 théorèmes) + `probes/check_sorry.lean` (10 théorèmes, M2 étendu) | `64a8c01` |
| G2.3 | `expected_axioms.md` : canonical baseline avec SHA256 anchor + Section 3bis out-of-scope | `47eac87` |
| G2.4 | `reproduce.sh` v2 avec mitigations RT H1/H2/H7 + M1/M2 | `1920ddb` |
| G2.5 | `.github/workflows/build.yml` upgraded : `ubuntu-24.04`, elan v4.1.2 pinned, cache hard-fail, artifact upload | `6eb15a1` |
| G2.6 | `docs/BIBLE/env-snapshots/2026-04-22-doi-check.txt` + `docs/BIBLE/redteam/2026-04-22-G2-hardening.md` | `6dae8ce` |
| G2.7 | Merge `--ff-only g2-hardening` → `main` + push | HEAD main `6dae8ce` (6 commits G2 intégrés) |
| G2.8 | CI run `24793727572` : **conclusion `success` en 6m53s** | [GitHub Actions run](https://github.com/ericmerle3789/collatz-nocycle-lean4/actions/runs/24793727572) |
| G2.9 | Signoff + JOURNAL append + commit + push (ce fichier + commit à venir) | (à venir) |

## Métriques d'intégrité post-G2

| Métrique | Valeur | vs baseline G0 |
|----------|--------|----------------|
| `ProjetCollatz/*.lean` sha256 global | `a18dce00dba72dffc67fdb2dd7f1882b69f9c4c9e3239e2215cc231e6a00f00f` | **identique** (0 Lean modifié) |
| `#print axioms no_nontrivial_cycle_phase59` | `[propext, Classical.choice, Quot.sound]` | **identique** |
| `#print axioms` 7 central + 3 auxiliary | strict match `expected_axioms.md` | nouveauté G2 |
| `lake build` EXIT | 0 (7925 jobs = lib + exe) | nouveauté G2 (baseline n'incluait pas exe) |
| `reproduce.sh` EXIT | 0 (toolchain + build + axioms + sorry tous PASS) | nouveauté G2 |
| CI GitHub Actions | `success` 6m53s sur ubuntu-24.04 | upgrade G2 |

## Red Team findings (RT G2)

- **7 HIGH** : tous mitigés avant commits (H1/H2/H7 dans `reproduce.sh`, H3 dans CI workflow, H4 dans `expected_axioms.md`, H5/H6 dans CI workflow)
- **4 MEDIUM mitigés** : M1 (`lean-toolchain` [ -f ] check), M2 (sorry probe 10 théorèmes), M3 (Section 3bis out-of-scope), M5 (lib + exe default target)
- **3 MEDIUM tech debt documentée** : M4 (multi-source truth across script/probe/md), M6 (`EXPECTED_TOOLCHAIN` vs `lakefile.toml` rev), M7 (M3 update comment enforcement) — à adresser en itération future
- **7 LOW** : reportés pour itérations ultérieures (runtime estimates Mac-specific, etc.)

Rapport complet : `docs/BIBLE/redteam/2026-04-22-G2-hardening.md`.

## DOI-check HYPOTHESES.md

- Barina 2025, J. Supercomputing : HTTP 200 ✓
- Hercher 2023, arXiv:2201.00406 : HTTP 200 ✓
- Baker 1966, Mathematika : DOI valide (redirect vers Wiley, full PDF auth-required mais le DOI résout)
- Rhin 1987 : non cité directement dans HYPOTHESES.md — TO-ADD en amélioration S2.X

Fichier : `docs/BIBLE/env-snapshots/2026-04-22-doi-check.txt`

## Réversibilité

- **Revert soft** : `git revert f05f3cc..6dae8ce` (6 commits sous forme de revert commits, préserve historique)
- **Revert dur (urgence)** : `git reset --hard 6407100 && git push --force-with-lease origin main` (destructif, Eric-only via P0)
- **Unarchive** : non applicable (aucun repo modifié côté GitHub archive statuses en G2)

## Prochain gate

**G3 — Paper v1 draft + decision point Phase Legendre**.

Périmètre G3 :
- Rédaction du draft paper (15-25 pages, structure METAPROMPT §3 S3)
- Decision point fin S3 : feu vert Phase Legendre (M2-M3) vs STOP publier conditionnel (critères METAPROMPT §6)
- Feedback Gouëzel (externe) attendu

G3 est plus sensible que G2 (matériel s'approchant d'une pré-claim publique). L'éligibilité ADR-003 à évaluer au cas par cas :
- Outline + sections internes : probable autosign auditor
- Commit final du paper draft dans `paper/` : **probable Eric-only**

À confirmer par auditor dans le message d'amorce G3.

---

**G2 clos. Infrastructure hardening terminée, intégrité Lean préservée, CI vert.**
