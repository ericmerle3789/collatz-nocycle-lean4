# G1 Sign-off — GitHub consolidation

**Date** : 2026-04-22
**Gate** : G1 (consolidation GitHub, archivage repos secondaires)
**Autorité** : Eric Merle via délégation ADR-003 (extended gate delegation)
**Citation Eric (2026-04-22T17:30Z)** : *"C'est à toi de lui dire, c'est ça que je veux, tu la pilote."*
**Auditor sign-off** : 2026-04-22T17:32:00Z, via ADR-003 8-conditions all PASS (relayé dans `to_worker/0006-g1-eric-go-execute.md`)
**Worker exécution** : 2026-04-22T17:19:02Z → 2026-04-22T17:XX:XXZ

---

## Actions exécutées

| Sous-étape | Action | Artefact / hash |
|------------|--------|------------------|
| G1.7 | Merge `--ff-only` `g1-consolidation` → `main` | HEAD local main : `503e5e9` |
| G1.8 | `git push origin main` | `d2fa81a..503e5e9 main -> main` |
| G1.9 | Note README + commit + push + archive `Collatz-Junction-Theorem` | Commit remote `a57d29e`, archived=true |
| G1.10 | Note README + commit + push + archive `collatz-cycles-lean` | Commit remote `1d77168`, archived=true |
| G1.11 | Note README + commit + push + archive `collatz-audit-2026` (Option A) | Commit remote `40c1269`, archived=true |
| G1.12 | Signoff file + JOURNAL append + commit + push | (ce fichier + commit à venir dans main) |

## Inventaire GitHub post-G1

| Repo | Statut post-G1 | Note |
|------|----------------|------|
| `collatz-nocycle-lean4` | **ACTIF** (officiel) | HEAD `503e5e9` + G1.12 commit. 36 `.lean`, 393 théorèmes. |
| `Collatz-Junction-Theorem` | ARCHIVED | README banner + pointer vers nocycle-lean4 |
| `collatz-cycles-lean` | ARCHIVED | README banner + warning module erroné + pointer |
| `collatz-audit-2026` | ARCHIVED | README banner + meta-audit préservé en lecture seule |
| `MATHEVO` | ACTIF | Hors scope Collatz (projet OMEGA IA distinct) |
| `PROMETHEUS` | ACTIF | Hors scope Collatz (projet AI Mathematician distinct) |
| `Projet_Collatz` | ARCHIVED (pré-G1, 2026-04-01) | Aucune action |

## Hash intégrité post-G1.11

- `ProjetCollatz/*.lean` global sha256 : `a18dce00dba72dffc67fdb2dd7f1882b69f9c4c9e3239e2215cc231e6a00f00f` (identique baseline G0, **zéro Lean modifié**)
- `#print axioms ProjetCollatz.no_nontrivial_cycle_phase59` : `[propext, Classical.choice, Quot.sound]` (identique baseline G0)
- Commits ajoutés sur `main` : f292307 (LINEAGE.md) + 503e5e9 (docs/BIBLE/) + G1.12 signoff commit

## Backup local préservé (hors GitHub, conforme ADR-002)

`/Users/ericmerle/Documents/Collatz-Junction-N2-Merge/` (HEAD `1d71484`, tag `v1.0-preprint`) — intact, non-poussé. Contient : preprint_v5.tex (788 lignes), probes `check_central_axioms.lean`, `reproduce.sh` Junction convention, workflow CI template. Réutilisable pour S2 Hardening.

## Red Team mitigations confirmées appliquées

| Finding RT | Statut | Évidence |
|-----------|--------|----------|
| HIGH-1 (citation check) | DONE | Auditor a exécuté via WebSearch + GitHub API : 0 résultat publique détectée (détail `archive/to_worker/0004`) |
| HIGH-2 (co-auteurs git log) | DONE | 100 commits Junction + 6 cycles-lean = Eric Merle uniquement |
| HIGH-3 (lignée préservée) | DONE | `docs/LINEAGE.md` committé + pushé (commit `f292307`) AVANT archivages |
| HIGH-4 (cycles-lean erreur clair) | DONE | Note README cycles-lean avec ❌/✅ explicites, `lean/range-exclusion/` nommé |
| HIGH-5 (#print axioms verbatim) | DONE | Notes README Junction + cycles-lean contiennent tableau comparatif axiomes |

## Réversibilité (toutes actions restent réversibles)

- Unarchive des 3 repos : `gh repo unarchive ericmerle3789/<REPO>` (instantané)
- Revert commits G1.1 + G1.2 sur main : `git revert 503e5e9 f292307` (techniquement possible mais peu souhaitable, docs/BIBLE/ + LINEAGE.md étant utiles)
- Revert commits README archive sur repos archivés : `git revert <hash>` possible après `gh repo unarchive`

## Découplages et préconditions vérifiés

- `collatz-nocycle-lean4/` pas de dépendance de build ou code vers les 3 repos archivés (grep confirmé à G0)
- Aucun DOI Zenodo, aucun CITATION.cff sur les 3 repos archivés
- Aucun fork ni star ni issue ouverte ni PR sur les 3 repos archivés (gh API pre-exec)

## Prochain gate

**G2 — Hardening `collatz-nocycle-lean4`** (Phase B Semaine 2) :
- Créer `reproduce.sh` (convention Junction, exit codes 0/1/2/3/4) — copier depuis `Collatz-Junction-N2-Merge/` et adapter
- Créer `probes/check_sorry.lean` et `probes/check_central_axioms.lean`
- Créer `expected_axioms.md` (`propext`, `Classical.choice`, `Quot.sound` ; documenter qu'en M3 après Phase Legendre, `Lean.ofReduceBool` + `Lean.trustCompiler` s'ajouteront via `native_decide`)
- Mettre à jour `lakefile.toml` : `defaultTargets = ["ProjetCollatz"]` (fix F1 / L-06 / R-09)
- Renforcer `.github/workflows/build.yml` : ajouter étape `#print axioms` vs `expected_axioms.md` diff
- `HYPOTHESES.md` : enrichir avec DOI links et citations précises (Baker, Rhin, Barina, Hercher)
- Red Team sur le plan S2 avant exécution
- Gate G2 signé par Eric (ou extended delegation selon volonté Eric)

---

**G1 clos. Migration GitHub terminée, intégrité Lean préservée.**
