# ADR-002 — Junction-N2-Merge backup policy

**Date** : 2026-04-22
**Statut** : accepted (Q4 autosigned by auditor per Eric delegation ADR-001)
**Auteur** : session auditor (content) + worker (instantiation)
**Sign-off Eric** : via délégation ADR-001, auto-signé 2026-04-22 ; Eric conserve droit de `contest Q4` rétroactivement.

---

## Contexte

`/Users/ericmerle/Documents/Collatz-Junction-N2-Merge/` contient Junction Theorem v1.0-preprint (HEAD `1d71484`, tag `v1.0-preprint`), avec :

- 788 lignes de `preprint_v5.tex`
- Probes `check_central_axioms.lean`
- `reproduce.sh` (convention Junction, exit codes 0/1/2/3/4)
- 16 instances calculatoires k = 3..18
- CI workflow `.github/workflows/verify.yml`
- 7 critiques hostile-review corrigées (audit 2026-04-21/22)

Décision stratégique Option B + Legendre (METAPROMPT §1, §3) = un seul repo officiel = `collatz-nocycle-lean4`.

## Options considérées

- **A** : publier `Collatz-Junction-N2-Merge` comme repo parallèle (2 preprints publics).
- **B** : supprimer le dossier local (espace disque économisé).
- **C** : conserver backup local permanent, jamais pushé sur GitHub.

## Décision

**Option C retenue.**

## Justifications

1. **Anti-dilution** : deux repos publics sur le même sujet = confusion reviewer + dilution d'attention (réf MITIGATION R-04, METAPROMPT §3 S1).
2. **Réutilisation templates** : préservation `preprint_v5.tex` + probes + `reproduce.sh` + workflow CI comme templates pour S2 Hardening (L-02, L-03, L-04).
3. **Aucune perte scientifique** : l'approche Junction (k ∈ [3,17] + barrière k ≥ 18 via Simons-de Weger) reste documentée via `docs/LINEAGE.md` du repo officiel.
4. **Réversibilité** : si Eric souhaite un jour publier Junction en parallèle (après `v2.0-preprint` accepté), la décision est réversible par un `git push` ad-hoc.

## Contraintes d'usage

- **JAMAIS** push sur GitHub (public ou privé personnel).
- **JAMAIS** inclus dans une release formelle de `collatz-nocycle-lean4`.
- **JAMAIS** référencé dans le paper soumis comme source primaire.
- Utilisable pour : extraction de templates (S2 Hardening), références internes `docs/BIBLE/`, audit rétrospectif.
- Statut "archive historique locale" explicite.

## Réversibilité

Condition de déblocage de la contrainte "JAMAIS push" : publication `collatz-nocycle-lean4` v2.0 (post-Phase Legendre) acceptée par un journal peer-reviewed.

Si cette condition est remplie, Eric peut reconsidérer :
- publier Junction comme "v1.0-archive" séparé (repo distinct, clairement "historical companion"), OU
- continuer à le garder backup local indéfiniment.

Aucun automatisme : révision = décision Eric explicite post-acceptance.

## Impact sur G1

Aucun sur actions GitHub : le dossier reste dans le filesystem local, pas d'archivage, pas de push. Mention explicite dans `docs/LINEAGE.md` du repo officiel pour transparence vis-à-vis des futurs relecteurs (signal "zéro travail perdu, seulement consolidé").

## Conséquences

### Positives
- Un seul pointeur public (`collatz-nocycle-lean4`) ; intégrité institutionnelle préservée.
- Templates S2 disponibles hors GitHub (rapide, pas de network dependency).
- Réversibilité triviale sous condition.

### Négatives
- Dépendance du backup à l'intégrité du filesystem local Eric (mitigée par backups macOS Time Machine usuels).
- Risque d'oubli post-G6 : "il y avait un preprint Junction en local ?" — mitigé par cet ADR et par LINEAGE.md.

### Classification

Décision P2 opérationnelle (pas de publication, pas de modification code Lean). Réversibilité : facile.

---

## Historique

- 2026-04-22 : ADR rédigé par auditor, instancié par worker dans `docs/BIBLE/decisions/ADR-002-junction-backup-policy.md`. Autosign Q4 par auditor via ADR-001 §1.
