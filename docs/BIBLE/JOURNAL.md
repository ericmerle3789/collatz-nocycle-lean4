# JOURNAL — collatz-nocycle-lean4

**Convention** : append-only, jamais d'édition d'entrée passée. Toute correction = nouvelle entrée qui référence l'ancienne.

---

## 2026-04-22 — G0 Setup [P1] Fresh working tree + BIBLE + baseline §14

**Auteur** : Claude Opus 4.7 (1M context), session handoff 2026-04-22 post-validation 23/23 + 2 PASS++ + GO G0 Option B.

**Contexte** : Session précédente (2026-04-21/22) a produit audit adversarial nocycle + MISSION_AND_PROTOCOLS_NASA.md (695 lignes). Nouvelle session a validé 10 questions (23/23) puis 2 questions de contrôle (PASS++). Eric a choisi Option B révisée pour G0 : archive du clone d'audit, fresh clone dédié, baseline §14.

**Actions exécutées** :

1. `mv /Users/ericmerle/Documents/Audit-NoCycle-Lean4-2026-04-22 → Archive-Audit-NoCycle-2026-04-22` (figée, read-only conceptuellement).
2. `git clone https://github.com/ericmerle3789/collatz-nocycle-lean4 collatz-nocycle-lean4-work` dans `/Users/ericmerle/Documents/`.
3. Vérification HEAD : `d2fa81a4aa18ecd011ebe7832fe7ba518e1068df` (2026-02-22, "fix(attribution): rename misattributed structures, add HYPOTHESES.md") — match METAPROMPT §2.
4. Création `docs/BIBLE/` + 6 sous-dossiers + 4 fichiers d'index.
5. Env snapshot → `docs/BIBLE/env-snapshots/2026-04-22-baseline.txt`.
6. Initialisation `RISK_REGISTER.md` (R-01..R-10) et `LIMITATIONS.md` (L-01..L-07).
7. `lake build ProjetCollatz` fresh from source (pas de `lake exe cache get` car cache Mathlib non fetched) → **EXIT 0, 7930 jobs, wall-clock 1h32min38s**. Log : `docs/BIBLE/env-snapshots/2026-04-22-baseline-lib-build.log`.
8. Probe `#print axioms` sur 10 théorèmes listés par Eric → `docs/BIBLE/env-snapshots/2026-04-22-axioms-central.txt`. **Résultat** :
   - `no_nontrivial_cycle_phase59/final/derived/full, no_cycle_k_le_1322, no_cycle_k_gt_1322, sdw_from_cf` : dépendances = `[propext, Classical.choice, Quot.sound]` — **3 axiomes fondamentaux, cohérent METAPROMPT §2**.
   - `cf_gap_8, cf_gap_13, cf_nbound_8` : dépendances = `[propext, Lean.ofReduceBool, Lean.trustCompiler]` — `native_decide` confirmé, **mais isolé** (pas dans la chaîne centrale à G0).
9. Hash tree : 36 fichiers `.lean`, fichier per-fichier `docs/BIBLE/integrity_logs/baseline-d2fa81a-20260422-173948.sha256`, **global hash** : `a18dce00dba72dffc67fdb2dd7f1882b69f9c4c9e3239e2215cc231e6a00f00f`.
10. `./verify.sh` (best-effort, `reproduce.sh` absent) → VERIFICATION PASSED ; 7922 jobs (incremental), 393 théorèmes, 36 fichiers, 0 sorry textuel, 0 axiome utilisateur textuel. Log : `docs/BIBLE/env-snapshots/2026-04-22-verify-sh.log`.

**Métriques baseline** (à geler pour comparaison future) :

| Métrique | Valeur G0 | Source |
|----------|-----------|--------|
| Commit HEAD | `d2fa81a` | `git rev-parse HEAD` |
| Date commit | 2026-02-22 | `git log -1` |
| Fichiers `.lean` dans ProjetCollatz/ | 36 | `find + wc` |
| Théorèmes + lemmes (grep strict) | 393 | verify.sh |
| Sorry textuels | 0 | verify.sh + grep |
| Axiomes utilisateur textuels (`^axiom`) | 0 | verify.sh + grep |
| Axiomes effectifs du théorème central | `propext, Classical.choice, Quot.sound` | `#print axioms` |
| Jobs `lake build ProjetCollatz` (fresh) | 7930 | build log |
| Jobs `lake build ProjetCollatz` (incremental) | 7922 | verify.sh |
| Wall-clock build fresh | 1h32min38s (M1 Pro 16GB) | `time lake build` |
| Toolchain Lean | `leanprover/lean4:v4.27.0` | `lean-toolchain` |
| Version elan | 4.1.2 (58e8d545e 2025-05-26) | env snapshot |
| sha256 global arbre `.lean` | `a18dce00dba72dffc67fdb2dd7f1882b69f9c4c9e3239e2215cc231e6a00f00f` | `shasum` chain |
| Occurrences `native_decide` ProjetCollatz | 182 (8 fichiers) | grep |

**Classification** : G0 = setup + mesure, AUCUN commit, AUCUN push, AUCUN fichier Lean modifié.

**Findings G0 à documenter** :

- **F1 / L-06 / R-09 [P2]** : `lake build` (default target = exe `projetcollatz`) donne faux positif ; vrai build = `lake build ProjetCollatz`. À corriger S2 (ADR : changer `defaultTargets` ou fixer doc).
- **F2 / L-07 / R-10 [P2 G0 / foreseen P1 M3]** : 182 `native_decide`. À G0, isolés au contenu-justificateur de `DerivedLargeKBound` (structure). En M3, quand `DerivedLargeKBound` sera prouvée via `cf_gap_*` + Legendre, `Lean.ofReduceBool` et `Lean.trustCompiler` entreront dans la chaîne centrale — à déclarer préventivement dans `expected_axioms.md` + paper.
- **F3 / L-02..L-05 [P2]** : absences à combler en S2 : `reproduce.sh`, `probes/`, `expected_axioms.md`, DOI-vérification références bibliographiques.
- **F4 [observation]** : `verify.sh` existant utilise `grep` (R-08 ; insuffisant vs §3.2 NASA). Ne pas s'y fier isolément.

**Classification Eric-visible** : G0 terminé ; **déviations vs METAPROMPT §2** = zéro sur métriques critiques (HEAD, files, théorèmes, sorry, axiomes centraux) ; écarts documentés = présence `Lean.trustCompiler` en plus de `Lean.ofReduceBool` sur `cf_gap_*` (mineur, isolé), temps de build 1h32 vs "9 min" (explication : absence `lake exe cache get` ici).

**Prochaine action attendue** : sign-off Eric G1 avant Phase B / Semaine 1 (Consolidation GitHub : archiver `Collatz-Junction-Theorem` et `collatz-cycles-lean` sur GitHub, sans toucher `Collatz-Junction-N2-Merge` qui reste backup local).

**Interdits actifs jusqu'à G1 signed** : aucun `git add` / `commit` / `push` / modification fichier Lean / archivage GitHub.

**Sign-off Eric** : [EN ATTENTE G1]

---

## 2026-04-22 — G1 CLÔTURE [P1] GitHub consolidation done

**Autorité** : Eric via ADR-003 extended gate delegation. Citation : *"C'est à toi de lui dire, c'est ça que je veux, tu la pilote."* Auditor sign-off 17:32Z.

**Actions exécutées** :
- G1.7 merge `--ff-only` `g1-consolidation` → `main` (HEAD `503e5e9`)
- G1.8 push origin main (f292307 LINEAGE + 503e5e9 BIBLE)
- G1.9 archive `Collatz-Junction-Theorem` (commit `a57d29e` + `gh repo archive`)
- G1.10 archive `collatz-cycles-lean` (commit `1d77168` + `gh repo archive`)
- G1.11 archive `collatz-audit-2026` (commit `40c1269` + `gh repo archive`) — Option A autosigned per Q1 délégation
- G1.12 signoff `docs/BIBLE/signoffs/G1-consolidation.md` + cette entrée JOURNAL

**Vérifications post-archivages** :
- 3/3 repos `archived=true` confirmé via `gh api`
- `collatz-nocycle-lean4` reste actif, `archived=false`
- ProjetCollatz/ sha256 inchangé : `a18dce00...` (zéro Lean modifié)
- `#print axioms no_nontrivial_cycle_phase59` inchangé : `[propext, Classical.choice, Quot.sound]`

**Inventaire GitHub post-G1** : `collatz-nocycle-lean4` actif (officiel) + `MATHEVO`/`PROMETHEUS` actifs hors-scope Collatz + 4 repos archivés (Junction-Theorem, cycles-lean, audit-2026, Projet_Collatz pré-G1).

**Réversibilité** : triviale via `gh repo unarchive` (instantané par repo).

**Prochain** : G2 hardening (reproduce.sh, probes/, expected_axioms.md, lakefile defaultTargets fix, CI renforcée).
