# G0 Sign-off — Baseline setup

**Date** : 2026-04-22
**Gate** : G0 (setup working tree + BIBLE + baseline mesurée)
**Autorité** : Eric Merle (via session précédente Claude Opus)
**Confirmation reçue** : "G0 signed off par Eric — 2026-04-22" (transmis par la session précédente après revue du rapport baseline)

---

## Baseline gelée (à ne jamais modifier dans ce document — append-only)

| Élément | Valeur |
|---------|--------|
| HEAD commit | `d2fa81a4aa18ecd011ebe7832fe7ba518e1068df` |
| Message commit | "fix(attribution): rename misattributed structures, add HYPOTHESES.md" |
| Date commit | 2026-02-22 18:38:53 +0100 |
| Tree sha256 global (fichiers `.lean` de `ProjetCollatz/`) | `a18dce00dba72dffc67fdb2dd7f1882b69f9c4c9e3239e2215cc231e6a00f00f` |
| Axiomes `no_nontrivial_cycle_phase59` | `propext, Classical.choice, Quot.sound` |
| Fichiers `.lean` dans `ProjetCollatz/` | 36 |
| Théorèmes + lemmes (grep strict verify.sh) | 393 |
| `sorry` textuels | 0 |
| `axiom` utilisateur textuels (`^axiom`) | 0 |
| `lake build ProjetCollatz` EXIT | 0 |
| Jobs build fresh from source | 7930 |
| Jobs build incremental (verify.sh) | 7922 |
| Wall-clock fresh (M1 Pro 16 GB, sans `lake exe cache get`) | 1h32min38s |
| Wall-clock attendu avec cache (CI) | ~9 min |
| Toolchain Lean | `leanprover/lean4:v4.27.0` |
| elan | 4.1.2 (58e8d545e 2025-05-26) |
| Plateforme | Darwin arm64 (Mac M1 Pro 16GB) |
| Occurrences `native_decide` dans ProjetCollatz | 182 (8 fichiers) |

## Artefacts baseline

- `docs/BIBLE/env-snapshots/2026-04-22-baseline.txt` — env (elan, lean, uname, toolchain, remote)
- `docs/BIBLE/env-snapshots/2026-04-22-baseline-build.log` — `lake build` default (constaté trivial, exe `Main.lean` uniquement)
- `docs/BIBLE/env-snapshots/2026-04-22-baseline-lib-build.log` — `lake build ProjetCollatz` complet (7930 jobs, EXIT 0)
- `docs/BIBLE/env-snapshots/2026-04-22-axioms-central.txt` — résultat brut du probe `#print axioms` (10 théorèmes)
- `docs/BIBLE/env-snapshots/2026-04-22-verify-sh.log` — `verify.sh` VERIFICATION PASSED
- `docs/BIBLE/integrity_logs/baseline-d2fa81a-20260422-173948.sha256` — per-file hashes

## Findings documentés (non-bloquants pour G0, à résoudre en S2 ou provisionnés pour M3)

| ID | Nature | Plan | Réf |
|----|--------|------|-----|
| F1 | `lake build` default = exe trivial `Main.lean`, pas la librairie ; faux positif potentiel sur §3.1 | S2 : ADR pour changer `defaultTargets` ou fixer la doc `reproduce.sh` | L-06, R-09 |
| F2 | 182 × `native_decide` dans ProjetCollatz. À G0 isolés (hors chaîne centrale) ; en M3 ils entreront dans la chaîne via la formalisation de `DerivedLargeKBound` | S2 : créer `expected_axioms.md` avec `propext, Classical.choice, Quot.sound`. Pré-M3 : mettre à jour avec `Lean.ofReduceBool, Lean.trustCompiler` + note dédiée paper | L-07, R-10 |
| F3 | Absences : `reproduce.sh`, `probes/`, `expected_axioms.md` | S2 : copier depuis `Collatz-Junction-N2-Merge/` et adapter | L-02, L-03, L-04, R-06, R-07 |
| F4 | `verify.sh` existant utilise `grep` pour axioms/sorry (insuffisant vs §3.2 NASA) | S2 : remplacer par `reproduce.sh` avec probes `#print axioms` | R-08 |
| Note | `Lean.trustCompiler` apparaît en plus de `Lean.ofReduceBool` pour `native_decide` — METAPROMPT §2 ne mentionnait que le second | S2 : corriger dans toute nouvelle documentation | — |

## Décision S2 (reproduce.sh) — recommandation superviseur

- `reproduce.sh` par défaut utilisera `lake exe cache get` (≤ 15 min sur reviewer modeste)
- Option `--from-source` pour audit profond (≈ 1h30, rigueur maximale)
- ADR à rédiger en S2

## Prochaine action

**G1 planification** (cette session) : consolidation GitHub. Inventaire + plan d'archivage + Red Team sur le plan, puis sign-off Eric avant exécution.

**Classification G1** : P1 (action publique sur GitHub, partiellement réversible via `gh repo unarchive`).

---

**Ce document est append-only et verrouillé en écriture après G0. Toute mise à jour = nouvelle entrée dans `JOURNAL.md` qui référence ce signoff.**
