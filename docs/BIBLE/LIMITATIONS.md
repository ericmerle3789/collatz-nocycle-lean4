# LIMITATIONS — collatz-nocycle-lean4

Document append-only listant les limitations connues du repo à un instant donné. À joindre en annexe du paper avant toute soumission.

---

## Limitations au G0 (baseline 2026-04-22, commit `d2fa81a`)

### L-01 — `DerivedLargeKBound` encodée comme `structure`
- **Nature** : `ProjetCollatz/Phase59ContinuedFractions.lean:115` expose `DerivedLargeKBound` comme `structure` contenant un champ `large_k_bound : ∀ (n k : ℕ), IsOddCycle n k → k > 1322 → n < 2 ^ 71` (à reconfirmer par lecture directe lors du check §3).
- **Conséquence** : le théorème central `no_nontrivial_cycle_phase59` est *conditionnel* sur cette dérivation, non sur un théorème prouvé en Lean.
- **Justification mathématique** : fractions continues de log₂3 + Legendre 1798 (détaillée dans le paper, section CF).
- **Plan de résolution** : Phase Legendre (M2-M3), remplacement par théorème Lean prouvé → tag `v2.0-preprint`.
- **Risque associé** : R-01 (pétition de principe).

### L-02 — Pas de `reproduce.sh` aux exit codes 0/1/2/3/4
- **Nature** : seul `verify.sh` présent, qui :
  - utilise `grep` pour détecter sorry/axioms (insuffisant vs §3.2 du manuel NASA — ne capture pas `sorryAx` masqué via macros, imports, tactiques custom)
  - ne retourne pas les exit codes de la convention Junction (0 OK / 1 toolchain / 2 build / 3 axioms / 4 sorryAx)
- **Conséquence** : la baseline G0 utilise `#print axioms` manuel comme best-effort, ne peut pas être automatisé à l'état actuel.
- **Plan de résolution** : S2 Hardening — copier `reproduce.sh` depuis `/Users/ericmerle/Documents/Collatz-Junction-N2-Merge/`, adapter.
- **Risque associé** : R-06.

### L-03 — Pas de `probes/` ni `expected_axioms.md`
- **Nature** : répertoire `probes/` absent ; fichier `expected_axioms.md` absent à la racine.
- **Conséquence** : la vérification §3.3 (diff axiomes effectifs vs attendus) ne peut pas être automatisée.
- **Plan de résolution** : S2 — créer `probes/check_sorry.lean` et `probes/check_central_axioms.lean` (adaptés aux théorèmes centraux de nocycle : au minimum `no_nontrivial_cycle_phase59`, + théorèmes support identifiés par l'audit du 2026-04-22) + `expected_axioms.md` listant `propext`, `Classical.choice`, `Quot.sound` et rien d'autre.
- **Risque associé** : R-05, R-07.

### L-04 — CI GitHub Actions minimale
- **Nature** : `.github/workflows/build.yml` existe (à examiner en détail lors de S2) mais sa couverture vs les 4 checks §3 n'est pas auditée.
- **Conséquence** : la CI pourrait PASS sans détecter un axiome ajouté inopinément.
- **Plan de résolution** : S2 — copier `.github/workflows/verify.yml` depuis Junction, merger avec `build.yml`.
- **Risque associé** : R-07.

### L-05 — Références bibliographiques non entièrement DOI-vérifiées
- **Nature** : `HYPOTHESES.md` documente les hypothèses externes ; DOI-check complet (Baker 1966, Rhin 1987, Hercher 2023) requis §17 Lock 2 avant submit G6. Seul Barina 2025 (DOI 10.1007/s11227-025-07337-0) est CONFIRMED à ce jour.
- **Plan de résolution** : pre-G6, cf. Annexe B du manuel NASA.
- **Risque associé** : aucun risque bloquant à G0 ; blocant à G6.

### L-07 — `native_decide` présent dans cf_gap_* et cf_nbound_* (isolé à G0, sera dans la chaîne en M3)
- **Nature** : 182 occurrences de `native_decide` réparties sur 8 fichiers ProjetCollatz (Phase29 : 97×, Phase13 : 22×, Phase59 : 28×, Phase12 : 14×, Phase30 : 11×, Phase28 : 4×, Phase58 : 4×, Phase56 : 2×). À G0, ces théorèmes **ne sont pas dans la chaîne** de `no_nontrivial_cycle_phase59` : le probe `#print axioms` de 2026-04-22 (`docs/BIBLE/env-snapshots/2026-04-22-axioms-central.txt`) confirme que les 7 théorèmes centraux (`no_nontrivial_cycle_phase59/final/derived/full`, `no_cycle_k_le_1322`, `no_cycle_k_gt_1322`, `sdw_from_cf`) dépendent uniquement de `propext, Classical.choice, Quot.sound`.
- **Mécanisme d'isolation** : `DerivedLargeKBound` est une `structure` prise *en paramètre* par le théorème central. Les `cf_gap_*` / `cf_nbound_*` sont des lemmes de justification mathématique du contenu de cette structure mais ne participent pas à la preuve — ils ne deviennent pertinents que quand la structure est *instanciée*.
- **Évidence échantillon** : `cf_gap_8`, `cf_gap_13`, `cf_nbound_8` dépendent de `[propext, Lean.ofReduceBool, Lean.trustCompiler]`. Note : `Lean.trustCompiler` en plus de `Lean.ofReduceBool` (METAPROMPT §2 ne mentionnait que le premier).
- **Conséquence pour G0** : **pas de violation** de la claim "3 axiomes fondamentaux" pour le théorème central. METAPROMPT §2 confirmé sur ce point.
- **Conséquence pour M3 (Phase Legendre)** : quand `DerivedLargeKBound` sera prouvée via `cf_gap_*` + Legendre, `Lean.ofReduceBool` et `Lean.trustCompiler` entreront dans la chaîne du théorème central. **À prévoir** : déclaration explicite dans `expected_axioms.md` + note dédiée dans le paper (cf. MISSION_NASA §10 : `native_decide` autorisé avec déclaration explicite).
- **Plan de résolution** : inscrire dans le plan M3 l'étape "mettre à jour `expected_axioms.md` avec `Lean.ofReduceBool` + `Lean.trustCompiler` quand `DerivedLargeKBound` devient théorème".
- **Risque associé** : voir R-10 (nouveau).

### L-06 — `lake build` (default) ne compile pas la librairie ProjetCollatz
- **Nature** : `lakefile.toml` définit `defaultTargets = ["projetcollatz"]` (l'*exe* `Main.lean` = "Hello Collatz"), pas la *library* `ProjetCollatz`. Un `lake build` sans argument passe EXIT 0 en ~1 min en ne compilant que l'exe trivial, sans toucher Mathlib ni les Phase* files.
- **Conséquence** : la commande `lake build` du manuel NASA §3.1 donne un faux positif si exécutée sans argument explicite sur ce repo. Le vrai build complet exige `lake build ProjetCollatz`.
- **Évidence baseline G0** : log `env-snapshots/2026-04-22-baseline-build.log` montre 4 jobs totaux en 1:01.59, dont aucun fichier Mathlib ni Phase*. À comparer avec `2026-04-22-baseline-lib-build.log` (cible `ProjetCollatz` explicite).
- **Plan de résolution** : S2 Hardening — soit changer `defaultTargets = ["ProjetCollatz"]` dans `lakefile.toml`, soit documenter explicitement dans `reproduce.sh` la commande `lake build ProjetCollatz` (préféré : explicite > implicite). ADR à rédiger.
- **Risque associé** : **nouveau risque** à ajouter à RISK_REGISTER comme R-09.

---

## Historique

- **2026-04-22 G0** : document initialisé. L-01 à L-05 identifiés à partir de l'inventaire du working tree après fresh clone.
