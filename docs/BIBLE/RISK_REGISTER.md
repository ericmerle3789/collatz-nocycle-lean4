# RISK REGISTER — collatz-nocycle-lean4

**Owner de document** : Claude Opus session (auteur). Revue formelle Eric aux gates.
**Convention** : append-only pour historique ; mises à jour = nouvelle ligne avec date, ancienne ligne conservée barrée.
**Severity** : HIGH (bloquant publication) / MEDIUM (à mitiger) / LOW (surveillance).

---

## Risques actifs

| ID | Risque | Probabilité | Impact | Mitigation | Owner | Statut |
|----|--------|-------------|--------|------------|-------|--------|
| R-01 | `DerivedLargeKBound` qualifié de pétition de principe par relecteur hostile (réplique Signal #1 Junction QuasiUniformity) | MEDIUM | HIGH | Phase Legendre (M2-M3) : remplacer `structure` par théorème Lean prouvé via Legendre 1798 | Eric + Claude | MITIGATION-IN-PROGRESS |
| R-02 | Mathlib ne contient pas les convergents de log₂3 (`Mathlib.NumberTheory.ContinuedFractions.Convergents`) | LOW | HIGH | Spike M2 évalue, formalisation from scratch en plan B (budget ≤ 1500 lignes = STOP) | Claude | TO-ASSESS-M2 |
| R-03 | Toolchain Lean incompat. après update Mathlib | LOW | MEDIUM | `lean-toolchain` pinné à `leanprover/lean4:v4.27.0` (vérifié G0), CI teste, upgrade = P1 + ADR | Claude | MITIGATED |
| R-04 | Dilution d'attention si deux repos publics concurrents | LOW (évité) | MEDIUM | `Collatz-Junction-N2-Merge` reste backup local uniquement ; `Collatz-Junction-Theorem` + `collatz-cycles-lean` à archiver en S1 | Eric | MITIGATED |
| R-05 | `native_decide` caché dans une dépendance ajoute `Lean.ofReduceBool` aux axiomes | LOW | HIGH | `#print axioms` check obligatoire §3.2 + §3.3, déclaration `expected_axioms.md` (à créer S2) | Claude | MITIGATED-PENDING-PROBE |

---

## Risques ajoutés en G0 (baseline 2026-04-22)

| ID | Risque | Probabilité | Impact | Mitigation | Owner | Statut |
|----|--------|-------------|--------|------------|-------|--------|
| R-06 | Absence de `reproduce.sh` avec exit codes 0/1/2/3/4 (convention Junction) ; seul `verify.sh` présent mais utilise `grep` (insuffisant vs §3.2) | MEDIUM | MEDIUM | S2 : copier `reproduce.sh` depuis `Collatz-Junction-N2-Merge/`, adapter aux probes nocycle | Claude | TO-CREATE-S2 |
| R-07 | Absence de `probes/check_central_axioms.lean` et `expected_axioms.md` ; baseline G0 utilise `#print axioms` manuel | MEDIUM | HIGH | S2 : créer probes adaptés aux théorèmes centraux de nocycle + `expected_axioms.md` | Claude | TO-CREATE-S2 |
| R-08 | `verify.sh` existant détecte sorry/axiomes par `grep` uniquement (miss `sorryAx` via macros, imports, tactiques custom) | LOW (état actuel propre) | HIGH (si régression) | Remplacer par `reproduce.sh` avec `#print axioms` check en S2 ; ne pas se fier à verify.sh isolément | Claude | MITIGATION-PLANNED-S2 |
| R-09 | `lake build` sans argument compile uniquement l'exe `projetcollatz` (Main.lean trivial), pas la librairie `ProjetCollatz`. Risque de faux positif sur §3.1 si la commande est utilisée telle qu'écrite dans le manuel NASA | HIGH | HIGH | Toujours utiliser `lake build ProjetCollatz` explicitement. S2 : corriger `defaultTargets` dans `lakefile.toml` ou fixer la doc. Voir L-06 | Claude | IDENTIFIED-G0-BASELINE |
| R-10 | Phase Legendre M3 introduira `Lean.ofReduceBool` + `Lean.trustCompiler` dans la chaîne du théorème central (quand `DerivedLargeKBound` prouvée via `cf_gap_*`). Sans déclaration préventive, risque de qualification "axiome caché" par relecteur | HIGH (certitude à M3) | MEDIUM (mitigable) | Inscrire au plan M3 : (a) mise à jour `expected_axioms.md` avant intégration ; (b) note dédiée dans paper §formalisation ; (c) §3.3 check mis à jour avant commit Legendre. Voir L-07 | Claude | FORESEEN-M3 |

---

## Risques identifiés pendant M3.3 (Phase62 BestApproxBridge)

| ID | Risque | Probabilité | Impact | Mitigation | Owner | Statut |
|----|--------|-------------|--------|------------|-------|--------|
| R-M3.H12 | Bridge `q_n (Phase61, ℕ) ↔ (of logb23).dens (Phase62, ℝ)` non prouvé directement par Mathlib v4.27.0 (4 patterns grep retournent 0 match). Conceptuellement égaux par normalisation CF coprime, mais formalisation demande ~30-50 lignes sous-projet (gcd + Rat.num_div_den + casts ℕ→ℝ). Phase62 Section 6 paramétrique pour ne pas bloquer. | LOW | Phase63 decision | Phase62 Section 6 expose `log23_abs_sub_convergent_le_in_window` (alias enrichi d'un window context, post RT#2 rename pour clarté sémantique). Phase63 choisira instanciation (`(of).dens n` directe OU `q_n n` via bridge construit à ce moment si nécessaire pour compat avec Phase59 `DerivedLargeKBound` signature). `InWindow` Phase61 non orphelin — préservé pour Phase63. | Session B + Worker | DEFERRED-TO-M3.4 (Phase63) |

---

## Historique

- **2026-04-22** : registre initialisé à G0 avec R-01..R-05 (depuis MISSION §7.3) + R-06..R-08 (baseline findings).
- **2026-04-24** : R-M3.H12 ajouté pendant M3.3 Phase62 écriture (proactive disclosure + Option C paramétrique adoption, décision Session B auditor per message archive/to_worker/0056).
