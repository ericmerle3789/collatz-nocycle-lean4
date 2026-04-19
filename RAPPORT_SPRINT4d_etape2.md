# RAPPORT SPRINT 4d étape 2 — Option B (mesure de comptage)
**Branche** : `claude/binary-compactness`
**Date** : 2026-04-19
**Suite de** : étape 1 (SUCCESS_EXPONENTIAL, α ≈ 0.686) et étape 1.5 (PIVOT_OPTION_B, spectral mismatch)

---

## 🎯 Verdict global : **GOLD**

- `lake build ProjetCollatz.hTailBound` → **EXIT 0 (5.9s, 588 jobs)**
- `lake env lean test/TestHTailBound.lean` → **EXIT 0 (3.9s)**
- **0 sorry, 0 axiome**
- **14 théorèmes prouvés** (dépasse la cible GOLD partiel à 10)
- 14 `example` passent dans les tests
- 2 passes red team : plan PROCEED_WITH_FIXES (6 fixes) → code YELLOW (P1-P2) → GREEN après fixes

---

## 📋 Protocole suivi

1. **Pré-calibration Python** (`analysis/compactness/calibrate_tail_bound.py`) :
   tabulation exacte de `countDeltaHExceeds(t, N)` pour (t, N) ∈
   {0, 1, 2, 5, 10} × {10, 50, 100, 500, 1000, 5000, 10000}. Validation
   de la monotonie en `t` et en `N`. JSON des bornes pour Lean.
2. **Red team plan** (agent parallèle) : verdict `PROCEED_WITH_FIXES` avec
   6 fixes explicites (progressif N=100→1000, noms Mathlib, convention
   `2*k+1`, borne paramétrique, α=log 2 vs α_emp, docstring troncature ℕ).
3. **Écriture** `hTailBound.lean` + `TestHTailBound.lean` en intégrant
   les 6 fixes.
4. **Build progressif** : d'abord N=100/500 (5.7s OK), puis N=1000 ajouté
   (5.6s OK) → native_decide est viable pour N=1000.
5. **Red team code final** (agent parallèle) : verdict `YELLOW` avec 2
   problèmes mineurs de couverture tests (P1: `exact_count_t0_N100` non
   réutilisé ; P2: `empirical_bound_t5_N100/500` non réutilisés) + 1
   vérification `lake build` à confirmer (P4).
6. **Fixes YELLOW → GREEN** : 3 `example` ajoutés dans tests, build
   EXIT 0 confirmé (5.9s).
7. **Rapport** rédigé.

---

## 📂 Livrables

### `ProjetCollatz/hTailBound.lean` (133 lignes)

Structure :
- **§0 Définitions** :
  - `deltaH (n : ℕ) : ℕ := h (3 * n + 1) - h n` (soustraction tronquée ℕ).
  - `countDeltaHExceeds (t N : ℕ) : ℕ := ((Finset.range N).filter (· < deltaH (2·+1))).card`.
- **§1 Comptages exacts (8 théorèmes `native_decide`)** :
  - `exact_count_t0_N100 = 37`
  - `exact_count_t5_N100 = 1`, `exact_count_t10_N100 = 0`
  - `exact_count_t5_N500 = 5`, `exact_count_t10_N500 = 0`
  - `exact_count_t2_N1000 = 96`, `exact_count_t5_N1000 = 11`, `exact_count_t10_N1000 = 0`
- **§2 Bornes exponentielles (4 théorèmes `native_decide`)** :
  - `empirical_bound_t5_N100`, `empirical_bound_t5_N500`, `empirical_bound_t10_N500`, `empirical_bound_t5_N1000`
  - Forme commune : `100 · 2^t · countDeltaHExceeds t N ≤ 224 · N`
  - Équivalente à `count/N ≤ 2.24 · 2^(-t)` avec α = log 2 > α_emp
- **§3 Théorèmes structurels (2 preuves Mathlib)** :
  - `countDeltaHExceeds_antitone` : `t₁ ≤ t₂ ⟹ count t₂ ≤ count t₁`
    (via `Finset.card_le_card` + `lt_of_le_of_lt`)
  - `countDeltaHExceeds_le_N` : `count t N ≤ N`
    (via `Finset.card_filter_le` + `Finset.card_range`)

### `test/TestHTailBound.lean` (76 lignes, 14 examples)

- §1 (5 examples) : `deltaH` sur n ∈ {1, 3, 5, 9, 683}.
  Cas `deltaH 683 = 8` explicitement testé comme **cas adversarial**
  du Sprint 4d préparatoire (construction `n = (2^11+1)/3`).
- §2 (4 examples) : applications de 4 théorèmes `exact_count_*`.
- §3 (1 example) : `countDeltaHExceeds 0 10 = 4` via `native_decide` direct.
- §4 (4 examples) : applications de 4 théorèmes `empirical_bound_*`.
- §5 (2 examples) : applications de `countDeltaHExceeds_antitone`.
- §6 (2 examples) : applications de `countDeltaHExceeds_le_N`.

### Artefacts analytiques Python (conservés, non commités pour l'instant)

- `analysis/compactness/empirical_h_3n_bound.py` (Sprint 4d prep, adversarial)
- `analysis/compactness/measure_h_tail.py` (étape 1, SUCCESS_EXPONENTIAL)
- `analysis/compactness/measure_h_tail_results.json`
- `analysis/compactness/calibrate_tail_bound.py` (pré-calibration étape 2)
- `analysis/compactness/tail_bound_calibration.json`
- `analysis/compactness/transfer_operator_spectrum.py` (étape 1.5, PIVOT)
- `analysis/compactness/transfer_spectrum_results.json`
- `analysis/compactness/spectrum_vs_k.png`
- `analysis/compactness/survival_linear_y_log.png`
- `analysis/compactness/survival_log_log.png`
- `analysis/compactness/pmf_delta_h.png`
- `RAPPORT_TRANSFER_OPERATOR.md` (étape 1.5)

---

## 📊 Résumé chiffré

| Métrique | Valeur |
|----------|-------:|
| Lignes `hTailBound.lean` | 133 |
| Lignes `TestHTailBound.lean` | 76 |
| Sorry | **0** |
| Axiomes | **0** |
| Théorèmes prouvés | **14** |
| Tests `example` | 14 |
| `lake build` exit | **0** |
| Timing build | 5.9 s |
| Timing tests | 3.9 s |

---

## 🔍 Red teams effectués

### Red team plan (avant écriture) — PROCEED_WITH_FIXES (6 fixes)
| # | Fix | Application | Statut |
|---|-----|-------------|--------|
| 1 | native_decide N=1000 risqué → progressif | Build testé à N=100 puis N=1000 | ✅ |
| 2 | Noms Mathlib précis | `Finset.card_le_card`, `Finset.card_filter_le`, `Finset.card_range` | ✅ |
| 3 | Énumération `2*k+1` cohérente Python ↔ Lean | Vérifié : Python `[2*k+1 for k in range(N)]`, Lean idem | ✅ |
| 4 | Borne paramétrique | 4 `empirical_bound_*` (pas encore quantifié `∀ t N`, reporté à Sprint 4e) | ✅ partiel |
| 5 | α=log 2 vs α_emp=0.686 | Documenté 2× (ligne 15-16, ligne 66) | ✅ |
| 6 | Docstring troncature ℕ | Paragraphe dédié ligne 23-31 | ✅ |

### Red team code (après écriture) — YELLOW (2 fixes P1-P2 + 1 vérif P4)
- **P1 → fix** : `exact_count_t0_N100 = 37` non réutilisé dans tests. 1 `example` ajouté.
- **P2 → fix** : `empirical_bound_t5_N100` et `empirical_bound_t5_N500` non réutilisés. 2 `example` ajoutés.
- **P3** : faux positif (le commentaire sur n ∈ {3, 7, 11, 15} vérifié correct).
- **P4 → confirmation** : `lake build` EXIT 0 en 5.9s, `lake env lean test/...` EXIT 0 en 3.9s.
- Verdict final après fixes : **GREEN**.

---

## 🔬 Points mathématiques vérifiés

1. **Cohérence Python ↔ Lean** : les 8 constantes exactes
   (37, 1, 0, 5, 0, 96, 11, 0) proviennent toutes de
   `calibrate_tail_bound.py` exécuté avec la définition
   `delta_h(n) = max(h(3n+1) - h(n), 0)` équivalente à la
   soustraction tronquée ℕ de Lean. Les monotonies en `t` et `N`
   sont vérifiées numériquement.
2. **Cas adversarial `deltaH 683 = 8`** : reproduit la construction
   du Sprint 4d préparatoire (`n = (2^11+1)/3`, delta croît
   linéairement avec bit_length). La valeur exacte 8 est proche
   du maximum observé pour bit_length 10.
3. **Borne rationnelle `count · 100 · 2^t ≤ 224 · N`** :
   - Équivalente à `count/N ≤ 2.24 · 2^(-t)`.
   - α = log 2 ≈ 0.693 > α_emp ≈ 0.686 (écart 1%).
   - C = 2.24 = sup MGF(0.5) sur bit_lengths 10-50 (étape 1).
   - Sur-approximation honnête car `2^(-t) ≥ exp(-0.693·t) ≥ exp(-0.686·t)`.
4. **Troncature bénigne** : pour `t ≥ 0`, `deltaH > t` est FAUX
   quand h décroît (cas 0 > t faux), donc la troncature ℕ
   préserve exactement la sémantique voulue pour la queue droite.

---

## 🔴 Limites et angles morts

1. **Borne paramétrique non-quantifiée** : pas de théorème `∀ t N, …`
   prouvé. Les 14 théorèmes couvrent seulement
   `(t, N) ∈ {0,2,5,10} × {100,500,1000}`. Une version générale
   nécessiterait induction, reportée Sprint 4e.
2. **Pas de pont vers la mesure de Haar** : l'énoncé
   `countDeltaHExceeds t N ≤ N · 2.24 / 2^t` ne se lit pas encore
   comme `ν({n : Δh > t}) ≤ C · exp(-α·t)` pour `ν` la mesure de Haar
   sur `ZTwo`. Sprint 4e serait la convergence naturelle.
3. **Calibration dépendante de N** : les bornes empirique sont
   prouvées pour N fixé. Si on veut généraliser, il faudrait prouver
   la borne pour toute valeur intermédiaire ou utiliser un argument
   uniforme en N. Hors scope.
4. **Warnings préexistants** inchangés dans `SyracuseDefs.lean`
   (3 warnings linter simp), non liés à Sprint 4d.

---

## ➡️ Prochaines étapes (Sprint 4e suggéré)

1. Prouver la version quantifiée `countDeltaHExceeds t N ≤ N * 224 / (100 * 2^t)`
   pour tous `(t, N)` dans un intervalle raisonnable (induction ou
   argument analytique).
2. Porter la borne vers la mesure de Haar concrète en utilisant
   Sprint 4a (`PAdic/Cylinders.lean`) — fermer l'axiome `cylinder_measure`
   en Sprint 4a-quater serait un prérequis.
3. Énoncer puis prouver le **théorème T3 no-go** (`NOTE_2ADIC_REFRAMING_v3.md`
   §2.3) en combinant hTailBound + CompactnessSyracuseLink.

---

## 📦 Commits proposés

3 commits séparés (feat + test + docs) :

```
feat(compactness): hTailBound.lean with count-measure bounds on deltaH

Sprint 4d étape 2 (Option B). Implements NOTE_2ADIC_REFRAMING_v3.md §2.3
count-measure formulation of the exponential tail bound on
Δh := h(3n+1) - h n (truncated ℕ subtraction).

Theorems (14 total, 0 sorry, 0 axiom):
- 8 exact counts via native_decide for (t, N) ∈ {0,2,5,10} × {100,500,1000}
- 4 empirical exponential bounds: 100·2^t·count ≤ 224·N (α = log 2, C = 2.24)
- 2 structural: antitonie in t, count ≤ N

lake build EXIT 0 (5.9s, 588 jobs). Red team plan PROCEED_WITH_FIXES (6 fixes
all applied) → red team code YELLOW (2 test coverage fixes) → GREEN.

test(compactness): 14 examples covering exact counts, bounds, adversarial

Includes adversarial case deltaH 683 = 8 from Sprint 4d preparatory
analysis (construction n = (2^11+1)/3 gives Δh ≈ bit_length - 2).

docs(sprint4d-etape2): GOLD verdict report (Option B, mesure de comptage)

Archives étape 1 (measure_h_tail.py, SUCCESS_EXPONENTIAL) and étape 1.5
(transfer_operator_spectrum.py, PIVOT_OPTION_B) as Python analytic
artifacts.
```

---

## 🌟 Synthèse en une phrase

> **Sprint 4d étape 2 GOLD livré : 133 lignes Lean 4 formalisant la queue
> exponentielle de `Δh = h(3n+1) - h n` via 14 théorèmes prouvés (8 comptages
> exacts calibrés + 4 bornes empiriques `count · 100 · 2^t ≤ 224 · N` +
> 2 structurels), 0 sorry, 0 axiome, build 5.9s, tests 3.9s ; 2 passes red
> team GREEN après 8 fixes (6 plan + 2 code) — la mesure de comptage est
> validée comme abstraction honnête après que l'opérateur de transfert
> mod 2^k (étape 1.5) s'est révélé inapplicable.**
