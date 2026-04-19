# RAPPORT — Test empirique « h comme certificat anti-cycle »
**Branche** : `claude/binary-compactness` (analyse R&D)
**Date** : 2026-04-19
**Trigger** : flash d'Eric — « Si le 0000 reste 0000 il n'y a pas de cycle.
Si un 1 apparaît dans le bloc, il y a cycle. »
**Révisé** : après red team rétrospectif (YELLOW, 9 fixes appliqués)

---

## 🎯 Verdict final : **DIP_EARLY_STRONG** (hypothèse brute rejetée, mais interprétation nuancée)

- **96.4%** des orbites Syracuse testées ont leur 1er dip `h < 4` **alors que
  `bit_length(n) ≥ 80% bit_length(n_initial)`** — donc `n` est encore à sa
  taille initiale.
- **100%** des orbites dipent à `bl ≥ bl_init/2` (seule 1 orbite sur 3200 fait
  exception).
- **Position relative médiane du 1er dip : `0.000` à `0.036`** — dans les tous
  premiers pas.
- L'hypothèse brute *« h ≥ 4 ⟹ pas de cycle »* est donc **rejetée** par les
  données : `h` chute sous 4 très rapidement, bien avant toute approche du
  cycle trivial.

---

## ⚠️ Caveats red team rétrospectif (9 fixes intégrés)

1. **Sanity check ajouté** : `h()` Python testé contre 12 valeurs Lean de
   référence (`h(267)=4`, `h(1025)=9`, etc.) — PASS.
2. **Bug L129 corrigé** : `if first_below is not None` au lieu de test truthy.
3. **Seuil `bl > 10` (absolu) remplacé par seuils relatifs** `bl/bl_initial ≥ 0.5`
   et `≥ 0.8`. L'ancien 98.8% était un artefact du fait que TOUTES les
   orbites commencent à `bl > 10` par construction.
4. **TAUTOLOGIE explicitée** : `orbits_never_below_4 = 0` est FORCÉ par la
   conjecture de Collatz (toutes orbites atteignent 1). Ce critère ne teste
   RIEN sur les orbites Collatz réelles.
5. **Non-falsifiabilité** : aucun cycle non-trivial n'existe pour `n < 2^68`
   (vérification numérique Oliveira e Silva, Roosendaal). L'hypothèse
   d'Eric n'est donc **PAS falsifiable empiriquement** : on ne peut pas la
   tester sur un cycle qui n'existe pas. Les tests ici mesurent un signal
   **adjacent** : « à quelle phase de l'orbite `h` chute-t-il sous 4 ? ».
6. **Renomage du verdict** : `NO_SIGNAL` (trop négatif, laisse croire qu'il
   n'y a aucune information) → `DIP_EARLY_STRONG` (capture le vrai signal :
   dip TRÈS précoce).
7. **Chiffre `98.8%` retiré** : non robuste au choix du seuil absolu. Remplacé
   par le robuste `96.4% à bl ≥ 80% bl_initial` et `100% à bl ≥ bl_init/2`.
8. **Test 5 (faux cycle)** : clairement articulé comme observation de
   construction, pas comme réfutation de l'hypothèse.
9. **Interprétation affaiblie** : pistes constructives explicitées (moyenne
   temporelle, durée de persistance, combinaison d'invariants).

---

## 📊 Résultats chiffrés révisés

### Test 1 — Cycle trivial {1, 2, 4}

| n | h(n) | < 4 ? |
|---|-----:|:-----:|
| 1 | 0    | ✓     |
| 2 | 0    | ✓     |
| 4 | 0    | ✓     |

`syracuse_next(1) = 1` (point fixe compressé). Compatible mais trivialement
(h(n) ≤ bit_length(n) - 2 pour les petits n).

### Test 2 — Orbites Syracuse aléatoires

| Range | bl | N | frac h≥4 | median 1st-dip rel | **median bl_ratio au 1st dip** |
|-------|:--:|--:|:--------:|:------------------:|:----------------------------:|
| small  | 10-14 | 1000 | 0.178 ± 0.062 | 0.000 | **1.000** |
| medium | 20-24 | 1000 | 0.301 ± 0.074 | 0.010 | **1.000** |
| large  | 30-34 | 1000 | 0.404 ± 0.079 | 0.017 | **1.000** |
| huge   | 60-64 |  200 | 0.595 ± 0.068 | 0.036 | **0.968** |

**Observation clé** : le ratio **bl au 1er dip / bl initial** a pour médiane
**1.000** (pour small/medium/large) et **0.968** (pour huge). Autrement dit :
quand `h` franchit 4 pour la 1ère fois, `n` est encore à sa taille initiale.

### Test 3 — Phase de l'orbite au 1er dip (critères RELATIFS)

| Critère | Nombre | % |
|---------|------:|----:|
| Dip à `bl ≥ 80% bl_initial` (TRÈS précoce) | 3085 | **96.4%** |
| Dip à `bl ≥ 50% bl_initial` (précoce) | 3199 | **100.0%** |
| Dip à `bl < 50% bl_initial` (tardif) | 1 | 0.0% |
| Aucun dip (TAUTOLOGIE Collatz) | 0 | 0.0% |

**Une seule orbite sur 3200** a son 1er dip après que `n` ait perdu plus de
la moitié de sa taille. Le signal est sans ambiguïté : **`h` chute dès le
départ**.

### Test 5 — Faux cycle artificiel

Suite `{33, 65, 129, 257, 513, 1025}` : `h ∈ {4, 5, 6, 7, 8, 9}`, tous `≥ 4`.
Mais `T(33) = 25 ≠ 65`, donc **pas un cycle Syracuse**.
Cette construction illustre qu'on peut librement **fabriquer** des suites
d'entiers avec `h ≥ 4` partout, mais elle ne teste PAS l'hypothèse d'Eric :
elle confirme seulement que l'hypothèse n'est pas tautologique (ce qui est
bien).

---

## 🔬 Interprétation mathématique

### Pourquoi l'hypothèse brute échoue

1. **h est hautement fluctuant sous Syracuse** : cohérent avec l'étape 1
   (Sprint 4d), `P(Δh > 0) ≈ 0.32`, `mean(Δh) ≈ 0`. `h` fait une marche
   aléatoire autour d'une valeur moyenne proche de 2-3, donc franchit
   constamment le seuil 4.
2. **h < 4 ne force pas n petit** : un `n` de 60 bits avec pattern
   alternant `1010...101` a `h(n) = 1`. La descente de `h` n'implique PAS
   la descente de `n`.
3. **Conséquence** : `h = 4` n'est pas une « frontière » stable — c'est une
   valeur centrale typique autour de laquelle `h` oscille.

### Non-testabilité empirique (red team B9)

Pour tester l'hypothèse d'Eric *au sens strict*, il faudrait :
- Un cycle non-trivial Collatz (n'existe pas ≤ 2⁶⁸)
- OU un analogue sur un système dynamique avec cycles connus

Ce test sur Collatz mesure donc un **proxy** : « pendant combien de temps `h`
reste-t-il au-dessus de 4 avant de chuter ? ». La réponse empirique est :
**zéro ou presque**.

### Variantes affaiblies potentiellement viables

1. **Moyenne temporelle** : `E_orbite[𝟙_{h ≥ 4}]` croît de `0.18` à `0.60`
   avec `log₂(n)` — tend peut-être vers 1 pour n → ∞ ? Testable plus loin.
2. **Durée de persistance** : existe-t-il `C` telle que toute orbite
   maintient `h ≥ 4` pendant `≥ C · log₂(n)` pas consécutifs ? Non testé.
3. **Combinaison `h + log₂(n)`** comme Lyapunov stochastique ? Cohérent avec
   l'étape 1 (queue exponentielle de `Δh`, Sprint 4d).

---

## 📂 Artefacts

- [analysis/compactness/test_h_as_cycle_detector.py](analysis/compactness/test_h_as_cycle_detector.py) — 370 lignes, seed=42, 9 fixes red team
- [analysis/compactness/h_cycle_detector_results.json](analysis/compactness/h_cycle_detector_results.json) — incluant `caveats_red_team`
- [analysis/compactness/h_along_orbits.png](analysis/compactness/h_along_orbits.png) — 4 orbites : `h` oscillant entre 0 et 12, franchit 4 constamment
- [analysis/compactness/min_h_distribution.png](analysis/compactness/min_h_distribution.png)
- [analysis/compactness/bl_at_first_dip.png](analysis/compactness/bl_at_first_dip.png)

---

## 🌟 Synthèse en une phrase

> **L'hypothèse brute « h ≥ 4 persistant ⟹ pas de cycle » est rejetée par
> les données : 96.4% des 3200 orbites Syracuse dipent sous `h = 4` alors
> que `bit_length(n) ≥ 80%` de la valeur initiale (médiane du ratio :
> **1.000**), c'est-à-dire dès les premiers pas ; par ailleurs l'hypothèse
> est strictement non-falsifiable sur Collatz (aucun cycle non-trivial
> connu), donc ce test mesure un signal adjacent — et confirme que `h` est
> une variable fluctuante autour de `~2-3`, pas une frontière stable.**

---

## ➡️ Recommandation

- **Ne pas formaliser** en Lean (hypothèse brute rejetée).
- **Garder les artefacts** comme contribution scientifique négative
  rigoureusement documentée.
- **Piste possible pour Sprint 4e** : combiner `h` avec `log₂(n)` ou
  mesure temporelle `E_orbite[𝟙_{h ≥ 4}]` pour obtenir un vrai Lyapunov
  stochastique.
