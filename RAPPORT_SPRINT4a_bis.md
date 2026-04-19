# RAPPORT SPRINT 4a-bis — Fermeture axiome `wellDefinedDomain_compl_eq_cylinder`
**Branche** : `claude/binary-compactness`
**Date** : 2026-04-19
**Suite de** : RAPPORT_SPRINT4a.md (verdict BRONZE, 3 axiomes)

---

## 🎯 Verdict : **GREEN-partial** — axiome 3 fermé, 2 axiomes restants

- `lake build ProjetCollatz.PAdic.Cylinders` → EXIT 0, 0 warning
- `lake env lean test/TestCylinders.lean` → EXIT 0
- Axiome `wellDefinedDomain_compl_eq_cylinder` **converti en théorème prouvé**
- Reste **2 axiomes** : `haarZTwo` (opaque) + `cylinder_measure`
- Upgrade de BRONZE (3 axiomes) vers **quasi-GOLD** (2 axiomes justifiés par
  littérature standard Haar + p-adiques, construction effective = Sprint 4a-ter)

---

## 📋 Protocole suivi

1. **Analyse du sorry précédent** : preuve esquissée dans docstring de l'axiome v1.
2. **Tentative 1** : `linear_combination` avec coefficient unit (`h3.unit⁻¹`) → FAIL
   (Lean mélange `↑(h3.unit⁻¹)` et `(↑h3.unit)⁻¹`, deux formes de coercion).
3. **Tentative 2** : `set u := ...` pour uniformiser → FAIL
   (les deux formes subsistent via `ZMod.inv` vs `Units.inv`).
4. **Tentative 3** : reformulation target via `(3 : ZMod (2^L))⁻¹` direct (utilise
   `ZMod.inv` partout, équivalent sémantiquement à `↑(h3.unit⁻¹)` via
   `ZMod.inv_coe_unit`) → **SUCCÈS**.
5. **Red team final** : YELLOW sur docstring d'en-tête obsolète + fragilité
   `map_ofNat` → **fixes appliqués**.

---

## 📊 Détails de la preuve

### Signature du théorème (changée vs v1 axiome)

**Avant (axiome v1)** :
```lean
axiom wellDefinedDomain_compl_eq_cylinder (L : ℕ) :
    (wellDefinedDomain L)ᶜ =
      cylinder (-((isUnit_three_zmod_pow_two L).unit⁻¹ : ZMod (2^L)))
```

**Après (théorème 4a-bis)** :
```lean
theorem wellDefinedDomain_compl_eq_cylinder (L : ℕ) :
    (wellDefinedDomain L)ᶜ = cylinder (-((3 : ZMod (2^L))⁻¹))
```

Les deux signatures sont **sémantiquement équivalentes** via `ZMod.inv_coe_unit`
(Mathlib `ZMod/Basic.lean` ligne 825) : pour une unité `u`, on a
`(↑u : ZMod n)⁻¹ = ↑(u⁻¹ : (ZMod n)ˣ)`. Appliqué à `u = h3.unit` dont la
valeur est 3, les deux formes coïncident.

### Preuve (19 lignes)

```lean
theorem wellDefinedDomain_compl_eq_cylinder (L : ℕ) :
    (wellDefinedDomain L)ᶜ = cylinder (-((3 : ZMod (2^L))⁻¹)) := by
  ext x
  simp only [Set.mem_compl_iff, mem_wellDefinedDomain_iff, not_not,
             cylinder, Set.mem_preimage, Set.mem_singleton_iff]
  have ring_step : PadicInt.toZModPow L (3 * x + 1) =
      3 * PadicInt.toZModPow L x + 1 := by
    simp [map_add, map_mul, map_one, map_ofNat]
  rw [ring_step]
  set y : ZMod (2^L) := PadicInt.toZModPow L x with y_def
  have h3 := isUnit_three_zmod_pow_two L
  have key : (3 : ZMod (2^L)) * (3 : ZMod (2^L))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ h3
  constructor
  · intro h
    linear_combination (3 : ZMod (2^L))⁻¹ * h - y * key
  · intro h
    linear_combination 3 * h - key
```

### Mécanique des `linear_combination`

**Forward `3y+1=0 → y = -3⁻¹`** :
- Combinaison `3⁻¹ * h - y * key`
- = `3⁻¹ · (3y + 1) - y · (3 · 3⁻¹ - 1)`
- = `3 · 3⁻¹ · y + 3⁻¹ - 3 · 3⁻¹ · y + y`
- = `3⁻¹ + y` (termes `3 · 3⁻¹ · y` annulés par commutativité, sans besoin de
  savoir que `3 · 3⁻¹ = 1`)
- Égal à `y - (-3⁻¹) = y + 3⁻¹` ✓

**Reverse `y = -3⁻¹ → 3y+1 = 0`** :
- Combinaison `3 * h - key`
- = `3 · (y - (-3⁻¹)) - (3 · 3⁻¹ - 1)`
- = `3y + 3 · 3⁻¹ - 3 · 3⁻¹ + 1`
- = `3y + 1` ✓

Les deux directions passent par `ring1` après substitution des coefficients
et **ne nécessitent pas** d'évaluation explicite de `3⁻¹` ; seule l'identité
symbolique `3 · 3⁻¹ = 1` (via `key`) est utilisée.

---

## 🔍 Audits effectués

### Red team math reviewer (post-preuve)

**Verdict YELLOW** (preuve mathématiquement correcte + 2 clarifications mineures) :

1. **Check 1-7 PASS** : équivalence sémantique, `ring_step`, `key`,
   `linear_combination` forward, `linear_combination` reverse, sémantique `⁻¹`,
   cohérence aval `wellDefinedDomain_measure`.

2. **Check 8-9 PASS** : réduction axiomes (3 → 2), tests inchangés.

3. **Check 10 FAIL MINEUR** : docstring d'en-tête obsolète ("SILVER, 1 sorry").
   **→ Fixed** (mis à jour en "BRONZE+ / quasi-GOLD, 0 sorry, 2 axiomes, 5 théorèmes").

4. **Fragilité `map_ofNat`** : potentielle mais non bloquante actuellement.
   Tentative de robustification via `push_cast; ring` a échoué (push_cast ne
   convertit pas `toZModPow L 3` → `3`). **→ Conservé en simp original**, qui
   fonctionne et est documenté. Risque de maintenance accepté.

---

## 📊 Bilan chiffré post-4a-bis

| Métrique | 4a (BRONZE) | 4a-bis (quasi-GOLD) |
|----------|------------:|--------------------:|
| Lignes Cylinders.lean | 169 | 185 |
| Sorry | 0 | **0** |
| Axiomes | 3 | **2** |
| Théorèmes prouvés | 5 | **6** (+ `wellDefinedDomain_compl_eq_cylinder`) |
| `lake build` exit | 0 | **0** |
| Warnings build | 0 | **0** |

### Axiomes restants (après 4a-bis)

| Axiome | Justification | Reportée à |
|--------|---------------|-----------|
| `haarZTwo : Measure ZTwo` (`opaque`) | `addHaarMeasure` sur groupe additif compact Hausdorff | Sprint 4a-ter |
| `cylinder_measure` | Pushforward uniforme de Haar via `toZModPow` surjective | Sprint 4a-ter |

Tous deux sont **pure-mesure** (pas de structure ZMod). Sprint 4a-ter devra
construire `addHaarMeasure` sur `ℤ_[2]` et prouver la surjectivité de `toZModPow`
(non présente dans Mathlib v4.27.0).

---

## 🔴 Limites restantes

1. **`map_ofNat` fragile** : reste, mais fonctionne. Alternative `push_cast`
   testée et échouée. `simp [map_add, map_mul, map_one, map_ofNat]` est
   conservé car il passe et est lisible.

2. **2 axiomes pure-mesure** subsistent. Pour GOLD strict il faut construire
   `addHaarMeasure` effectivement — ~10-20h de Lean (hors 4a-ter single sprint).

3. **Équivalence `(3 : ZMod)⁻¹ = ↑(h3.unit⁻¹)`** non formalisée explicitement dans
   le fichier. Si on voulait réconcilier la signature v1 et v2, il faudrait un
   lemme `cylinder_eq_via_unit` via `ZMod.inv_coe_unit`. Non bloquant car les
   clients utilisent `wellDefinedDomain_measure`, pas la signature directe.

4. **Tests inchangés** : 7 examples dans `TestCylinders.lean`, tous PASS avec la
   nouvelle preuve. Pas d'ajout de test pour la nouvelle preuve (mais elle est
   testée implicitement via `wellDefinedDomain_measure` qui l'invoque).

---

## ➡️ Prochaines étapes (Sprint 4a-ter / 4b)

### Sprint 4a-ter (fermeture des 2 derniers axiomes)
- Construire `haarZTwo` via `MeasureTheory.Measure.addHaarMeasure` + chaîne d'instances.
- Prouver `PadicInt.toZModPow_surjective` (contrib potentielle à Mathlib).
- Prouver `cylinder_measure` = pushforward uniforme.
- **GOLD atteint** : 0 sorry, 0 axiome.

### Sprint 4b (`CompactnessDefs.lean`)
- `h : ℕ → ℕ`, `IsCompact k n := h n < k`, lemmes triviaux.
- Interface avec `SyracuseDefs.v2Nat` du projet existant.

---

## 📦 Commit proposé

```
refactor(padic): close wellDefinedDomain_compl axiom

- Convert axiom to theorem via linear_combination + ZMod.mul_inv_of_unit
- Signature refactored: cylinder (-(3 : ZMod (2^L))⁻¹) direct
  (equivalent to previous via ZMod.inv_coe_unit)
- Reduces axiom count 3 → 2 (only haarZTwo + cylinder_measure remain)
- Build + tests EXIT 0, 0 sorry, 0 warnings
- Red team YELLOW → fixed (docstring + robustness notes)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
```

Un seul fichier modifié (`ProjetCollatz/PAdic/Cylinders.lean`), un seul commit.

---

## 🌟 Synthèse en une phrase

> **Sprint 4a-bis complété en ~2h : axiome `wellDefinedDomain_compl_eq_cylinder`
> fermé en théorème prouvé (19 lignes, `linear_combination` + `ZMod.mul_inv_of_unit`),
> upgrade de BRONZE (3 axiomes) vers quasi-GOLD (2 axiomes pure-mesure), red
> team YELLOW adressé, build + tests EXIT 0 — prêt pour commit.**
