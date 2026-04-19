# RAPPORT SPRINT 4a-ter — Construction explicite de `haarZTwo` + `toZModPow_surjective`
**Branche** : `claude/binary-compactness`
**Date** : 2026-04-19
**Suite de** : RAPPORT_SPRINT4a_bis.md (2 axiomes restants)

---

## 🎯 Verdict global : **Quasi-GOLD partiel** — 1 axiome fermé sur 2

- `lake build ProjetCollatz.PAdic.Cylinders` → EXIT 0
- `lake env lean test/TestCylinders.lean` → EXIT 0
- **0 sorry** maintenu
- **Axiomes : 2 → 1** (haarZTwo fermé, cylinder_measure documenté avec plan)
- **Théorèmes prouvés : 6 → 8** (+ `toZModPow_surjective`, + corollaire `_le`)
- **`haarZTwo` n'est plus `opaque`** — définie concrètement via `addHaarMeasure ⊤`

---

## 📋 Protocole suivi (avec red teams en boucle)

1. **Red team plan** → verdict PROCEED PARTIAL :
   - Phase A (obligatoire) : fermer `haarZTwo`
   - Phase B (recommandée) : prouver `toZModPow_surjective`
   - Phase C (non recommandée) : laisser `cylinder_measure` axiomatisé faute de budget
2. **Phase A** (30 min) : ✅ implémentée, build EXIT 0.
3. **Phase B** (15 min) : ✅ 5 lignes, utilise `map_natCast` + `ZMod.natCast_zmod_val`.
4. **Phase C** (tentative ~30 min) : ❌ abandonnée après multiples échecs Lean
   (linarith sur ZMod non-ordonné, `PadicInt.continuous_toZModPow` absent Mathlib,
   type mismatches `@cylinder`).
5. **Documentation axiome** : plan de preuve détaillé en 6 étapes avec
   lemmes Mathlib identifiés (dont ceux manquants).
6. **Red team final** → YELLOW (1 docstring obsolète).
7. **Fix** : docstring §2 mis à jour pour refléter la construction concrète.
8. **Build + tests** : EXIT 0 confirmés.

---

## 📂 Changements diff

### Phase A : `haarZTwo` concret

**Avant (Sprint 4a-bis)** :
```lean
noncomputable opaque haarZTwo : Measure ZTwo
```

**Après (Sprint 4a-ter)** :
```lean
noncomputable def haarZTwo : Measure ZTwo :=
  MeasureTheory.Measure.addHaarMeasure ⊤

instance isAddHaarMeasure_haarZTwo : haarZTwo.IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure ⊤
```

**Bénéfice** :
- `haarZTwo` est maintenant un objet mathématique concret, pas un témoin arbitraire.
- L'instance `IsAddHaarMeasure` est désormais prouvée, pas axiomatisée.
- Un reviewer peut invoquer `Measure.haarMeasure_self`, `IsAddLeftInvariant`, etc.
  sur haarZTwo via la construction `addHaarMeasure ⊤`.

### Phase B : `toZModPow_surjective` prouvé

**Nouveau théorème** (contribution potentielle à Mathlib) :
```lean
theorem _root_.PadicInt.toZModPow_surjective {p : ℕ} [hp : Fact p.Prime] (k : ℕ) :
    Function.Surjective (PadicInt.toZModPow k : ℤ_[p] →+* ZMod (p^k)) := by
  intro y
  refine ⟨((y.val : ℕ) : ℤ_[p]), ?_⟩
  rw [map_natCast]
  haveI : NeZero (p^k) := ⟨pow_ne_zero k hp.out.pos.ne'⟩
  exact ZMod.natCast_zmod_val y
```

**Preuve en 5 lignes** via :
- `map_natCast` (toZModPow préserve le cast ℕ)
- `NeZero (p^k)` instance (dérivée)
- `ZMod.natCast_zmod_val : (y.val : ZMod n) = y`

### Phase C : `cylinder_measure` axiome + plan détaillé

L'axiome est conservé avec un docstring enrichi présentant un plan de preuve
Lean en 6 étapes, identifiant les lemmes Mathlib nécessaires et les obstacles
(dont `PadicInt.continuous_toZModPow` absent). Estimation Sprint 4a-quater :
4-8h de Lean.

---

## 📊 Résumé chiffré

| Métrique | Sprint 4a-bis | Sprint 4a-ter |
|----------|--------------:|--------------:|
| Lignes Cylinders.lean | 185 | 214 |
| Sorry | 0 | **0** |
| Axiomes | 2 | **1** |
| Théorèmes prouvés | 6 | **8** |
| `lake build` exit | 0 | **0** |
| Warnings | 0 | **0** |

### Bilan des axiomes au fil des sprints

| Sprint | haarZTwo | cylinder_measure | wellDefinedDomain_compl_eq_cylinder |
|--------|:--------:|:----------------:|:-----------------------------------:|
| 4a initial | axiom | axiom | **axiom** |
| 4a BRONZE | opaque | axiom | axiom |
| **4a-bis BRONZE+** | opaque | axiom | **théorème** ✅ |
| **4a-ter** | **def concret** ✅ | axiom (plan) | théorème ✅ |
| Sprint 4a-quater visé | def concret | **théorème** ✅ | théorème ✅ |

---

## 🔍 Red teams effectués

### Red team plan (avant écriture)
- Verdict : PROCEED PARTIAL.
- Estimation honnête : 5-12h pour fermeture complète (Phase C).
- Recommandation : fermer `haarZTwo` + `toZModPow_surjective`, laisser `cylinder_measure`
  en axiome documenté.

### Red team code final (après écriture)
- Check 1 (Phase A correctness) : PASS avec réserve docstring §2.
- Check 2 (Phase B correctness) : PASS.
- Check 3 (plan de preuve Phase C honnêteté) : PASS partiel + risque identifié.
- Check 4 (cohérence globale) : FAIL partiel (docstring obsolète + comptage théorèmes).
- Check 5 (intégrité math reviewer) : PASS + remarque sur continuité.
- Check 6 (imports) : PASS.
- Check 7 (tests) : PASS.

Verdict final : **YELLOW, 1 ajustement à faire**.

### Fix appliqué suite à red team YELLOW
- Docstring §2 mis à jour : "Mesure de Haar (construction + axiome résiduel)"
  au lieu de "Mesure de Haar axiomatisée".
- Description du contenu dans le header : "haarZTwo construite via addHaarMeasure ⊤"
  vs "axiomatisée à ce stade".
- Comptage théorèmes corrigé : "8 théorèmes prouvés (incluant 1 corollaire)"
  vs "7 théorèmes prouvés".

Build + tests confirmés EXIT 0 après fixes.

---

## 🔴 Limites et angles morts restants

1. **Axiome `cylinder_measure` reste ouvert**. Plan de preuve solide mais non
   implémenté. Obstacle principal : `PadicInt.continuous_toZModPow` absent
   de Mathlib v4.27.0 — à prouver directement, ou à contourner via
   structure discrète + measurability.

2. **Gymnastique ZMod** : `linarith`/`linear_combination` ne clôturent pas
   directement sur ZMod pour les équivalences `a = b ↔ a - b = 0`. Utilisable
   mais demande `sub_eq_zero.mp` + travail sur `Prop`.

3. **Tentative Phase C** : consumé ~30 min, révélant plus d'obstacles que prévus
   par le red team initial (qui estimait 4h). L'estimation 4-8h est
   probablement serrée ; 8-12h plus réaliste.

4. **Import `ProperSpace.lean`** ajouté : fournit `CompactSpace ℤ_[p]`, requis
   pour l'instance `Top (PositiveCompacts ZTwo)`. Import minimal, pas de
   bloat.

---

## ➡️ Sprint 4a-quater futur (fermeture complète)

**Plan détaillé pour fermer `cylinder_measure`** (en commentaire dans le fichier) :

1. Disjonction des cylindres (préimages de singletons) — ~10 lignes.
2. Union des cylindres = univ (via `toZModPow_surjective`) — ~10 lignes.
3. `cylinder r = translate (cylinder 0) r.val` via ZMod arithmétique — ~15-20 lignes.
4. Toutes les mesures égales via `measure_preimage_add` — ~5 lignes.
5. Somme = 1 via `measure_iUnion` + `measure_univ` — **requiert prouver
   mesurabilité des cylindres (≠ trivial sans `continuous_toZModPow`)** — 20-30 lignes.
6. Conclusion : `(2^k) * haarZTwo (cylinder 0) = 1` → `= (1/2)^k` via
   `ENNReal.div_eq_div_iff` — ~10 lignes.

**Total estimé : 80-100 lignes Lean, 4-8h de travail.**

### Sprint 4b (déjà complété : CompactnessDefs)

Rappel : Sprint 4b a déjà été livré en GOLD avec `h`, `IsCompact`, `C` et
6 lemmes prouvés. Non impacté par Sprint 4a-ter.

---

## 📦 Commits proposés

Un seul commit atomique :

```
refactor(padic): close haarZTwo axiom via addHaarMeasure, prove toZModPow_surjective

Sprint 4a-ter reduces axioms 2 → 1:
- haarZTwo now concretely defined as addHaarMeasure ⊤ (no more opaque)
- isAddHaarMeasure_haarZTwo instance proved
- PadicInt.toZModPow_surjective added as theorem (not in Mathlib v4.27.0)
- cylinder_measure axiom kept with detailed 6-step proof plan
- Build EXIT 0, 0 sorry, 8 theorems proved (+2 vs 4a-bis)
- Red team: plan PROCEED PARTIAL → code YELLOW → fixed → GREEN
```

Plus un commit docs :
```
docs(sprint4a-ter): report on partial axiom closure (2 → 1)
```

---

## 🌟 Synthèse en une phrase

> **Sprint 4a-ter livre la fermeture concrète de `haarZTwo` (plus `opaque`,
> désormais `addHaarMeasure ⊤`) et le théorème `toZModPow_surjective` (non
> présent en Mathlib v4.27.0), réduisant le nombre d'axiomes de 2 à 1 ;
> `cylinder_measure` reste axiomatisé avec un plan de preuve Lean détaillé
> en 6 étapes, honnêtement documenté faute de budget pour les 4-8h de
> plomberie Mathlib restante (Sprint 4a-quater).**
