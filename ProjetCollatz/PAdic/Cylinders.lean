/-
Copyright (c) 2026 Eric Merle. All rights reserved.

# `ProjetCollatz/PAdic/Cylinders.lean` — Sprint 4a + 4a-bis

Cadre 2-adique pour la reformulation mesure de la piste "binary compactness"
(cf. `NOTE_2ADIC_REFRAMING_v3.md` §1.2, §1.3, §4.1).

## Contenu

* `ZTwo` : alias pour `ℤ_[2]`.
* `cylinder r` pour `r : ZMod (2^k)` : la préimage de `{r}` par `toZModPow k`.
* `haarZTwo` : mesure de Haar 2-adique construite via
  `MeasureTheory.Measure.addHaarMeasure ⊤` (Sprint 4a-ter, plus axiomatisée).
* `cylinder_measure` : μ(C_{r,k}) = 2^{-k} (axiome résiduel avec plan de
  preuve détaillé, Sprint 4a-quater visé).
* `wellDefinedDomain L` : clause technique §1.3 — E_L = {x : toZModPow L (3x+1) ≠ 0}.
* `wellDefinedDomain_compl_eq_cylinder` : **PROUVÉ** (Sprint 4a-bis) —
  (E_L)^c = cylinder(-(3⁻¹)) via ring hom + `ZMod.mul_inv_of_unit`.
* `wellDefinedDomain_measure` : μ(E_L^c) = 2^{-L} (théorème prouvé).

## Statut après Sprint 4a-ter

**Quasi-GOLD** :
- **0 sorry**.
- **1 axiome** (réduit de 2 → 1 via Phase A+B du Sprint 4a-ter) :
  `cylinder_measure`. Plan de preuve détaillé inline, Sprint 4a-quater visé.
- **8 théorèmes prouvés** (incluant 1 corollaire) :
  - `cylinder_def`, `mem_cylinder_iff` (§1)
  - `PadicInt.toZModPow_surjective` (§3, nouveau Sprint 4a-ter)
  - `mem_wellDefinedDomain_iff`, `isUnit_three_zmod_pow_two` (§3)
  - `wellDefinedDomain_compl_eq_cylinder` (§3, Sprint 4a-bis)
  - `wellDefinedDomain_measure` + corollaire `_le` (§3)
- **`haarZTwo` est maintenant construit explicitement** via `addHaarMeasure ⊤`
  (plus `opaque`). Instance `IsAddHaarMeasure` prouvée (pas axiomatisée).

Progression : 4a BRONZE (3 axiomes) → 4a-bis BRONZE+ (2 axiomes) → 4a-ter
quasi-GOLD (1 axiome avec plan de preuve).

## Conventions

On suit la convention namespace `ProjetCollatz.*` du projet (pas `Collatz.*`
comme initialement suggéré dans la note, qui avait été rédigée avant examen
de la structure du projet).
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ENNReal.Basic

namespace ProjetCollatz.PAdic

open MeasureTheory ENNReal

/-! ## §1. Entiers 2-adiques et cylindres -/

/-- Instance globale `Fact (Nat.Prime 2)` requise par `ℤ_[p]` paramétré.
Note : Mathlib v4.27.0 ne fournit pas d'instance globale `Fact (Nat.Prime 2)`,
et préfère le pattern local `haveI`. Cette instance est visible à tout fichier
qui importe `Cylinders.lean` ; comme elle est paramétrée par `p = 2`, elle
n'entre pas en conflit avec d'autres instances `Fact (Nat.Prime p)` pour
`p ≠ 2`. Non-bloquant pour Sprint 4a. -/
instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Entiers 2-adiques : `ℤ_[2]`. Alias pour lisibilité. -/
abbrev ZTwo : Type := ℤ_[2]

/-- Instance canonique de `MeasurableSpace` sur `ZTwo` via la topologie Borel.
`ℤ_[2]` est un `MetricSpace` (donc `TopologicalSpace` Hausdorff), donc admet
sa tribu borélienne. Note : Mathlib v4.27.0 ne fournit pas d'instance
canonique `MeasurableSpace ℤ_[p]` — nous la déclarons ici sans risque de
conflit d'instance actuel. -/
noncomputable instance : MeasurableSpace ZTwo := borel ZTwo

/-- `BorelSpace` : la tribu mesurable déclarée coïncide avec la tribu borélienne.
Trivial par `rfl` puisque l'instance précédente est `borel ZTwo`. -/
instance : BorelSpace ZTwo := ⟨rfl⟩

/-- Cylindre 2-adique de profondeur `k` centré sur `r`.

`cylinder r = {x ∈ ℤ_[2] : x ≡ r mod 2^k}` vu comme préimage de `{r}` par
`PadicInt.toZModPow k : ℤ_[2] →+* ZMod (2^k)`.

Correspond à `C_{r,k}` dans la note §1.2. -/
def cylinder {k : ℕ} (r : ZMod (2^k)) : Set ZTwo :=
  (PadicInt.toZModPow k) ⁻¹' {r}

@[simp]
theorem cylinder_def {k : ℕ} (r : ZMod (2^k)) :
    cylinder r = (PadicInt.toZModPow k) ⁻¹' {r} := rfl

@[simp]
theorem mem_cylinder_iff {k : ℕ} (r : ZMod (2^k)) (x : ZTwo) :
    x ∈ cylinder r ↔ PadicInt.toZModPow k x = r := Iff.rfl

/-! ## §2. Mesure de Haar (construction + axiome résiduel)

Mathlib v4.27.0 fournit `MeasureTheory.Measure.addHaarMeasure` pour tout groupe
topologique additif localement compact Hausdorff muni d'un `BorelSpace`. `ℤ_[2]`
satisfait toutes ces conditions (compact via `PadicInt.compactSpace`,
`NormedCommRing` → `IsTopologicalAddGroup`, `MetricSpace` Hausdorff, Borel
déclaré §1).

**Sprint 4a-ter** : `haarZTwo` est désormais **construite explicitement** via
`addHaarMeasure ⊤` (plus d'axiome `opaque`). Seul l'axiome `cylinder_measure`
reste, avec un plan de preuve détaillé (voir docstring de l'axiome). Fermeture
complète reportée à Sprint 4a-quater (estimé 4-8 h Lean).
-/

/-- Mesure de Haar 2-adique normalisée (probabilité) sur `ZTwo`.

**Construction Sprint 4a-ter** : `addHaarMeasure ⊤` appliquée au compact canonique
`⊤ : PositiveCompacts ZTwo` (qui existe car `ZTwo` est `CompactSpace` et `Nonempty`).

Par construction :
- `haarZTwo = addHaarMeasure ⊤` via `MeasureTheory.Measure.addHaarMeasure`
- `haarZTwo` satisfait `IsAddHaarMeasure` (invariance par translation additive)
- `haarZTwo univ = 1` (probabilité, via `haarMeasure_self` avec `↑⊤ = univ`)

Référence : note §1.2 « L'anneau topologique `ℤ_2` admet une unique mesure de
probabilité invariante par translation, la mesure de Haar ν ». -/
noncomputable def haarZTwo : Measure ZTwo :=
  MeasureTheory.Measure.addHaarMeasure ⊤

/-- `haarZTwo` est une mesure de Haar additive (invariance par translation). -/
instance isAddHaarMeasure_haarZTwo : haarZTwo.IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure ⊤

/-! ### Lemme auxiliaire : surjectivité de `toZModPow`

`toZModPow k : ℤ_[p] →+* ZMod (p^k)` est surjective : pour tout `y : ZMod (p^k)`,
on a `toZModPow k (y.val : ℤ_[p]) = y` via la préservation des casts naturels
et `ZMod.natCast_zmod_val`.

Ce lemme n'existe pas en Mathlib v4.27.0 ; contribution possible à Mathlib. -/
theorem _root_.PadicInt.toZModPow_surjective {p : ℕ} [hp : Fact p.Prime] (k : ℕ) :
    Function.Surjective (PadicInt.toZModPow k : ℤ_[p] →+* ZMod (p^k)) := by
  intro y
  refine ⟨((y.val : ℕ) : ℤ_[p]), ?_⟩
  rw [map_natCast]
  haveI : NeZero (p^k) := ⟨pow_ne_zero k hp.out.pos.ne'⟩
  exact ZMod.natCast_zmod_val y

/-- **Axiome résiduel Sprint 4a-ter** : `μ(C_{r,k}) = 2^{-k}`.

**Statut** : Sprint 4a-ter a réduit 2 axiomes (4a) à 1 axiome (4a-ter) :
- `haarZTwo` : désormais construite explicitement via `addHaarMeasure ⊤` (§2).
- `cylinder_measure` : **axiome résiduel**, plan de preuve détaillé ci-dessous.

**Plan de preuve complet** (Sprint 4a-quater futur, estimé 4-8h de Lean) :

1. **Disjonction** : `Pairwise (Disjoint on (cylinder : ZMod (2^k) → Set ZTwo))`
   via préimages de singletons distincts par un ring hom.

2. **Partition** : `⋃ r : ZMod (2^k), cylinder r = Set.univ`
   via `PadicInt.toZModPow_surjective` (prouvé §3 ci-dessus).

3. **Translation** : pour tout `r`, `cylinder r = (· + (-r.val)) ⁻¹' (cylinder 0)`
   (requiert la gymnastique `ZMod.natCast_zmod_val` + `sub_eq_zero`, sur laquelle
   la tentative Sprint 4a-ter a buté — `linarith`/`linear_combination` ne ferment
   pas sur `ZMod` pour l'équivalence `toZModPow x = r ↔ toZModPow x - r = 0`).

4. **Même mesure** : `haarZTwo (cylinder r) = haarZTwo (cylinder 0)` via
   `measure_preimage_add haarZTwo _ _` (disponible Mathlib car
   `isAddHaarMeasure_haarZTwo` + `IsAddLeftInvariant`).

5. **Somme = 1** : `∑ s, haarZTwo (cylinder s) = haarZTwo univ = 1`
   via `measure_iUnion` (disjonction) et `measure_univ` (probabilité).
   **Obstacle** : `cylinder` est mesurable via la continuité de `toZModPow`,
   mais `PadicInt.continuous_toZModPow` n'existe pas explicitement en Mathlib
   v4.27.0 — à prouver (clopen-ness via `mem_span_pow_iff_le_valuation`).

6. **Conclusion** : `(2^k) * haarZTwo (cylinder 0) = 1` → `haarZTwo (cylinder 0) = 1/2^k`
   via `ENNReal.div_eq_div_iff` + `Fintype.card (ZMod (2^k)) = 2^k`.

**Cohérence logique** : cet axiome est désormais une **propriété calculable**
de l'objet concret `haarZTwo = addHaarMeasure ⊤` (pas d'un opaque). Un reviewer
peut vérifier informellement que c'est vrai ; un vérificateur Lean ne peut
pas encore le prouver sans les ~100 lignes de plomberie ci-dessus.

Référence : note §1.2 ligne 35 : ν(C_{r,k}) = 2^{-k}. -/
axiom cylinder_measure {k : ℕ} (r : ZMod (2^k)) :
    haarZTwo (cylinder r) = ((1 : ENNReal) / 2) ^ k

/-! ## §3. Domaine de bonne définition (clause technique §1.3)

L'action de `T(x) = (3x+1)/2^{v_2(3x+1)}` descend bien au quotient
`ℤ_[2] / 2^L·ℤ_[2] ≅ ZMod(2^L)` uniquement sur le sous-ensemble où
`v_2(3x+1) < L`. Le complémentaire, `{x : 2^L ∣ 3x+1}`, est un unique
cylindre de mesure `2^{-L}`.

**Note (correction post red-team H2)** : Mathlib convention `valuation 0 = 0`
rendrait `x₀ = -1/3 ∈ ℤ_[2]` (où `3x+1 = 0`) faussement membre de `E_L` pour
tout `L ≥ 1`. Nous définissons `E_L` directement via `toZModPow L (3x+1) ≠ 0`,
qui est équivalent à la définition mathématique (car `0 ∈ ker(toZModPow L)`
exclut automatiquement `x₀`) et évite l'ambiguïté.
-/

/-- Domaine où `T` est bien définie au quotient modulo `2^L` :
`E_L := {x ∈ ℤ_[2] : toZModPow L (3x+1) ≠ 0}`.

Équivalent à `{x : v_2(3x+1) < L}` avec la convention p-adique standard
`v_2(0) = +∞` (sous laquelle `3x+1 = 0` implique `v_2 ≥ L` pour tout `L`,
donc `x ∉ E_L`). On utilise la formulation `toZModPow ≠ 0` directement pour
contourner la convention Mathlib `PadicInt.valuation 0 = 0` qui n'est pas
l'infini mathématique standard. -/
def wellDefinedDomain (L : ℕ) : Set ZTwo :=
  { x : ZTwo | PadicInt.toZModPow L (3 * x + 1) ≠ 0 }

@[simp]
theorem mem_wellDefinedDomain_iff (L : ℕ) (x : ZTwo) :
    x ∈ wellDefinedDomain L ↔ PadicInt.toZModPow L (3 * x + 1) ≠ 0 := Iff.rfl

/-- Lemme auxiliaire : `3` est inversible dans `ZMod (2^L)` car `gcd(3, 2^L) = 1`.
Prouvé via `ZMod.isUnit_prime_iff_not_dvd` appliqué à p=3 (premier) et 2^L. -/
theorem isUnit_three_zmod_pow_two (L : ℕ) : IsUnit (3 : ZMod (2^L)) := by
  rw [show (3 : ZMod (2^L)) = ((3 : ℕ) : ZMod (2^L)) by norm_cast]
  exact (ZMod.isUnit_prime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
    (fun h => absurd (Nat.Prime.dvd_of_dvd_pow (by decide) h) (by decide))

/-- **Lemme structurel** : le complémentaire de `E_L` est EXACTEMENT le cylindre
de profondeur `L` centré en `-(3⁻¹) mod 2^L`, où `3⁻¹` est l'inverse de 3 dans
`ZMod(2^L)` (existe car `gcd(3, 2^L) = 1`).

Preuve :
  `x ∉ E_L  ⟺ toZModPow L (3x+1) = 0        (def)
           ⟺ 3 · toZModPow L x + 1 = 0     (ring hom)
           ⟺ toZModPow L x = -3⁻¹          (3 inversible)
           ⟺ x ∈ cylinder (-3⁻¹)           (def cylinder)`

Utilise `linear_combination` avec l'identité `3 · 3⁻¹ = 1`
(fournie par `ZMod.mul_inv_of_unit`) pour contourner l'absence de
`field_simp`/`linarith` sur `ZMod (2^L)`. -/
theorem wellDefinedDomain_compl_eq_cylinder (L : ℕ) :
    (wellDefinedDomain L)ᶜ = cylinder (-((3 : ZMod (2^L))⁻¹)) := by
  ext x
  simp only [Set.mem_compl_iff, mem_wellDefinedDomain_iff, not_not,
             cylinder, Set.mem_preimage, Set.mem_singleton_iff]
  -- Réduction via ring hom.
  have ring_step : PadicInt.toZModPow L (3 * x + 1) =
      3 * PadicInt.toZModPow L x + 1 := by
    simp [map_add, map_mul, map_one, map_ofNat]
  rw [ring_step]
  set y : ZMod (2^L) := PadicInt.toZModPow L x with y_def
  have h3 := isUnit_three_zmod_pow_two L
  -- Clé : 3 · 3⁻¹ = 1 (car 3 est une unité dans ZMod(2^L))
  have key : (3 : ZMod (2^L)) * (3 : ZMod (2^L))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ h3
  constructor
  · intro h
    -- h : 3*y + 1 = 0, goal : y = -3⁻¹
    linear_combination (3 : ZMod (2^L))⁻¹ * h - y * key
  · intro h
    -- h : y = -3⁻¹, goal : 3*y + 1 = 0
    linear_combination 3 * h - key

/-- **Théorème §1.3** : `μ((E_L)^c) = 2^{-L}` (égalité via
`wellDefinedDomain_compl_eq_cylinder` + `cylinder_measure`).

Corollaire de la note v3 §1.3 : `ν(E_L^c) ≤ 2^{-L}` avec égalité. -/
theorem wellDefinedDomain_measure (L : ℕ) :
    haarZTwo (wellDefinedDomain L)ᶜ = ((1 : ENNReal) / 2) ^ L := by
  rw [wellDefinedDomain_compl_eq_cylinder L, cylinder_measure]

/-- Corollaire direct : `μ((E_L)^c) ≤ 2^{-L}` (forme faible de la note §1.3). -/
theorem wellDefinedDomain_measure_le (L : ℕ) :
    haarZTwo (wellDefinedDomain L)ᶜ ≤ ((1 : ENNReal) / 2) ^ L :=
  le_of_eq (wellDefinedDomain_measure L)

end ProjetCollatz.PAdic
