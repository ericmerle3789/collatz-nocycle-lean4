/-
Copyright (c) 2026 Eric Merle. All rights reserved.

# `ProjetCollatz/PAdic/Cylinders.lean` — Sprint 4a + 4a-bis

Cadre 2-adique pour la reformulation mesure de la piste "binary compactness"
(cf. `NOTE_2ADIC_REFRAMING_v3.md` §1.2, §1.3, §4.1).

## Contenu

* `ZTwo` : alias pour `ℤ_[2]`.
* `cylinder r` pour `r : ZMod (2^k)` : la préimage de `{r}` par `toZModPow k`.
* `haarZTwo` : mesure de Haar 2-adique (axiomatisée à ce stade ; construction
  via `MeasureTheory.Measure.addHaarMeasure` reportée à Sprint 4a-ter).
* `cylinder_measure` : μ(C_{r,k}) = 2^{-k} (axiomatisée, corollaire de
  Haar + surjectivité de `toZModPow`).
* `wellDefinedDomain L` : clause technique §1.3 — E_L = {x : toZModPow L (3x+1) ≠ 0}.
* `wellDefinedDomain_compl_eq_cylinder` : **PROUVÉ** (Sprint 4a-bis) —
  (E_L)^c = cylinder(-(3⁻¹)) via ring hom + `ZMod.mul_inv_of_unit`.
* `wellDefinedDomain_measure` : μ(E_L^c) = 2^{-L} (théorème prouvé).

## Statut après Sprint 4a-bis

**BRONZE+ / quasi-GOLD** :
- **0 sorry**.
- **2 axiomes** (réduits depuis 3 via fermeture 4a-bis) : `haarZTwo` (opaque) et
  `cylinder_measure`. Tous deux justifiés par la littérature standard Haar + p-adiques,
  construction effective reportée à Sprint 4a-ter.
- **5 théorèmes prouvés** : `cylinder_def`, `mem_cylinder_iff`, `mem_wellDefinedDomain_iff`,
  `isUnit_three_zmod_pow_two`, `wellDefinedDomain_compl_eq_cylinder`,
  `wellDefinedDomain_measure` (+ corollaire `_le`).

## Conventions

On suit la convention namespace `ProjetCollatz.*` du projet (pas `Collatz.*`
comme initialement suggéré dans la note, qui avait été rédigée avant examen
de la structure du projet).
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.MeasureTheory.Measure.MeasureSpace
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

/-! ## §2. Mesure de Haar axiomatisée

Mathlib v4.27.0 fournit `MeasureTheory.Measure.addHaarMeasure` pour tout groupe
topologique additif localement compact Hausdorff muni d'un `BorelSpace`. `ℤ_[2]`
satisfait ces conditions (compact, `NormedCommRing`, donc `TopologicalAddGroup`),
mais la chaîne d'instances n'est pas pré-assemblée. Nous axiomatisons ici la
mesure et sa valeur sur les cylindres. La construction effective via
`addHaarMeasure` sera réalisée en Sprint 4a-bis.

Les axiomes ci-dessous formalisent des faits mathématiques standards :
- unicité de la mesure de Haar normalisée sur un groupe compact
- valeur `2^{-k}` sur les cylindres par invariance translationnelle + surjectivité
  de `toZModPow`
-/

/-- Mesure de Haar 2-adique normalisée (probabilité) sur `ZTwo`.

**Axiomatisée à ce stade via `opaque`** : `Measure ZTwo` est habité (la mesure
zéro est un témoin canonique), donc `opaque` est logiquement sain — Lean sélectionne
un témoin arbitraire via `Classical.choice`. **La paire (`haarZTwo` opaque + axiome
`cylinder_measure` ci-dessous) est mathématiquement cohérente uniquement si
la mesure de Haar 2-adique existe ET satisfait `μ(C_{r,k}) = 2^{-k}`**.

Ce couple est justifié par :
- `MeasureTheory.Measure.addHaarMeasure` : existence sur tout groupe additif
  localement compact Hausdorff (`ℤ_[2]` satisfait toutes les conditions).
- `MeasureTheory.Measure.Haar.Unique` : unicité de Haar normalisée sur
  un groupe compact.
- `PadicInt.toZModPow k` surjective (à prouver explicitement Sprint 4a-bis),
  pushforward uniforme → mesure égale sur chaque cylindre de profondeur k.

Construction effective de l'instance `IsAddHaarMeasure haarZTwo` reportée
à Sprint 4a-bis. -/
noncomputable opaque haarZTwo : Measure ZTwo

/-- Axiome fondateur : la mesure d'un cylindre 2-adique de profondeur `k` est
`2^{-k}`.

**Justification mathématique** (note §1.2) : par unicité de Haar sur `ℤ_[2]` et
pushforward uniforme via `toZModPow k` surjective, `μ(C_{r,k}) = 1/|ZMod(2^k)|
= 1/2^k`. Repose sur :
- `PadicInt.toZModPow_surjective` (à prouver, non présent en Mathlib v4.27.0)
- `Measure.map haarZTwo toZModPow = uniformMeasure (ZMod (2^k))` par unicité
  de Haar sur groupes compacts finis (pushforward préserve l'invariance
  translationnelle).

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
