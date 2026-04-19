/-
Copyright (c) 2026 Eric Merle. All rights reserved.

# `ProjetCollatz/hTailBound.lean` — Sprint 4d étape 2 Option B

Bornes concrètes sur la mesure de comptage de `Δh := h(3n+1) - h n`
(soustraction tronquée ℕ), calibrées par l'étape 1 empirique
(`analysis/compactness/measure_h_tail.py`).

## Contexte empirique (documentation uniquement, pas axiome)

Étape 1 (5 × 10⁶ impairs aléatoires, bit_length ∈ [10, 50]) :
- α ≈ 0.686 stable sur 5 bit_lengths (std = 0.012, cv = 1.8%).
- `P(Δh > t) ≤ 2.24 · exp(-α · t)` avec α ∈ [0.67, 0.70].
- Comme `log(2) ≈ 0.693` est proche de α_empirique, la borne rationnelle
  `count · 100 · 2^t ≤ 224 · N` est une sur-approximation serrée (écart 1%).

Étape 1.5 (`transfer_operator_spectrum.py`) : le modèle markovien sur
`ZMod(2^k)` NE capture PAS α : `|λ₂| ≈ 0.19` vs valeur attendue `exp(-0.686) = 0.50`.
h est une propriété globale de l'orbite (cohérent Tao 2019), d'où
l'approche **mesure de comptage** plutôt qu'opérateur de transfert.

## Convention `Δh` : soustraction tronquée ℕ

`deltaH n := h (3 * n + 1) - h n` en Lean utilise la soustraction tronquée ℕ :
si `h (3n+1) < h n`, alors `deltaH n = 0`. Pour tout `t ≥ 0`, la condition
`deltaH n > t` capture exactement les cas où `h` **augmente strictement** d'au
moins `t + 1` unités après une étape `n ↦ 3n+1`. Les cas où `h` décroît
(deltaH = 0 en Lean, `h(3n+1) - h(n) < 0` en ℤ) sont automatiquement
éliminés puisque `0 > t` est faux pour `t ≥ 0`. Cette troncature est donc
**bénigne** pour l'analyse de queue droite.

## Contenu

* `deltaH n` — soustraction tronquée `h(3n+1) - h n`.
* `countDeltaHExceeds t N` — `#{ k ∈ [0, N) : deltaH (2k+1) > t }`.
* §1 : 8 théorèmes exacts `countDeltaHExceeds t N = ...` via `native_decide`
  (calibration empirique N ∈ {100, 500, 1000}, t ∈ {0, 2, 5, 10}).
* §2 : 4 théorèmes de borne exponentielle rationnelle
  `100 · 2^t · count ≤ 224 · N` via `native_decide`.
* §3 : 2 théorèmes structurels : antitonie en `t` et borne triviale `≤ N`.

## Statut Sprint 4d étape 2

**GOLD** : 14 théorèmes prouvés, 0 sorry, 0 axiome, `lake build` EXIT 0 (5.6s).
Version asymptotique générique (quantifiée sur tous N, t) laissée pour
Sprint 4e (extension vers mesure de Haar concrète).
-/

import ProjetCollatz.CompactnessDefs
import Mathlib.Data.Finset.Card

namespace ProjetCollatz.Compactness

/-! ## §0. Définitions -/

/-- `Δh n := h(3n+1) - h n` avec soustraction tronquée ℕ. -/
def deltaH (n : ℕ) : ℕ := h (3 * n + 1) - h n

/-- Nombre d'impairs `n = 2k+1` pour `k ∈ [0, N)` avec `deltaH n > t`. -/
def countDeltaHExceeds (t N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun k => t < deltaH (2 * k + 1))).card

/-! ## §1. Comptages exacts (calibration empirique via `native_decide`)

Ces théorèmes vérifient exactement les valeurs tabulées par
`analysis/compactness/calibrate_tail_bound.py`. -/

/-- Sur N=100 impairs, 37 ont un `Δh` strictement positif. -/
theorem exact_count_t0_N100 : countDeltaHExceeds 0 100 = 37 := by native_decide

/-- Sur N=100 impairs, 1 seul a `Δh > 5`. -/
theorem exact_count_t5_N100 : countDeltaHExceeds 5 100 = 1 := by native_decide

/-- Sur N=100 impairs, aucun n'a `Δh > 10`. -/
theorem exact_count_t10_N100 : countDeltaHExceeds 10 100 = 0 := by native_decide

/-- Sur N=500 impairs, 5 ont `Δh > 5`. -/
theorem exact_count_t5_N500 : countDeltaHExceeds 5 500 = 5 := by native_decide

/-- Sur N=500 impairs, aucun n'a `Δh > 10`. -/
theorem exact_count_t10_N500 : countDeltaHExceeds 10 500 = 0 := by native_decide

/-- Sur N=1000 impairs, 96 ont `Δh > 2`. -/
theorem exact_count_t2_N1000 : countDeltaHExceeds 2 1000 = 96 := by native_decide

/-- Sur N=1000 impairs, 11 ont `Δh > 5`. -/
theorem exact_count_t5_N1000 : countDeltaHExceeds 5 1000 = 11 := by native_decide

/-- Sur N=1000 impairs, aucun n'a `Δh > 10`. -/
theorem exact_count_t10_N1000 : countDeltaHExceeds 10 1000 = 0 := by native_decide

/-! ## §2. Borne exponentielle empirique (α ≈ log 2)

On vérifie la borne rationnelle `count · 100 · 2^t ≤ 224 · N`, équivalente à
`count / N ≤ 2.24 · 2^(-t)`. La constante `2.24 = 224/100` est une
sur-approximation du `sup_{bl} MGF(0.5)` mesurée en étape 1 ;
`α = log(2) ≈ 0.693` sur-approxime α_empirique ≈ 0.686 (écart 1%). -/

theorem empirical_bound_t5_N100 :
    100 * 2^5 * countDeltaHExceeds 5 100 ≤ 224 * 100 := by native_decide

theorem empirical_bound_t5_N500 :
    100 * 2^5 * countDeltaHExceeds 5 500 ≤ 224 * 500 := by native_decide

theorem empirical_bound_t10_N500 :
    100 * 2^10 * countDeltaHExceeds 10 500 ≤ 224 * 500 := by native_decide

theorem empirical_bound_t5_N1000 :
    100 * 2^5 * countDeltaHExceeds 5 1000 ≤ 224 * 1000 := by native_decide

/-! ## §3. Théorèmes structurels -/

/-- Antitonie en `t` : augmenter le seuil diminue le comptage.

`{k ∈ [0, N) : t₂ < Δh k} ⊆ {k ∈ [0, N) : t₁ < Δh k}` car `t₁ ≤ t₂ ⟹
(t₂ < x) ⟹ (t₁ < x)` (transitivité `<`). -/
theorem countDeltaHExceeds_antitone (N : ℕ) {t₁ t₂ : ℕ} (h_le : t₁ ≤ t₂) :
    countDeltaHExceeds t₂ N ≤ countDeltaHExceeds t₁ N := by
  unfold countDeltaHExceeds
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  exact ⟨hk.1, lt_of_le_of_lt h_le hk.2⟩

/-- Borne triviale : le comptage est majoré par la taille de la fenêtre. -/
theorem countDeltaHExceeds_le_N (t N : ℕ) : countDeltaHExceeds t N ≤ N := by
  unfold countDeltaHExceeds
  calc ((Finset.range N).filter (fun k => t < deltaH (2 * k + 1))).card
      ≤ (Finset.range N).card := Finset.card_filter_le _ _
    _ = N := Finset.card_range N

end ProjetCollatz.Compactness
