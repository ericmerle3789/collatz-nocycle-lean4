/-
Copyright (c) 2026 Eric Merle. All rights reserved.

# `ProjetCollatz/CompactnessDefs.lean` — Sprint 4b

Définitions de la compacité binaire (cf. `NOTE_2ADIC_REFRAMING_v3.md` §2.1, §4.2).

## Contenu

* `h : ℕ → ℕ` — longueur du plus grand bloc interne de zéros dans
  l'expansion binaire (les zéros de queue trailing ne comptent pas).
* `IsCompact k n := h n < k` — prédicat de `k`-compacité.
* `C k : Set ℕ` — ensemble des `k`-compacts.
* 3 lemmes structurels prouvés : `one_is_compact`, `double_preserves_compact`,
  `C_monotone`, + lemme auxiliaire `h_two_mul`.

## Statut Sprint 4b

**GOLD** : 0 sorry, 0 axiome, `lake build` EXIT 0.

## Conventions

Convention namespace `ProjetCollatz.*` du projet (cohérent avec
`ProjetCollatz.PAdic` du Sprint 4a).

## Algorithme de `h`

On utilise `Nat.bits n : List Bool` (LSB-first, Mathlib). Le prédicat
`dropWhile (fun b => !b)` retire les `false` initiaux, c'est-à-dire les bits
LSB nuls, ce qui correspond aux **zéros de queue trailing** dans la
représentation MSB-first. Le plus long run de `false` dans la liste
résultante est le plus grand bloc interne.

Référence sémantique Python : `bin(n)[2:].rstrip("0")` puis scan du plus
long run de `'0'`.
-/

import Mathlib.Data.Nat.Bits
-- Note : `List.dropWhile_cons_of_pos` vient du core Lean 4
-- (`Init.Data.List.TakeDrop`), pas besoin d'import Mathlib supplémentaire.

namespace ProjetCollatz.Compactness

/-! ## §1. Fonction `h` et ses définitions dérivées -/

/-- Plus long run consécutif de `false` dans une liste (scan left-to-right).
`acc` est le run courant, `best` le meilleur trouvé ; on retourne
`max acc best` à la fin de la liste pour capter un éventuel run de queue. -/
private def maxFalseRunAux : ℕ → ℕ → List Bool → ℕ
  | acc, best, [] => max acc best
  | acc, best, true :: rest => maxFalseRunAux 0 (max acc best) rest
  | acc, best, false :: rest => maxFalseRunAux (acc + 1) best rest

/-- Longueur du plus long run consécutif de `false` dans la liste. -/
def _root_.List.maxFalseRun : List Bool → ℕ := maxFalseRunAux 0 0

/-- `h n` = longueur du plus grand bloc interne de zéros dans l'expansion
binaire de `n` (MSB-first). Les zéros de queue (trailing zeros) ne comptent pas.

`h 0 = 0` par convention (liste de bits vide).
`h 1 = 0` (un seul bit 1, aucun bloc interne).
`h 9 = 2` car 9 = 1001₂ avec bloc interne de 2 zéros.
`h 17 = 3` car 17 = 10001₂ avec bloc interne de 3 zéros.
`h 73 = 2` car 73 = 1001001₂ avec blocs internes de 2 zéros. -/
def h (n : ℕ) : ℕ :=
  List.maxFalseRun ((Nat.bits n).dropWhile (fun b => !b))

/-- `n` est `k`-compact ssi son plus grand bloc interne de zéros est `< k`. -/
def IsCompact (k n : ℕ) : Prop := h n < k

/-- Ensemble des entiers `k`-compacts. -/
def C (k : ℕ) : Set ℕ := { n | IsCompact k n }

/-! ## §2. Lemmes structurels -/

/-- Cas de base : `h 0 = 0`. -/
@[simp]
theorem h_zero : h 0 = 0 := by
  unfold h
  rw [Nat.zero_bits]
  rfl

/-- Cas de base : `h 1 = 0`. -/
@[simp]
theorem h_one : h 1 = 0 := by
  unfold h
  rw [Nat.one_bits]
  rfl

/-- `1` est `k`-compact pour tout `k ≥ 1`. -/
theorem one_is_compact {k : ℕ} (hk : 1 ≤ k) : IsCompact k 1 := by
  simp [IsCompact, h_one]
  omega

/-- **Lemme clé** : `h` est invariante par doublement.
Doubler `n` ajoute un zéro LSB (= zéro trailing en MSB), qui est retiré par
`dropWhile`. Donc `h (2 * n) = h n`. -/
@[simp]
theorem h_two_mul (n : ℕ) : h (2 * n) = h n := by
  by_cases hn : n = 0
  · subst hn; simp [h]
  · unfold h
    rw [Nat.bit0_bits n hn]
    simp [List.dropWhile_cons_of_pos]

/-- Le doublement préserve la compacité. -/
theorem double_preserves_compact (k n : ℕ) (hn : IsCompact k n) :
    IsCompact k (2 * n) := by
  simp [IsCompact, h_two_mul]
  exact hn

/-- Monotonie : `C k ⊆ C (k+1)`. -/
theorem C_monotone (k : ℕ) : C k ⊆ C (k + 1) := by
  intro n hn
  show h n < k + 1
  have hk : h n < k := hn
  omega

end ProjetCollatz.Compactness
