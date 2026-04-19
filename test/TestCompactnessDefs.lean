/-
# `test/TestCompactnessDefs.lean` — Tests Sprint 4b

Tests de cohérence pour `ProjetCollatz/CompactnessDefs.lean` :

1. Valeurs concrètes de `h` via `native_decide` (calculs effectifs).
2. Cohérence `IsCompact` avec `h`.
3. Application du lemme `double_preserves_compact`.
4. Monotonie `C k ⊆ C (k+1)`.

Les exemples correspondent aux cas canoniques mentionnés dans les rapports
Sprints 1-3 (27, 31, 41, 47, 54, 73, 267, 1025).
-/

import ProjetCollatz.CompactnessDefs

namespace ProjetCollatz.Compactness.Test

open ProjetCollatz.Compactness

/-! ## Valeurs concrètes de `h` -/

example : h 0 = 0 := by native_decide
example : h 1 = 0 := by native_decide
example : h 2 = 0 := by native_decide
example : h 3 = 0 := by native_decide
example : h 4 = 0 := by native_decide
example : h 5 = 1 := by native_decide
example : h 9 = 2 := by native_decide
example : h 17 = 3 := by native_decide
example : h 27 = 1 := by native_decide  -- 27 = 11011
example : h 73 = 2 := by native_decide  -- 73 = 1001001
example : h 267 = 4 := by native_decide -- 267 = 100001011 (bloc de 4)
example : h 1025 = 9 := by native_decide -- 1025 = 10000000001

/-! ## Cohérence `IsCompact` -/

example : IsCompact 4 27 := by
  show h 27 < 4
  native_decide

example : ¬ IsCompact 4 267 := by
  show ¬ (h 267 < 4)
  native_decide  -- h 267 = 4, donc pas < 4

/-! ## `double_preserves_compact` -/

example : IsCompact 4 54 := by
  -- 54 = 2 * 27, et 27 est 4-compact
  have h27 : IsCompact 4 27 := by show h 27 < 4; native_decide
  exact double_preserves_compact 4 27 h27

/-! ## Monotonie `C` -/

example (n : ℕ) (hn : n ∈ C 3) : n ∈ C 4 :=
  C_monotone 3 hn

end ProjetCollatz.Compactness.Test
