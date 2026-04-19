/-
# `test/TestCompactnessSyracuseLink.lean` — Tests Sprint 4c

Tests de cohérence numérique pour `ProjetCollatz/CompactnessSyracuseLink.lean`.
Vérifient `native_decide` sur les 4 théorèmes + quelques valeurs canoniques.
-/

import ProjetCollatz.CompactnessSyracuseLink

namespace ProjetCollatz.Compactness.Test

open ProjetCollatz ProjetCollatz.Compactness

/-! ## Test 1 : `h_mul_pow2` — invariance par multiplication par 2^k -/

example : h (12 * 4) = h 12 := h_mul_pow2 12 2
example : h (5 * 8) = h 5 := h_mul_pow2 5 3
example : h 80 = h 5 := h_mul_pow2 5 4  -- 80 = 5 * 16

example : h 48 = 0 := by native_decide  -- 48 = 110000₂, trailing zéros
example : h (3 * 16) = h 3 := h_mul_pow2 3 4

/-! ## Test 2 : `h_div_pow2_v2Nat` — invariance par division par partie paire -/

-- Pour 72 = 9 * 8, v2Nat(72) = 3, 72/8 = 9.
-- h(72) = h(9) = 2
example : h 72 = h (72 / 2^(v2Nat 72)) := h_div_pow2_v2Nat 72

/-! ## Test 3 : `IsCompact_mul_pow2` — compacité invariante -/

example : IsCompact 4 (27 * 8) ↔ IsCompact 4 27 := IsCompact_mul_pow2 4 3 27

example : IsCompact 4 (27 * 2^4) := by
  rw [IsCompact_mul_pow2]
  show h 27 < 4
  native_decide

/-! ## Test 4 : `h_syracuseNext` — bridge Syracuse

Vérifications :
- syracuseNext 3 = (3*3+1)/2 = 5.  h 5 = 1.  h 10 = 1. ✓
- syracuseNext 5 = (3*5+1)/16 = 1. h 1 = 0.  h 16 = 0. ✓
- syracuseNext 7 = (3*7+1)/2 = 11. h 11 = 1. h 22 = 1. ✓
- syracuseNext 9 = (3*9+1)/4 = 7.  h 7 = 0.  h 28 = 0. ✓
-/

example : h (syracuseNext 3) = h 10 := h_syracuseNext 3
example : h (syracuseNext 5) = h 16 := h_syracuseNext 5
example : h (syracuseNext 7) = h 22 := h_syracuseNext 7
example : h (syracuseNext 9) = h 28 := h_syracuseNext 9

/-! ## Test 5 : `IsCompact_syracuseNext_iff` -/

example (k n : ℕ) :
    IsCompact k (syracuseNext n) ↔ IsCompact k (3 * n + 1) :=
  IsCompact_syracuseNext_iff k n

end ProjetCollatz.Compactness.Test
