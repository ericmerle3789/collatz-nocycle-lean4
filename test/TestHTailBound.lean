/-
# `test/TestHTailBound.lean` — Tests Sprint 4d étape 2 Option B

Tests de cohérence pour `ProjetCollatz/hTailBound.lean` :
1. Valeurs concrètes de `deltaH` (incluant le cas adversarial du Sprint 4d prep).
2. Applications des théorèmes exacts `exact_count_*`.
3. Vérification des bornes empiriques `empirical_bound_*`.
4. Applications de l'antitonie en `t`.
5. Borne triviale `≤ N`.
-/

import ProjetCollatz.hTailBound

namespace ProjetCollatz.Compactness.Test

open ProjetCollatz.Compactness

/-! ## §1. `deltaH` sur valeurs concrètes -/

-- n = 1 : h(1) = 0, h(4) = 0, deltaH = 0
example : deltaH 1 = 0 := by native_decide

-- n = 3 : h(3) = 0, h(10) = 1, deltaH = 1
example : deltaH 3 = 1 := by native_decide

-- n = 5 : h(5) = 1, h(16) = 0, deltaH = max(0-1, 0) = 0 (troncature bénigne)
example : deltaH 5 = 0 := by native_decide

-- n = 683 : cas adversarial du Sprint 4d préparatoire (n = (2^11 + 1)/3).
-- h(683) = 1 (pattern alternant 1010101011₂), h(2050) = 9 (1000000000010₂).
-- deltaH = 9 - 1 = 8, proche du max théorique bit_length(683) - 2 = 8.
example : deltaH 683 = 8 := by native_decide

-- n = 9 : h(9) = 2, h(28) = 0 (bin 11100 → rstrip 111), deltaH = 0 (tronqué)
example : deltaH 9 = 0 := by native_decide

/-! ## §2. Applications des comptages exacts -/

example : countDeltaHExceeds 0 100 = 37 := exact_count_t0_N100

example : countDeltaHExceeds 5 100 = 1 := exact_count_t5_N100

example : countDeltaHExceeds 5 1000 = 11 := exact_count_t5_N1000

example : countDeltaHExceeds 10 1000 = 0 := exact_count_t10_N1000

/-! ## §3. Comptage nouveau calibrage (pour test `native_decide` direct) -/

-- N=10, t=0 : 4 impairs ont deltaH > 0 (à savoir n=3, 7, 11, 15 ; cf. calibrage Python)
example : countDeltaHExceeds 0 10 = 4 := by native_decide

/-! ## §4. Bornes empiriques (α ≈ log 2, C ≈ 2.24) -/

example : 100 * 2^5 * countDeltaHExceeds 5 100 ≤ 224 * 100 :=
  empirical_bound_t5_N100

example : 100 * 2^5 * countDeltaHExceeds 5 500 ≤ 224 * 500 :=
  empirical_bound_t5_N500

example : 100 * 2^5 * countDeltaHExceeds 5 1000 ≤ 224 * 1000 :=
  empirical_bound_t5_N1000

example : 100 * 2^10 * countDeltaHExceeds 10 500 ≤ 224 * 500 :=
  empirical_bound_t10_N500

/-! ## §5. Applications de l'antitonie en `t` -/

example (N : ℕ) : countDeltaHExceeds 10 N ≤ countDeltaHExceeds 5 N :=
  countDeltaHExceeds_antitone N (by omega)

example : countDeltaHExceeds 10 100 ≤ countDeltaHExceeds 0 100 :=
  countDeltaHExceeds_antitone 100 (by omega)

/-! ## §6. Borne triviale `≤ N` -/

example : countDeltaHExceeds 5 1000 ≤ 1000 := countDeltaHExceeds_le_N 5 1000

example (t : ℕ) : countDeltaHExceeds t 100 ≤ 100 := countDeltaHExceeds_le_N t 100

end ProjetCollatz.Compactness.Test
