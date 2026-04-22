/-
# legendre_spike/test_cf_convergents.lean
# M2.2b POC : test native_decide performance on arithmetic facts analogous
# to CF-convergent proof obligations for log_2 3.
#
# This file is a scratch experiment, NOT imported by ProjetCollatz.
# Safe to evaluate, discard, or break.
#
# The convergents q_i of log_2 3 (integer denominators of CF) are :
#   q_0 = 1, q_1 = 1, q_2 = 2, q_3 = 12, q_4 = 53, q_5 = 306,
#   q_6 = 665, q_7 = 15601, q_8 = 16266, q_9 = 176851, ...
#   (known table, see Phase59ContinuedFractions docstrings)
#
# The Phase59 lemmas verify arithmetic gaps like `2^{1055} > 3^{665} / C` for
# constants C extracted from the CF theory.
-/

-- Baseline : trivial arithmetic
example : 2^10 > 1000 := by native_decide
example : 2^20 > 1000000 := by native_decide
-- Bigger integer compare (typical of cf_gap_* lemmas)
-- This matches the scale of Phase59 ProjetCollatz.cf_gap_8 :
-- `2 * (2 : ℕ) ^ 1055 ≥ 3 * (3 : ℕ) ^ 665`
-- which is already proven in the repo by native_decide.
example : 2 * (2 : Nat) ^ 200 > 3 * (3 : Nat) ^ 125 := by native_decide

-- Scale test : 2^1000 range (uses exponentiation.threshold-like territory)
set_option exponentiation.threshold 2000 in
example : (2 : Nat) ^ 1000 > (3 : Nat) ^ 500 := by native_decide
