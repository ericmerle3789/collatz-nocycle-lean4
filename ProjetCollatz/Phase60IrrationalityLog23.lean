import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Phase 60 — Irrationality of log₂ 3 (Voie B: padicValNat)

## Context

This file proves `Irrational (Real.logb 2 3)`, the foundational analytic
lemma for the Legendre-based approach to the Collatz no-nontrivial-cycle
theorem. In the architecture of Phase 59 (M2), the bound on large values
of `k` was encoded as the structure parameter `DerivedLargeKBound` because
continued-fraction best-approximation was not yet formalised. Phase 60
starts the M3 replacement of that hypothesis by a self-contained proof
built on Mathlib's p-adic valuation theory.

## Voie A exhaustion

An exhaustive Mathlib v4.27.0 lookup across 8 patterns for any existing
theorem of the form `Irrational (Real.logb 2 3)` or equivalents returned
zero matches (see auditor mailbox `0038-voie-a-findings.md`). Voie B
(ab-initio proof) is therefore required.

## Strategy (Voie B: 2-adic valuation)

Assume `Real.logb 2 3 = q` for some `q : ℚ`. Since `logb 2 3 > 0` we
have `q > 0`, hence `q = p / d` with `p, d : ℕ` and `p, d ≥ 1`. From the
definitional identity `Real.logb 2 3 = Real.log 3 / Real.log 2` (which
holds by `rfl` on the Mathlib definition) we cross-multiply to obtain
`d * Real.log 3 = p * Real.log 2`, i.e. `Real.log (3 ^ d) = Real.log (2 ^ p)`.
Injectivity of `Real.log` on `(0, ∞)` transports this to `3 ^ d = 2 ^ p`
in ℝ, and `Nat.cast` injectivity transports it further to `3 ^ d = 2 ^ p`
in ℕ. The auxiliary lemma `two_pow_ne_three_pow` rules this out via the
2-adic valuation:

```
padicValNat 2 (2 ^ p) = p          (since 2 is prime)
padicValNat 2 (3 ^ d) = 0          (since 2 does not divide 3)
```

Hence `p = 0`, contradicting `p ≥ 1`. ∎

## Invariants

- Zero `axiom` (no new axioms; kernel three suffice).
- Zero `sorry`.
- No `native_decide` (all arithmetic is symbolic).
- No French docstring (MISSION_NASA §10 compliance).
-/

namespace ProjetCollatz.Phase60

open Real

/-- Auxiliary lemma: for `p : ℕ` with `0 < p` and any `d : ℕ`, `2 ^ p ≠ 3 ^ d`.

    The proof uses the 2-adic valuation `padicValNat 2`. We have
    `padicValNat 2 (2 ^ p) = p` because 2 is prime, and
    `padicValNat 2 (3 ^ d) = 0` because 2 does not divide `3 ^ d`
    (which follows from `Nat.Prime.dvd_of_dvd_pow` applied to the prime
    `2` and the fact that 2 does not divide 3). -/
theorem two_pow_ne_three_pow {p d : ℕ} (hp : 0 < p) :
    (2 : ℕ) ^ p ≠ (3 : ℕ) ^ d := by
  intro heq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- padicValNat 2 on the LHS: 2 is prime, so padicValNat 2 (2^p) = p.
  have h_lhs : padicValNat 2 ((2 : ℕ) ^ p) = p := padicValNat.prime_pow p
  -- 2 does not divide 3^d, because 2 prime and 2 ∤ 3.
  have h_not_dvd : ¬ (2 : ℕ) ∣ (3 : ℕ) ^ d := by
    intro h
    have h2dvd3 : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  -- padicValNat 2 on the RHS: = 0 since 2 ∤ 3^d.
  have h_rhs : padicValNat 2 ((3 : ℕ) ^ d) = 0 :=
    padicValNat.eq_zero_of_not_dvd h_not_dvd
  -- Substitute heq into h_lhs and compare with h_rhs.
  rw [heq] at h_lhs
  omega

/-- Main theorem: `Real.logb 2 3` is irrational.

    The proof is by contradiction. Assume `Real.logb 2 3 = (q : ℝ)` for
    some `q : ℚ`. Since `logb 2 3 > 0` we deduce `q > 0`, write
    `q = p / d` with `p = q.num.toNat ≥ 1` and `d = q.den ≥ 1`, and use
    the definitional identity `Real.logb 2 3 = Real.log 3 / Real.log 2`
    to obtain `d * Real.log 3 = p * Real.log 2` (cross-multiplication).
    Applying `Real.log_pow` on both sides yields
    `Real.log ((3 : ℝ) ^ d) = Real.log ((2 : ℝ) ^ p)`, and injectivity
    of `Real.log` on `(0, ∞)` gives `(3 : ℝ) ^ d = (2 : ℝ) ^ p`. Casting
    through `ℕ ↪ ℝ` transfers this to `(3 : ℕ) ^ d = (2 : ℕ) ^ p`, which
    is ruled out by `two_pow_ne_three_pow` since `p ≥ 1`. -/
theorem log23_irrational : Irrational (Real.logb 2 3) := by
  rintro ⟨q, hq⟩
  -- hq : (q : ℝ) = Real.logb 2 3
  -- Positivity of log 2, log 3, logb 2 3.
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h_logb_pos : 0 < Real.logb 2 3 :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 3)
  -- q is a positive rational (since its cast equals a positive real).
  have h_qR_pos : 0 < (q : ℝ) := hq ▸ h_logb_pos
  have h_q_pos : 0 < q := by exact_mod_cast h_qR_pos
  -- Set p = q.num.toNat, d = q.den.
  set p : ℕ := q.num.toNat with hp_def
  set d : ℕ := q.den with hd_def
  -- Basic positivity facts for p and d.
  have h_num_pos : 0 < q.num := Rat.num_pos.mpr h_q_pos
  have h_num_nonneg : 0 ≤ q.num := h_num_pos.le
  have h_d_pos : 0 < d := q.pos
  have h_p_eq_num : (p : ℤ) = q.num := Int.toNat_of_nonneg h_num_nonneg
  have h_p_pos : 0 < p := by
    have : (0 : ℤ) < (p : ℤ) := h_p_eq_num.symm ▸ h_num_pos
    exact_mod_cast this
  -- Cast q to ℝ as p/d.
  have h_qR_eq : (q : ℝ) = (p : ℝ) / (d : ℝ) := by
    have hp_cast : (q.num : ℝ) = (p : ℝ) := by exact_mod_cast h_p_eq_num.symm
    have hd_cast : (q.den : ℝ) = (d : ℝ) := rfl
    rw [Rat.cast_def q, hp_cast, hd_cast]
  -- logb 2 3 equals log 3 / log 2 via the explicit Mathlib lemma.
  -- We prefer `Real.log_div_log.symm` over `rfl` so the proof survives any
  -- future `irreducible` marking of `Real.logb` in Mathlib (robustness).
  have h_logb_unfold : Real.logb 2 3 = Real.log 3 / Real.log 2 := Real.log_div_log.symm
  -- Cross-multiply: p * log 2 = d * log 3.
  have h_d_real_ne : (d : ℝ) ≠ 0 := by exact_mod_cast h_d_pos.ne'
  have h_log2_ne : Real.log 2 ≠ 0 := h_log2_pos.ne'
  have h_eq_ratio : Real.log 3 / Real.log 2 = (p : ℝ) / (d : ℝ) := by
    rw [← h_logb_unfold, ← hq, h_qR_eq]
  have h_cross : (d : ℝ) * Real.log 3 = (p : ℝ) * Real.log 2 := by
    have := h_eq_ratio
    field_simp at this
    linarith
  -- log of (3^d) equals log of (2^p) in ℝ.
  have h_log_pow_eq : Real.log ((3 : ℝ) ^ d) = Real.log ((2 : ℝ) ^ p) := by
    rw [Real.log_pow, Real.log_pow]
    linarith
  -- Injectivity of log on (0, ∞).
  have h_3d_pos : (0 : ℝ) < (3 : ℝ) ^ d := pow_pos (by norm_num) d
  have h_2p_pos : (0 : ℝ) < (2 : ℝ) ^ p := pow_pos (by norm_num) p
  have h_pow_eq_real : (3 : ℝ) ^ d = (2 : ℝ) ^ p :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr h_3d_pos) (Set.mem_Ioi.mpr h_2p_pos) h_log_pow_eq
  -- Transfer the equality from ℝ to ℕ.
  have h_pow_eq_nat : (3 : ℕ) ^ d = (2 : ℕ) ^ p := by
    have h_cast : ((3 ^ d : ℕ) : ℝ) = ((2 ^ p : ℕ) : ℝ) := by
      push_cast
      exact h_pow_eq_real
    exact_mod_cast h_cast
  -- Apply the auxiliary lemma: 0 < p and 2^p = 3^d contradict.
  exact two_pow_ne_three_pow h_p_pos h_pow_eq_nat.symm

end ProjetCollatz.Phase60
