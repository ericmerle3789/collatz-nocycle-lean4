import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.DiophantineApproximation.Basic

-- Note: `ProjetCollatz.Phase60IrrationalityLog23` is deliberately NOT imported
-- here. The theorems of Phase61 — including the Legendre second-kind
-- contrapositive `not_convergent_implies_far_approx` — rely on Mathlib's
-- `Real.exists_rat_eq_convergent`, which applies to any real `ξ` (rational
-- or irrational). Irrationality of `logb 2 3` (proved in Phase60) is a
-- downstream requirement for Phase63 integration, where both Phase60 and
-- Phase61 are composed into `DerivedLargeKBoundTheorem`.

/-!
# Phase 61 — Continued-Fraction Convergents of log₂ 3

## Context

This file provides the structural framework for the continued-fraction
convergents of `Real.logb 2 3`, to be used in the Legendre-based proof
of `DerivedLargeKBoundTheorem` (Phase63, planned). It is a foundational
bridge file: no numerical values of the denominators `q_n` (665, 15601,
31867, ...) are computed here — those verifications are reserved for
Phase63 via `reflection_cert` / `native_decide`.

## What this file provides

1. **Wrapper definition** — `log23_convergent n := Real.convergent (Real.logb 2 3) n`.
2. **Positivity of log₂ 3** — re-stated as a standalone lemma for downstream use
   (Phase60 proves irrationality but does not export positivity explicitly).
3. **Denominator bridge (H2)** — `q_n n := (log23_convergent n).den` with
   basic positivity and definitional unfolding lemmas.
4. **Abstract window frame** — `InWindow n k` predicate capturing
   `q_n ≤ k < q_{n+1}`, with the usual conjunction projections.
5. **Contrapositive of Legendre's approximation theorem** — from Mathlib's
   `Real.exists_rat_eq_convergent`, we derive: if `q` is not a convergent of
   `logb 2 3`, then `|logb 2 3 - q| ≥ 1/(2·q.den²)`. Note: this is NOT the
   classical "best approximation of the second kind" property of CF theory
   (which states `|q·ξ - p| ≥ |q_n·ξ - p_n|` for `q < q_{n+1}`); it is
   only the logical contrapositive of Mathlib's approximation theorem.

## Voie B architecture link

Phase60 proved `Irrational (Real.logb 2 3)` via p-adic valuation. Phase61
builds the CF convergent infrastructure that Phase63 will combine with the
Baker-style upper bound to replace `DerivedLargeKBound` (Phase59 structure)
with a fully proved theorem.

## Mathlib dependencies (v4.27.0)

- `Real.convergent : ℝ → ℕ → ℚ` — noncomputable, recursive via `⌊·⌋` / `fract`.
- `Real.exists_rat_eq_convergent` — Legendre's theorem (positive direction).
- `Real.logb_pos` — for positivity of `log₂ 3`.

## Invariants (M3.2)

- Zero `axiom` declaration (kernel three suffice via Mathlib).
- Zero `sorry`.
- No `native_decide` (reserved for Phase63 `cf_gap_*`).
- No modification of `expected_axioms.md` (M3.2 stays outside central chain
  until Phase63 integration).
- All docstrings in English.
-/

namespace ProjetCollatz.Phase61

open Real

/-! ## Section 1 — Wrapper + basic positivity -/

/-- The `n`-th continued-fraction convergent of `Real.logb 2 3` as a
rational number. This is a thin wrapper around `Real.convergent`. -/
noncomputable def log23_convergent (n : ℕ) : ℚ :=
  convergent (logb 2 3) n

/-- Positivity of `Real.logb 2 3`. Re-stated as a standalone lemma for use
in downstream Phase62/63 arguments (Phase60 proves irrationality but does
not export this). -/
theorem logb23_pos : 0 < logb 2 3 :=
  logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 3)

/-! ## Section 2 — Abstract window frame

At this stage we do not prove that the windows partition ℕ (that requires
monotonicity of `q_n`, which is a Phase62 target). We only define the
predicate and basic projections. -/

/-- Denominator of the `n`-th convergent of `log₂ 3`. In the literature
this is the sequence `q_n` used in the continued-fraction expansion of
`log₂ 3` (OEIS A028507). Numerical values are proved in Phase63. -/
noncomputable def q_n (n : ℕ) : ℕ :=
  (log23_convergent n).den

/-- A natural number `k` lies in window `n` if `q_n ≤ k < q_(n+1)`.
This predicate is used downstream (Phase62) to define best-approximation
windows for the Collatz cycle argument. -/
def InWindow (n k : ℕ) : Prop :=
  q_n n ≤ k ∧ k < q_n (n + 1)

/-- Lower bound projection from `InWindow`. -/
theorem InWindow.lower {n k : ℕ} (h : InWindow n k) : q_n n ≤ k :=
  h.1

/-- Upper bound projection from `InWindow`. -/
theorem InWindow.upper {n k : ℕ} (h : InWindow n k) : k < q_n (n + 1) :=
  h.2

/-- Constructor for `InWindow`. -/
theorem InWindow.mk {n k : ℕ} (h_lo : q_n n ≤ k) (h_hi : k < q_n (n + 1)) :
    InWindow n k :=
  ⟨h_lo, h_hi⟩

/-! ## Section 3 — H2 bridge: denominators -/

/-- The denominator `q_n` is always strictly positive (as denominator of a
rational number). This is the minimal structural property needed downstream. -/
theorem q_n_pos (n : ℕ) : 0 < q_n n := by
  unfold q_n
  exact (log23_convergent n).pos

/-- Definitional unfolding: `q_n n` equals the denominator of the Mathlib
convergent of `log₂ 3`. Exposed as a rewrite handle for downstream proofs. -/
theorem q_n_eq_den (n : ℕ) :
    q_n n = (convergent (logb 2 3) n).den :=
  rfl

/-- The denominator as a real number is strictly positive (common downstream
need for division by `(q_n : ℝ) ^ 2`). -/
theorem q_n_real_pos (n : ℕ) : (0 : ℝ) < (q_n n : ℝ) := by
  exact_mod_cast q_n_pos n

/-! ## Section 4 — H3 contrapositive of Legendre's approximation theorem

The positive direction of Legendre's theorem (1798) is provided by Mathlib
as `Real.exists_rat_eq_convergent`: if `|ξ - q| < 1/(2·q.den²)`, then `q` is
a convergent of `ξ`. The logical contrapositive (non-convergent rationals
are bounded away from `ξ` by the same threshold) is derived below for
Phase62/63 best-approximation arguments.

Terminology caveat: this contrapositive is NOT the classical "best
approximation of the second kind" property of CF theory (which states
`|q·ξ - p| ≥ |q_n·ξ - p_n|` for all `q < q_{n+1}`, cf. Khinchin or
Hardy-Wright). The theorem below is merely the contrapositive of
Mathlib's approximation bound and makes no claim about comparison of
`|q·ξ - p|` across different denominators. -/

/-- Contrapositive of Legendre's approximation theorem applied to `log₂ 3`:
if `q : ℚ` is not equal to any convergent `(log₂ 3).convergent n`, then
`|log₂ 3 - q| ≥ 1 / (2 · q.den²)`.

Proof: contrapositive of `Real.exists_rat_eq_convergent`. If the lower
bound failed (`|ξ - q| < 1/(2·q.den²)`), then Mathlib would yield some
index `n` with `q = ξ.convergent n`, contradicting the hypothesis.

Terminology note: this is the *logical contrapositive* of Legendre's
approximation bound, not the CF-theoretic "best approximation of the
second kind" (which concerns comparison of `|q·ξ - p|` across
denominators and is not used here). -/
theorem not_convergent_implies_far_approx
    {q : ℚ} (h_not_conv : ∀ n, q ≠ (logb 2 3).convergent n) :
    1 / (2 * (q.den : ℝ) ^ 2) ≤ |logb 2 3 - (q : ℝ)| := by
  by_contra h_close
  push_neg at h_close
  obtain ⟨n, hn⟩ := exists_rat_eq_convergent h_close
  exact h_not_conv n hn

end ProjetCollatz.Phase61
