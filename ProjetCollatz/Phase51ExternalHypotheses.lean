import ProjetCollatz.Phase50CycleEquation

/-!
# Phase51ExternalHypotheses.lean — External Hypotheses WITHOUT AXIOM

## Purpose

Encode published mathematical results (Baker, Hercher, Barina) as explicit
hypotheses in a `structure`, rather than as `axiom` declarations that pollute
the global Lean environment.

## Design Philosophy

The Phase 50 approach used `axiom` — this silently makes every downstream
theorem depend on unproved assumptions without them appearing in the type.

The Phase 51 approach uses `structure` — the dependency is explicit:
  `theorem no_nontrivial_cycle_conditional (ext : ExternalCycleHypotheses) ...`

Anyone reading the theorem signature immediately sees what is assumed.
This is standard practice in formal mathematics: "Under hypotheses H₁, H₂, H₃, we prove P."

## Published Sources

| # | Field | Source | Published |
|---|-------|--------|-----------|
| B1 | `baker_separation` | Baker 1966 + Rhin 1987 | Mathematika / Fields Medal |
| B2 | `hercher_no_small_cycle` | Hercher 2023 | JIS Vol. 26 (arXiv:2201.00406) |
| B3 | `barina_convergence` | Barina 2021 | J. Supercomputing |

## Date: 2026-02-20 (Phase 51)
-/

namespace ProjetCollatz

/-!
## The Hypothesis Structure

Three published, peer-reviewed results bundled as explicit hypotheses.
Note: B4 (`cycle_min_bounded`) is NOT included — it will be PROVED as a
theorem from B1 + B2 + the cycle equation in Phase51CycleBound.lean.
-/

/-- External published hypotheses for cycle elimination, bundled as a structure.
    **No `axiom` keyword is used.** All downstream theorems are conditional
    on being given an instance of this structure. -/
structure ExternalCycleHypotheses where
  /-- **B1: Baker's Theorem on Linear Forms in Logarithms**

  Source: A. Baker, "Linear forms in the logarithms of algebraic numbers"
  (Mathematika, 1966). Fields Medal 1970.
  Effective bound sharpened by G. Rhin (1987): μ(log₂3) ≤ 5.125.

  Formulation: If 2^s > 3^k with s ≥ 1, k ≥ 2, then the gap is at least 3^k/k^6.
  We use μ = 6 (weaker than Rhin's 5.125 but sufficient for k ≥ 92).
  Note: k ≥ 2 (not k ≥ 1) because (2^2 - 3^1)·1^6 = 1 < 3 = 3^1 is a
  counterexample at k=1. For cycles, k ≥ 2 is guaranteed by cycle_k_ge_two. -/
  baker_separation : ∀ (s k : ℕ), s ≥ 1 → k ≥ 2 → 2^s > 3^k →
    (2^s - 3^k) * k^6 ≥ 3^k

  /-- **B2: Lower bound on cycle odd steps.**

  Originally encoded Hercher (2023): k ≥ 92. Weakened to k ≥ 1
  (trivially from IsOddCycle) because this field is NEVER accessed
  by the Product Bound chain (cycle_min_bound_small_k only uses
  baker_separation). The full Hercher result (k ≥ 92) is PROVED
  as a theorem in Phase 58 from Baker + Barina alone.

  Source: C. Hercher, "There are no Collatz m-cycles with m ≤ 91"
  (Journal of Integer Sequences, 2023). arXiv:2201.00406. -/
  hercher_no_small_cycle : ∀ (n k : ℕ), IsOddCycle n k → k ≥ 1

  /-- **B3: Barina Computational Verification**

  Source: D. Barina, "Improved verification limit for the convergence
  of the Collatz conjecture" (J. Supercomputing 81, 810, 2025).
  DOI: 10.1007/s11227-025-07337-0. Verified up to 2^71.

  Conservative bound: every positive integer up to 2^71 reaches 1. -/
  barina_convergence : ∀ (n : ℕ), n > 0 → n < 2^71 → reaches_one n

/-!
## Comparison with Phase 50

| Aspect | Phase 50 | Phase 51 |
|--------|----------|----------|
| Mechanism | `axiom` keyword | `structure` fields |
| Visibility | Hidden in environment | Explicit in theorem types |
| B4 | Axiomatized | Derived as theorem |
| Count | 4 axioms | 0 axioms |
| Dependency | Implicit | Explicit parameter |
-/

end ProjetCollatz
