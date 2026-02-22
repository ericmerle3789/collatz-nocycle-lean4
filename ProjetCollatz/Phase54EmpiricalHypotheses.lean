import ProjetCollatz.Phase9FirstReturnMap

/-!
# Phase54EmpiricalHypotheses.lean — Empirical Hypotheses WITHOUT AXIOM

## Purpose

Encode empirical observations (SalmonVisitsAbyss, Barina verification)
as explicit hypotheses in a `structure`, rather than as `axiom` declarations.

## Design Philosophy

Same pattern as Phase51ExternalHypotheses: downstream theorems are
conditional on being given an instance of `EmpiricalHypotheses`.
This makes the dependency on unproved empirical observations EXPLICIT
in every theorem signature.

## Fields

| Field | Source | Status |
|-------|--------|--------|
| `salmon_visits_abyss` | Empirical (verified n ∈ [2, 100000]) | Unproved |
| `barina_verified` | Barina 2025 (published, J. Supercomputing 81) | Published |

Note: `evt_bounded_tail` and `geometric_k_distribution` from the old
`EmpiricalAxioms.lean` were NEVER used in any proof, so they are not
included here.

## Date: 2026-02-21 (Phase 54)

**Note**: `SalmonVisitsAbyss` is NOT used in the Porte 2 (anti-cycle) proof.
This file is included as transitive infrastructure via Phase9ErgodicDescent.
Only `barina_verified` is relevant to the anti-cycle theorem chain.
-/

namespace ProjetCollatz

/-- Empirical hypotheses bundled as explicit structure.
    **No `axiom` keyword is used.** All downstream theorems are conditional
    on being given an instance of this structure.

    These are observations that have been verified empirically or published
    but not proved in Lean. Making them explicit ensures that no theorem
    silently depends on unproved claims. -/
structure EmpiricalHypotheses where
  /-- **SalmonVisitsAbyss — Weak Salmon Hypothesis**

  Every trajectory from n > 1 eventually visits a number ≡ 5 mod 8
  (class 5) with value > 0.

  Empirically verified for all n ∈ [2, 100000].
  Implied by Collatz: if nSeq n k = 1, then the predecessor of 1
  under Syracuse satisfies m ≡ 5 mod 8 for most values. -/
  salmon_visits_abyss : ∀ n : ℕ, n > 1 →
    ∃ t : ℕ, nSeq n t % 8 = 5 ∧ 0 < nSeq n t

  /-- **Barina Verification Bound**

  The Collatz conjecture has been verified computationally up to 2^71
  by David Barina (J. Supercomputing 81, 2025). Every n in [1, 2^71)
  eventually reaches 1.

  STATUS: Published, peer-reviewed computation. -/
  barina_verified : ∀ n : ℕ, n > 0 → n < 2^71 →
    ∃ k : ℕ, nSeq n k = 1

end ProjetCollatz
